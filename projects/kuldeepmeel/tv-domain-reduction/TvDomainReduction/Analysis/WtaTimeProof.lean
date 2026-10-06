import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Run
import TvDomainReduction.Meta.ModelClosure
import TvDomainReduction.Analysis.CorrectnessProof
import TvDomainReduction.Analysis.SpaceProof
import TvDomainReduction.Analysis.TimeProof
import TvDomainReduction.Analysis.MixtureCorrectnessProof
import TvDomainReduction.Analysis.MixtureTimeProof
import TvDomainReduction.Analysis.WtaJointBound
import TvDomainReduction.Analysis.WtaMassDPTime
import TvDomainReduction.Interface.Encoding
import TvDomainReduction.Interface.Pseudocode
import TvDomainReduction.Interface.ProgramModel

set_option autoImplicit false

open TvDomainReduction
open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Model.Operations
open TvDomainReduction.Interface
open TvDomainReduction.Analysis

set_option maxHeartbeats 4000000 in
/-- Proof-side owner for `TvDomainReduction.wta_fpras_time`; its statement is fixed by the proof charter.

PAPER: main.tex:996-1003, main.tex:1005-1034 (running-time half of `thm:wta_fpras`).

The paper's proof reduces this claim to `thm:pc_fpras` by padding to a common
feature dimension `d` and expanding every bilinear gate into a scalar
product/sum layer (main.tex:1005-1030).  This development does not build that
expanded circuit: `Run.runLawWTA` runs the *unexpanded* `Circuit.node` (already
the bilinear gate) through the very same `Program.build`/`Program.massDP`
machinery `Analysis.TimeProof`/`Analysis.SpaceProof` already cost for
`thm:pc_fpras`, so the proof below is a direct structural accounting against
`Program.runWTA`, not an instantiation of `pc_fpras_time_proof` (whose law is
`Program.run`, not `Program.runWTA` — the WTA run additionally pays for the
normalisation DP and a dense two-vector root query, main.tex:967, 992).

Two repairs from the paper's own formula are recorded in `Model/Theorem.lean`
and reused here verbatim: the first term is `|V|·d³·(…)²`, not the paper's
`|V|·d²·(…)²` (`Program.build`'s fused node charges the post-sum features on
every candidate row, not just the `M` survivors — a model gap, not a proof
convenience), and `hL : 0 < CircuitPair.steps C` is carried explicitly (the
paper's own `I ≥ 1` restriction, main.tex:1034). -/
theorem TvDomainReduction.Analysis.wta_fpras_time_proof (hprior : Prior) (fam : SparsifyFamily) : ∃ c : ℕ, ∀ {V : Vtree} (C : CircuitPair V 1 1) (ε η : ℝ), 0 < ε → ε < 1 → 0 < η → η < 1 → 0 < CircuitPair.steps C → ∀ prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C)) (perStepFail η (CircuitPair.steps C)), fam.Member prior → ∀ p ∈ (Run.runLawWTA C prior).support, (Charged.steps rate p : ℝ) ≤ (c : ℝ) * (1 + (prior.polylog (pairJointDim C * (leafDomMax V + pairRetainedBudget C prior) ^ 2) : ℝ)) * ((vtreeNodes V : ℝ) * (pairJointDim C : ℝ) ^ 3 * ((leafDomMax V : ℝ) + (pairJointDim C : ℝ) + (pairJointDim C : ℝ) ^ 2 * (vtreeNodes V : ℝ) ^ 2 / ε ^ 2 * Real.log ((vtreeNodes V : ℝ) / η)) ^ 2 + (vtreeNodes V : ℝ) * (pairJointDim C : ℝ) ^ (2 * prior.mmExp)) := by
  set K1 : ℕ := 1 + 72 * fam.sizeConst with hK1def
  refine ⟨9 + 7 * K1 ^ 2 + 10 * K1 + 2 * fam.costConst * K1 ^ 2, ?_⟩
  intro V C ε η hε0 hε1 hη0 hη1 hL prior hmem p hp
  rw [Run.runLawWTA, PMF.mem_support_map_iff] at hp
  obtain ⟨t, -, rfl⟩ := hp
  -- notation
  set d : ℕ := pairJointDim C with hddef
  set q : ℕ := leafDomMax V with hqdef
  set Vn : ℕ := vtreeNodes V with hVndef
  set M : ℕ := pairRetainedBudget C prior with hMdef
  set B : ℕ := q + M with hBdef
  set W : ℕ := pairWidth C with hWdef
  -- basic facts
  have hd2 : 2 ≤ d := pairJointDim_ge_two C
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
  have hVn1 : 1 ≤ Vn := vtreeNodes_pos V
  have hVn1' : (1:ℝ) ≤ (Vn:ℝ) := by exact_mod_cast hVn1
  have hLnVn : CircuitPair.steps C ≤ Vn := circuitPair_steps_le_vtreeNodes C.P C.Q
  have hLnVn' : (CircuitPair.steps C:ℝ) ≤ (Vn:ℝ) := by exact_mod_cast hLnVn
  have hWd : W ≤ d := pairWidth_le_pairJointDim C
  have hWd' : (W:ℝ) ≤ (d:ℝ) := by exact_mod_cast hWd
  have hL1 : (1:ℝ) ≤ (CircuitPair.steps C:ℝ) := by exact_mod_cast hL
  -- the retained-row budget, via the space claim
  have hMspace := (pc_fpras_space_proof hprior C ε η hε0 hε1 hη0 hη1 hL prior).2
  rw [← hMdef, ← hWdef] at hMspace
  have hlogW0 : (0:ℝ) ≤ Real.log (4 * (W:ℝ)) := by
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · simp [h0]
    · have hW1 : (1:ℝ) ≤ (W:ℝ) := by exact_mod_cast h0
      exact Real.log_nonneg (by linarith)
  have hlog4d : Real.log (4 * (d:ℝ)) ≤ 4 * (d:ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 * (d:ℝ) by linarith); linarith
  have hlog4d0 : (0:ℝ) ≤ Real.log (4 * (d:ℝ)) := Real.log_nonneg (by linarith)
  have hlog4Wd : Real.log (4 * (W:ℝ)) ≤ Real.log (4 * (d:ℝ)) := by
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · simp only [h0, Nat.cast_zero, mul_zero, Real.log_zero]
      linarith
    · have hW1 : (1:ℝ) ≤ (W:ℝ) := by exact_mod_cast h0
      apply Real.log_le_log (by linarith); linarith
  have hlog4W' : Real.log (4 * (W:ℝ)) ≤ 4 * (d:ℝ) := hlog4Wd.trans hlog4d
  have hlogLV : Real.log ((CircuitPair.steps C:ℝ) / η) ≤ Real.log ((Vn:ℝ) / η) := by
    apply Real.log_le_log (by positivity)
    gcongr
  have hlogVη0 : (0:ℝ) ≤ Real.log ((Vn:ℝ) / η) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hη0]; linarith
  -- the retained-row budget, in the paper's own shape
  have hMbound : (M:ℝ) ≤ 72 * (fam.sizeConst:ℝ) * (d:ℝ) ^ 2 * (Vn:ℝ) ^ 2
      * Real.log ((Vn:ℝ) / η) / ε ^ 2 := by
    have hsizeConst_le : (prior.sizeConst:ℝ) ≤ fam.sizeConst := by exact_mod_cast hmem.sizeConst_le
    have hsteps2 : (CircuitPair.steps C:ℝ) ^ 2 ≤ (Vn:ℝ) ^ 2 := by
      apply sq_le_sq' <;> linarith
    have hlogstepsC0 : (0:ℝ) ≤ Real.log ((CircuitPair.steps C:ℝ) / η) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hη0]; nlinarith
    have hstep : (prior.sizeConst:ℝ) * 18 * (W:ℝ) * (CircuitPair.steps C:ℝ) ^ 2
        * Real.log (4 * (W:ℝ)) * Real.log ((CircuitPair.steps C:ℝ) / η) / ε ^ 2
        ≤ (fam.sizeConst:ℝ) * 18 * (d:ℝ) * (Vn:ℝ) ^ 2
            * (4 * (d:ℝ)) * Real.log ((Vn:ℝ) / η) / ε ^ 2 := by
      gcongr
    calc (M:ℝ) ≤ _ := hMspace
      _ ≤ _ := hstep
      _ = 72 * (fam.sizeConst:ℝ) * (d:ℝ) ^ 2 * (Vn:ℝ) ^ 2 * Real.log ((Vn:ℝ) / η) / ε ^ 2 := by
          ring
  -- the bracket the headline bound is stated against, and `B ≤ K1 · bracket`
  set bracket : ℝ := (q:ℝ) + d + (d:ℝ) ^ 2 * (Vn:ℝ) ^ 2 / ε ^ 2 * Real.log ((Vn:ℝ) / η)
    with hbracketdef
  have hqbr : (q:ℝ) ≤ bracket := by
    rw [hbracketdef]
    have : (0:ℝ) ≤ (d:ℝ) ^ 2 * (Vn:ℝ) ^ 2 / ε ^ 2 * Real.log ((Vn:ℝ) / η) := by positivity
    linarith
  have hdbr : (d:ℝ) ≤ bracket := by
    rw [hbracketdef]
    have h1 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ (d:ℝ) ^ 2 * (Vn:ℝ) ^ 2 / ε ^ 2 * Real.log ((Vn:ℝ) / η) := by positivity
    linarith
  have hsq2br : (d:ℝ) ^ 2 * (Vn:ℝ) ^ 2 / ε ^ 2 * Real.log ((Vn:ℝ) / η) ≤ bracket := by
    rw [hbracketdef]
    have h1 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg _
    linarith
  have hbr1 : (1:ℝ) ≤ bracket := hd1.trans hdbr
  have hbr0 : (0:ℝ) ≤ bracket := by linarith
  clear_value bracket
  have hBreal : (B:ℝ) = (q:ℝ) + M := by rw [hBdef]; push_cast; ring
  have hBbr : (B:ℝ) ≤ (K1:ℝ) * bracket := by
    rw [hBreal, hK1def]
    push_cast
    have h1 : (M:ℝ) ≤ 72 * (fam.sizeConst:ℝ) * bracket := by
      calc (M:ℝ) ≤ 72 * (fam.sizeConst:ℝ) * (d:ℝ) ^ 2 * (Vn:ℝ) ^ 2 * Real.log ((Vn:ℝ) / η) / ε ^ 2 := hMbound
        _ = 72 * (fam.sizeConst:ℝ) * ((d:ℝ) ^ 2 * (Vn:ℝ) ^ 2 / ε ^ 2 * Real.log ((Vn:ℝ) / η)) := by ring
        _ ≤ 72 * (fam.sizeConst:ℝ) * bracket := by
            apply mul_le_mul_of_nonneg_left hsq2br (by positivity)
    linarith [hqbr]
  have hBbr2 : (B:ℝ) ^ 2 ≤ (K1:ℝ) ^ 2 * bracket ^ 2 := by
    have hB0 : (0:ℝ) ≤ (B:ℝ) := Nat.cast_nonneg _
    have hK10 : (0:ℝ) ≤ (K1:ℝ) := Nat.cast_nonneg _
    calc (B:ℝ) ^ 2 ≤ ((K1:ℝ) * bracket) ^ 2 := by
          apply pow_le_pow_left₀ hB0 hBbr
      _ = (K1:ℝ) ^ 2 * bracket ^ 2 := by ring
  -- the structural facts build_steps_le_joint / massDP_steps_le need
  have hBle : leafDomMax V + retainedBudget prior C.P C.Q ≤ B := by
    have e1 : retainedBudget prior C.P C.Q = M := by
      rw [hMdef]; exact (pairRetainedBudget_eq C prior).symm
    rw [← hqdef, e1, hBdef]
  have hdrefl : jointDim C.P C.Q ≤ d := le_of_eq hddef.symm
  have hqrefl : leafDomMax V ≤ q := le_of_eq hqdef
  have hdP : gateWidth C.P ≤ d := (gateWidth_le_jointDim_left C.P C.Q).trans hdrefl
  have hdQ : gateWidth C.Q ≤ d := (gateWidth_le_jointDim_right C.P C.Q).trans hdrefl
  -- the normalisation DP
  have hmP := massDP_steps_le d q C.P (PUnit.unit : PUnit.{2}) hdP hqrefl
  have hmQ := massDP_steps_le d q C.Q (PUnit.unit : PUnit.{2}) hdQ hqrefl
  -- the bottom-up coreset propagation
  have hbuild := build_steps_le_joint prior B d q C.P C.Q t hBle hdrefl hqrefl
  have hrows := build_card_idx_le prior C.P C.Q t
  have hrows' : ((Fintype.card (Program.build prior C.P C.Q t).val.Idx : ℕ) : ℝ) ≤ (B:ℝ) := by
    exact_mod_cast hrows
  -- the dense output stage (Algorithm 1 line 13, reused unchanged)
  have hdense := mixTime_steps_runDense C prior t
  -- Program.runWTA's own tally
  have hstepWTA : Charged.steps rate (Program.runWTA C prior t)
      = Charged.steps rate (Program.massDP C.P (PUnit.unit : PUnit.{2}))
        + Charged.steps rate (Program.massDP C.Q (PUnit.unit : PUnit.{2}))
        + 2 + 1
        + Charged.steps rate (Program.runDense C prior t) := by
    simp only [Program.runWTA, Charged.steps_bind, divs, subs, steps_opMany_rate]
    rw [massDP_steps_eq C.Q (Program.massDP C.P (PUnit.unit : PUnit.{2})).val
      (PUnit.unit : PUnit.{2})]
    ring
  -- combine the nat-level tallies: `rows ≤ B` absorbs the dense output stage
  have hnatcomb : Charged.steps rate (Program.runWTA C prior t)
      ≤ Charged.steps rate (Program.massDP C.P (PUnit.unit : PUnit.{2}))
        + Charged.steps rate (Program.massDP C.Q (PUnit.unit : PUnit.{2}))
        + Charged.steps rate (Program.build prior C.P C.Q t)
        + 6 * B + 4 := by
    rw [hstepWTA, hdense]
    omega
  have hnatcombR : (Charged.steps rate (Program.runWTA C prior t) : ℝ)
      ≤ (Charged.steps rate (Program.massDP C.P (PUnit.unit : PUnit.{2})) : ℝ)
        + (Charged.steps rate (Program.massDP C.Q (PUnit.unit : PUnit.{2})) : ℝ)
        + (Charged.steps rate (Program.build prior C.P C.Q t) : ℝ)
        + 6 * (B:ℝ) + 4 := by
    have := hnatcomb
    exact_mod_cast this
  have hbuildR : (Charged.steps rate (Program.build prior C.P C.Q t) : ℝ)
      ≤ (Vn:ℝ) * ((d:ℝ) * q) + (CircuitPair.steps C : ℝ) * ((B:ℝ) ^ 2 * (1 + 6 * (d:ℝ) ^ 3)
          + prior.costConst * (prior.polylog (d * B ^ 2) : ℝ)
              * ((d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp)) := by
    have hpr : (pairRegion C.P C.Q).steps = CircuitPair.steps C := rfl
    rw [hpr] at hbuild
    exact hbuild
  have hmPQ : (Charged.steps rate (Program.massDP C.P (PUnit.unit : PUnit.{2})) : ℝ)
      + (Charged.steps rate (Program.massDP C.Q (PUnit.unit : PUnit.{2})) : ℝ)
      ≤ 2 * (Vn:ℝ) * (d:ℝ) * q + 6 * (Vn:ℝ) * (d:ℝ) ^ 3 := by
    have e1 : (Vn:ℝ) * ((d:ℝ) * q + 3 * (d:ℝ) ^ 3) = (Vn:ℝ) * (d:ℝ) * q + 3 * (Vn:ℝ) * (d:ℝ) ^ 3 := by
      ring
    rw [e1] at hmP hmQ
    linarith
  have hcombined : (Charged.steps rate (Program.runWTA C prior t) : ℝ)
      ≤ 3 * (Vn:ℝ) * (d:ℝ) * q + 6 * (Vn:ℝ) * (d:ℝ) ^ 3
        + (CircuitPair.steps C : ℝ) * ((B:ℝ) ^ 2 * (1 + 6 * (d:ℝ) ^ 3)
            + prior.costConst * (prior.polylog (d * B ^ 2) : ℝ)
                * ((d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp))
        + 6 * (B:ℝ) + 4 := by
    linarith [hnatcombR, hbuildR, hmPQ]
  -- the common majorant `MT := Vn · d³ · bracket²` and prefactor `P := 1 + polylog(d·B²)`
  set MT : ℝ := (Vn:ℝ) * (d:ℝ) ^ 3 * bracket ^ 2 with hMTdef
  set P : ℝ := 1 + (prior.polylog (d * B ^ 2) : ℝ) with hPdef
  have hP1 : (1:ℝ) ≤ P := by
    rw [hPdef]; have := Nat.cast_nonneg (α := ℝ) (prior.polylog (d * B ^ 2)); linarith
  have hMT0 : (0:ℝ) ≤ MT := by rw [hMTdef]; positivity
  have hMT_le_PMT : MT ≤ P * MT := le_mul_of_one_le_left hMT0 hP1
  clear_value MT P
  clear_value W B M Vn q d
  -- term A: the leaf reads
  have hd3 : (d:ℝ) ≤ (d:ℝ) ^ 3 := le_self_pow₀ hd1 (by norm_num)
  have hbr2 : bracket ≤ bracket ^ 2 := le_self_pow₀ hbr1 (by norm_num)
  have hqbr2 : (q:ℝ) ≤ bracket ^ 2 := hqbr.trans hbr2
  have hTA : 3 * (Vn:ℝ) * (d:ℝ) * q ≤ 3 * MT := by
    rw [hMTdef]
    have hdq : (d:ℝ) * q ≤ (d:ℝ) ^ 3 * bracket ^ 2 :=
      mul_le_mul hd3 hqbr2 (Nat.cast_nonneg _) (by positivity)
    have h3Vn0 : (0:ℝ) ≤ 3 * (Vn:ℝ) := by positivity
    calc 3 * (Vn:ℝ) * (d:ℝ) * q = 3 * (Vn:ℝ) * ((d:ℝ) * q) := by ring
      _ ≤ 3 * (Vn:ℝ) * ((d:ℝ) ^ 3 * bracket ^ 2) := mul_le_mul_of_nonneg_left hdq h3Vn0
      _ = 3 * ((Vn:ℝ) * (d:ℝ) ^ 3 * bracket ^ 2) := by ring
  -- term B: the normalisation DP's own tensor cost
  have hTB : 6 * (Vn:ℝ) * (d:ℝ) ^ 3 ≤ 6 * MT := by
    rw [hMTdef]
    have h6d0 : (0:ℝ) ≤ 6 * (Vn:ℝ) * (d:ℝ) ^ 3 := by positivity
    calc 6 * (Vn:ℝ) * (d:ℝ) ^ 3 = 6 * ((Vn:ℝ) * (d:ℝ) ^ 3) * 1 := by ring
      _ ≤ 6 * ((Vn:ℝ) * (d:ℝ) ^ 3) * bracket ^ 2 :=
          mul_le_mul_of_nonneg_left (hbr1.trans hbr2) (by positivity)
      _ = 6 * ((Vn:ℝ) * (d:ℝ) ^ 3 * bracket ^ 2) := by ring
  have hK11 : (1:ℝ) ≤ (K1:ℝ) := by
    rw [hK1def]
    have h0 : (0:ℝ) ≤ 72 * (fam.sizeConst:ℝ) := by positivity
    push_cast; linarith
  have hd31 : (1:ℝ) ≤ (d:ℝ) ^ 3 := hd1.trans hd3
  -- term C: the inherited-weight / fused-feature traversal, per product region
  have hTC : (CircuitPair.steps C : ℝ) * ((B:ℝ) ^ 2 * (1 + 6 * (d:ℝ) ^ 3))
      ≤ 7 * (K1:ℝ) ^ 2 * MT := by
    rw [hMTdef]
    have h1 : (1:ℝ) + 6 * (d:ℝ) ^ 3 ≤ 7 * (d:ℝ) ^ 3 := by linarith [hd31]
    have h2 : (B:ℝ) ^ 2 * (1 + 6 * (d:ℝ) ^ 3) ≤ (K1:ℝ) ^ 2 * bracket ^ 2 * (7 * (d:ℝ) ^ 3) := by
      have hK10 : (0:ℝ) ≤ (K1:ℝ) ^ 2 * bracket ^ 2 := by positivity
      calc (B:ℝ) ^ 2 * (1 + 6 * (d:ℝ) ^ 3) ≤ ((K1:ℝ) ^ 2 * bracket ^ 2) * (7 * (d:ℝ) ^ 3) := by
            apply mul_le_mul hBbr2 h1 (by positivity) hK10
        _ = (K1:ℝ) ^ 2 * bracket ^ 2 * (7 * (d:ℝ) ^ 3) := by ring
    calc (CircuitPair.steps C : ℝ) * ((B:ℝ) ^ 2 * (1 + 6 * (d:ℝ) ^ 3))
        ≤ (Vn:ℝ) * ((K1:ℝ) ^ 2 * bracket ^ 2 * (7 * (d:ℝ) ^ 3)) :=
          mul_le_mul hLnVn' h2 (by positivity) (Nat.cast_nonneg _)
      _ = 7 * (K1:ℝ) ^ 2 * ((Vn:ℝ) * (d:ℝ) ^ 3 * bracket ^ 2) := by ring
  -- term D: the solver calls, one per product region
  have hTD : (CircuitPair.steps C : ℝ)
      * (prior.costConst * (prior.polylog (d * B ^ 2) : ℝ) * ((d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp))
      ≤ 2 * (fam.costConst : ℝ) * (K1:ℝ) ^ 2 * (P * MT) := by
    have hcc : (prior.costConst : ℝ) ≤ fam.costConst := by exact_mod_cast hmem.costConst_le
    have hplP : (prior.polylog (d * B ^ 2) : ℝ) ≤ P := by rw [hPdef]; linarith
    have hdB2 : (d:ℝ) * (B:ℝ) ^ 2 ≤ (d:ℝ) ^ 3 * ((K1:ℝ) ^ 2 * bracket ^ 2) :=
      mul_le_mul hd3 hBbr2 (by positivity) (by positivity)
    have hmmle : prior.mmExp ≤ (3:ℝ) := by linarith [prior.mmExp_le.2]
    have hdmm : (d:ℝ) ^ prior.mmExp ≤ (d:ℝ) ^ (3:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hd1 hmmle
    have hd3eq : (d:ℝ) ^ (3:ℝ) = (d:ℝ) ^ 3 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have hdmm' : (d:ℝ) ^ prior.mmExp ≤ (d:ℝ) ^ 3 := by rw [hd3eq] at hdmm; exact hdmm
    have hdmm'' : (d:ℝ) ^ prior.mmExp ≤ (d:ℝ) ^ 3 * ((K1:ℝ) ^ 2 * bracket ^ 2) := by
      have hK1sq1 : (1:ℝ) ≤ (K1:ℝ) ^ 2 := hK11.trans (le_self_pow₀ hK11 (by norm_num))
      have hbr2_1 : (1:ℝ) ≤ bracket ^ 2 := hbr1.trans hbr2
      have h1 : (1:ℝ) ≤ (K1:ℝ) ^ 2 * bracket ^ 2 := one_le_mul_of_one_le_of_one_le hK1sq1 hbr2_1
      have hd30 : (0:ℝ) ≤ (d:ℝ) ^ 3 := by positivity
      calc (d:ℝ) ^ prior.mmExp ≤ (d:ℝ) ^ 3 := hdmm'
        _ = (d:ℝ) ^ 3 * 1 := by ring
        _ ≤ (d:ℝ) ^ 3 * ((K1:ℝ) ^ 2 * bracket ^ 2) := mul_le_mul_of_nonneg_left h1 hd30
    have hsum : (d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp
        ≤ 2 * ((d:ℝ) ^ 3 * ((K1:ℝ) ^ 2 * bracket ^ 2)) := by linarith
    have hnn : (0:ℝ) ≤ (d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp :=
      add_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
    have hstep1 : prior.costConst * (prior.polylog (d * B ^ 2) : ℝ)
          * ((d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp)
        ≤ (fam.costConst:ℝ) * P * (2 * ((d:ℝ) ^ 3 * ((K1:ℝ) ^ 2 * bracket ^ 2))) := by
      have ha : (0:ℝ) ≤ prior.costConst * (prior.polylog (d * B ^ 2) : ℝ) := by positivity
      calc prior.costConst * (prior.polylog (d * B ^ 2) : ℝ)
            * ((d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp)
          ≤ (fam.costConst:ℝ) * P * ((d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp) := by
            apply mul_le_mul_of_nonneg_right _ hnn
            exact mul_le_mul hcc hplP (by positivity) (by positivity)
        _ ≤ (fam.costConst:ℝ) * P * (2 * ((d:ℝ) ^ 3 * ((K1:ℝ) ^ 2 * bracket ^ 2))) := by
            apply mul_le_mul_of_nonneg_left hsum (by positivity)
    calc (CircuitPair.steps C : ℝ)
          * (prior.costConst * (prior.polylog (d * B ^ 2) : ℝ)
              * ((d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp))
        ≤ (Vn:ℝ) * ((fam.costConst:ℝ) * P * (2 * ((d:ℝ) ^ 3 * ((K1:ℝ) ^ 2 * bracket ^ 2)))) := by
          apply mul_le_mul hLnVn' hstep1 (by positivity) (Nat.cast_nonneg _)
      _ = 2 * (fam.costConst : ℝ) * (K1:ℝ) ^ 2 * (P * MT) := by
          rw [hMTdef]; ring
  -- term E: the dense output stage and the two DP-adjacent scalar charges
  have hTE : 6 * (B:ℝ) + 4 ≤ 10 * (K1:ℝ) * MT := by
    rw [hMTdef]
    have h6B : 6 * (B:ℝ) ≤ 6 * (K1:ℝ) * bracket := by
      calc 6 * (B:ℝ) ≤ 6 * ((K1:ℝ) * bracket) := mul_le_mul_of_nonneg_left hBbr (by norm_num)
        _ = 6 * (K1:ℝ) * bracket := by ring
    have h4Kbr : 4 * (K1:ℝ) ≤ 4 * (K1:ℝ) * bracket := by
      calc 4 * (K1:ℝ) = 4 * (K1:ℝ) * 1 := by ring
        _ ≤ 4 * (K1:ℝ) * bracket := mul_le_mul_of_nonneg_left hbr1 (by positivity)
    have h6B' : 6 * (K1:ℝ) * bracket + 4 * (K1:ℝ) ≤ 10 * (K1:ℝ) * bracket := by linarith [h4Kbr]
    have hVnd31 : (1:ℝ) ≤ (Vn:ℝ) * (d:ℝ) ^ 3 := one_le_mul_of_one_le_of_one_le hVn1' hd31
    have hbrle : bracket ≤ (Vn:ℝ) * (d:ℝ) ^ 3 * bracket ^ 2 := by
      calc bracket ≤ bracket ^ 2 := hbr2
        _ = 1 * bracket ^ 2 := by ring
        _ ≤ (Vn:ℝ) * (d:ℝ) ^ 3 * bracket ^ 2 := mul_le_mul_of_nonneg_right hVnd31 (by positivity)
    have hfinal : 10 * (K1:ℝ) * bracket ≤ 10 * (K1:ℝ) * ((Vn:ℝ) * (d:ℝ) ^ 3 * bracket ^ 2) :=
      mul_le_mul_of_nonneg_left hbrle (by positivity)
    have h4 : (4:ℝ) ≤ 4 * (K1:ℝ) := by linarith [hK11]
    linarith
  -- assemble
  have hsplit : (CircuitPair.steps C : ℝ) * ((B:ℝ) ^ 2 * (1 + 6 * (d:ℝ) ^ 3)
        + prior.costConst * (prior.polylog (d * B ^ 2) : ℝ)
            * ((d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp))
      = (CircuitPair.steps C : ℝ) * ((B:ℝ) ^ 2 * (1 + 6 * (d:ℝ) ^ 3))
        + (CircuitPair.steps C : ℝ) * (prior.costConst * (prior.polylog (d * B ^ 2) : ℝ)
            * ((d:ℝ) * (B:ℝ) ^ 2 + (d:ℝ) ^ prior.mmExp)) := by ring
  rw [hsplit] at hcombined
  have hfinalbound : (Charged.steps rate (Program.runWTA C prior t) : ℝ)
      ≤ (9 + 7 * (K1:ℝ) ^ 2 + 10 * (K1:ℝ) + 2 * (fam.costConst:ℝ) * (K1:ℝ) ^ 2) * (P * MT) := by
    have e1 : (9 + 7 * (K1:ℝ) ^ 2 + 10 * (K1:ℝ) + 2 * (fam.costConst:ℝ) * (K1:ℝ) ^ 2) * (P * MT)
        = 3 * (P * MT) + 6 * (P * MT) + 7 * (K1:ℝ) ^ 2 * (P * MT) + 10 * (K1:ℝ) * (P * MT)
          + 2 * (fam.costConst:ℝ) * (K1:ℝ) ^ 2 * (P * MT) := by ring
    rw [e1]
    have h3PMT : 3 * MT ≤ 3 * (P * MT) := mul_le_mul_of_nonneg_left hMT_le_PMT (by norm_num)
    have h6PMT : 6 * MT ≤ 6 * (P * MT) := mul_le_mul_of_nonneg_left hMT_le_PMT (by norm_num)
    have h7PMT : 7 * (K1:ℝ) ^ 2 * MT ≤ 7 * (K1:ℝ) ^ 2 * (P * MT) :=
      mul_le_mul_of_nonneg_left hMT_le_PMT (by positivity)
    have h10PMT : 10 * (K1:ℝ) * MT ≤ 10 * (K1:ℝ) * (P * MT) :=
      mul_le_mul_of_nonneg_left hMT_le_PMT (by positivity)
    have hA' : 3 * (Vn:ℝ) * (d:ℝ) * q ≤ 3 * (P * MT) := by linarith [hTA, h3PMT]
    have hB' : 6 * (Vn:ℝ) * (d:ℝ) ^ 3 ≤ 6 * (P * MT) := by linarith [hTB, h6PMT]
    have hC' : (CircuitPair.steps C : ℝ) * ((B:ℝ) ^ 2 * (1 + 6 * (d:ℝ) ^ 3))
        ≤ 7 * (K1:ℝ) ^ 2 * (P * MT) := by linarith [hTC, h7PMT]
    have hE' : 6 * (B:ℝ) + 4 ≤ 10 * (K1:ℝ) * (P * MT) := by linarith [hTE, h10PMT]
    linarith [hcombined, hA', hB', hC', hTD, hE']
  have hextra0 : (0:ℝ) ≤ (Vn:ℝ) * (d:ℝ) ^ (2 * prior.mmExp) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcP0 : (0:ℝ) ≤ (9 + 7 * (K1:ℝ) ^ 2 + 10 * (K1:ℝ) + 2 * (fam.costConst:ℝ) * (K1:ℝ) ^ 2) * P := by
    have := hP1; positivity
  calc (Charged.steps rate (Program.runWTA C prior t) : ℝ)
      ≤ (9 + 7 * (K1:ℝ) ^ 2 + 10 * (K1:ℝ) + 2 * (fam.costConst:ℝ) * (K1:ℝ) ^ 2) * (P * MT) :=
        hfinalbound
    _ = (9 + 7 * (K1:ℝ) ^ 2 + 10 * (K1:ℝ) + 2 * (fam.costConst:ℝ) * (K1:ℝ) ^ 2) * P * MT := by ring
    _ ≤ (9 + 7 * (K1:ℝ) ^ 2 + 10 * (K1:ℝ) + 2 * (fam.costConst:ℝ) * (K1:ℝ) ^ 2) * P
        * (MT + (Vn:ℝ) * (d:ℝ) ^ (2 * prior.mmExp)) := by
        apply mul_le_mul_of_nonneg_left _ hcP0
        linarith [hextra0]
    _ = _ := by push_cast; ring

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `wta_fpras_time_proof`, via a fresh jointDim-indexed per-region
  recursion (`Analysis.WtaJointBound`) and a normalisation-DP recursion
  (`Analysis.WtaMassDPTime`), neither of which goes through `pc_fpras_time_proof`
  (whose law is `Program.run`, not `Program.runWTA`).
-/
