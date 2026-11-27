# References

Every paper this repository formalizes or cites, with the short key used in the
Lean docstrings. A citation in the source looks like ``[Hub15, Theorem 5]``: a
key from this file, plus the paper's own theorem number or LaTeX label.

**Why keys and not paths.** This follows arlib's convention, and for the same
reason: citations that point at files under a local `source/` directory are
unresolvable for every reader who is not the original author, and they break
whenever a paper is re-downloaded. A theorem number survives both. arlib's own
[REFERENCES.md](https://github.com/meelgroup/arlib/blob/main/REFERENCES.md)
covers everything an entry here inherits from the dependency.

## Sources

**`CV18`** — Ben Cousins, Santosh Vempala. *Gaussian Cooling and
$O^*(n^3)$ Algorithms for Volume and Gaussian Volume.* SIAM Journal on
Computing 47(4):1454–1484, 2018. The journal paper combines and extends the
STOC 2015 and SODA 2014 versions.

**`BL76`** — Herm Jan Brascamp, Elliott H. Lieb. *On extensions of the
Brunn–Minkowski and Prékopa–Leindler theorems, including inequalities for log
concave functions, and with an application to the diffusion equation.* Journal
of Functional Analysis 22(4):366–389, 1976.

**`KLS95`** — Ravi Kannan, László Lovász, Miklós Simonovits. *Isoperimetric
problems for convex bodies and a localization lemma.* Discrete & Computational
Geometry 13:541–559, 1995.

**`KLS97`** — Ravi Kannan, László Lovász, Miklós Simonovits. *Random walks and
an $O^*(n^5)$ volume algorithm for convex bodies.* Random Structures &
Algorithms 11(1):1–50, 1997.

**`KV97`** — Ravi Kannan, Santosh Vempala. *Sampling lattice points.*
Proceedings of the 29th Annual ACM Symposium on Theory of Computing (STOC),
1997, pp. 696–700.

**`LS93`** — László Lovász, Miklós Simonovits. *Random walks in a convex body
and an improved volume algorithm.* Random Structures & Algorithms
4(4):359–412, 1993.

**`LV06`** — László Lovász, Santosh Vempala. *Hit-and-run from a corner.* SIAM
Journal on Computing 35(4):985–1005, 2006. The STOC 2004 version has the same
title.

**`Lov99`** — László Lovász. *Hit-and-run mixes fast.* Mathematical
Programming 86 (1999), 443–461.
<https://faculty.washington.edu/harin/L1.pdf>

**`Hub10`** — Mark Huber, Sarah Schott. *Using TPA for Bayesian Inference.*
Bayesian Statistics 9, OUP, 2010, pp. 257–282. arXiv:0907.2989.

**`Hub15`** — Mark Huber. *Approximation Algorithms for the Normalizing Constant of Gibbs
Distributions.* Ann. Appl. Probab. 25(2):974–985, 2015. arXiv:1206.2689.

**`BGHP`** — Jacqueline Banks, Scott Garrabrant, Mark L. Huber, Anne Perizzolo.
*Using TPA to Count Linear Extensions.* arXiv:1010.4981; J. Discrete Algorithms (2018).
(Not cited here directly; it is the source of `Arlib.Probability.poissonPMF`'s
tail bounds, which `ArlibCommunity/Algorithms/TPA/UniformProduct.lean` consumes.)

## Known gaps

A gap is a place where a docstring quotes a result without saying whose it is.
They are listed rather than guessed at, because a plausible-looking wrong
citation is worse than an acknowledged missing one — it survives review. Each
needs an answer from the author, and until it has one the corresponding
docstrings say the source is unknown instead of naming a paper.

| Where | What is cited | What is known |
| --- | --- | --- |
| `ArlibCommunity/Algorithms/TPA/**` | "Huber, 2010" in three files, but `TwoPhase.lean` cites "its Theorem 5" and a two-phase schedule matching Huber 2015. | One of the two attributions is wrong; they are different papers (`Hub10` vs `Hub15`). A third Huber paper, `BGHP`, is cited correctly in arlib. Inherited from arlib, where the area originally lived. |

## Results cited but not in this repository

Some docstrings compare a result here with a declaration or file from the
author's unpublished Arlib development, which this repository does not vendor.
Those mentions use the bare name and say "not in this repository". They are
pointers for the author, not citations: nothing in this repository depends on
them, and none of them is checked by this repository's build.

| Name | Original file | What it is |
| --- | --- | --- |
| `not_hIso_two`, `not_hIso_two_measurable`, `cexK_hitAndRun_hypotheses`, `cexH_not_le_third` | `LovaszVempalaIsoFalse.lean` | A counterexample at `n = 2`, `K = [0,4]²` to the hit-and-run isoperimetry hypothesis without the clause `h ≤ 1/3` ([LV06], Theorem 2.1 as printed), including with `h` measurable |
| (P1), (G1) | `PositionalCut.lean`, `TransverseCut.lean` | The open statements of the positional cut that `HamSandwich.lean` settles |
| `two_pow_mul_ell_cube_corner_le_one` | `EllFloor.lean` | The local conductance at a corner of `[-1,1]ⁿ` is at most `2⁻ⁿ` |
| `isWarm_coolLaw_succ_sqrt_exp` | `WarmChain.lean` | Warmness `√e` at the cooling schedule `σ²ᵢ₊₁ = (1 + 1/n)σ²ᵢ` of [CV18] |
| `prod_sq_div_le` | `Estimator.lean` | Relative second moments multiply over independent factors |
| `TVLe.bind` | `TVKernel.lean` | Total variation does not grow under a Markov kernel (real-valued form) |
| — | `PhaseInduction.lean` | Composition of cooling phases, with error accumulated geometrically |
| — | `KLS97.lean` | The [KLS97] boundary-layer bound with `n` in place of `√n` |
| `cor_linf` | `KV97/Corollary.lean` | The [KV97] corollary: after rejection, every lattice point has probability within `1 ± 4(ε+E)` of `1/N` |
| `exists_unconditional_mixing_unitBall_nonstationary` | `WarmStart.lean` | A ball-walk mixing witness on the unit ball from a non-stationary start |
| `exists_mem_Icc_second_moment_le`, `lintegral_pi_prod_indicator_tent` | `BrascampLieb1D.lean`, `ContTent.lean` | The sharp one-dimensional second-moment bound obtained as the limit `k → 0` in `BrascampLieb1D.lean`; the product formula for the `∫⁻` of the tent kernel |
| — | `SpeedyToUniform.lean`, `Geometric.lean`, `IsoIndicatorEll.lean` | Speedy-walk-to-uniform transfer; geometric distributions; the `ℓ`-weighted indicator isoperimetry |
