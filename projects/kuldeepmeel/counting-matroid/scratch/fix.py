import re,sys
p='CountingMatroid/Analysis/RestartDrawProbeScanReplay.lean'
s=open(p).read()
start=s.index('          · subst hcm\n')
end=s.index('          · rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ tape s q w ordinal draw current\n              count hallow hcm] at h')
new='''          · subst hcm
            have key : ∀ (tp : ℕ → Bool) (d : ℕ × ℕ),
                chainDrawSite r o₁ o₂ tp s q w current.state current.bitCursor draw = some d →
                (Arlib.Computation.Charged.foldlWhile
                  (fun acc (_ : ℕ) => probedBody r o₁ o₂ tp s q w count draw acc) (a :: xs)
                  (((some current, false), count), none)).val.2 = some d := by
              intro tp d hd
              rw [probedBody_scan_cons, probedBody_eq r o₁ o₂ tp s q w draw current count hallow]
              cases hcs : (chainStep r o₁ o₂ tp s.drawTrials q w current.state
                  current.bitCursor).val with
              | none =>
                simp only
                rw [hd]
                exact probedBody_scan_sticky r o₁ o₂ tp s q w count draw xs _ d
              | some result =>
                obtain ⟨state, bitCursor⟩ := result
                simp only
                rw [hd]
                exact probedBody_scan_sticky r o₁ o₂ tp s q w count draw xs _ d
            cases hsite0 : chainDrawSite r o₁ o₂ tape s q w current.state current.bitCursor draw with
            | none =>
              exfalso
              rw [probedBody_scan_cons, probedBody_eq r o₁ o₂ tape s q w draw current count
                hallow] at h
              cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state
                  current.bitCursor).val with
              | none =>
                rw [hcs, hsite0] at h
                simp only at h
                rw [probedBody_scan_frozen r o₁ o₂ tape s q w count draw xs none true
                  (count + 1) (Or.inl rfl)] at h
                cases h
              | some result =>
                obtain ⟨state, bitCursor⟩ := result
                rw [hcs, hsite0] at h
                simp only at h
                rw [probedBody_scan_past r o₁ o₂ tape s q w count draw xs _ (count + 1)
                  (Nat.lt_succ_self count)] at h
                cases h
            | some d =>
              have h0 := h
              rw [key tape d hsite0] at h0
              cases h0
              have hsite := chainDrawSite_success_interval r o₁ o₂ s q w current.state
                current.bitCursor draw tape d hsite0
              refine ⟨hfl.trans hsite.1, ?_⟩
              intro other hagree
              exact key other d (hsite.2 other (fun i hlo hhi => hagree i (hfl.trans hlo) hhi))
'''
s=s[:start]+new+s[end:]
# nil case
s=s.replace('''    simp only [Arlib.Computation.Charged.val_foldlWhile_nil] at h
''','''    cases h
''')
s=s.replace('''              refine ⟨hfl.trans (hstep.1.trans hr.1), ?_⟩
              intro other hagree
              dsimp only
''','''              refine ⟨hfl.trans (hstep.1.trans hr.1), ?_⟩
              intro other hagree
''')
lemma='''/-- INTERNAL: Scanning from a running count already past the probed ordinal,
with nothing captured yet, never captures anything. -/
private theorem probedBody_scan_past {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ) :
    ∀ (acc1 : Option (RestartCursor n) × Bool) (count : ℕ), ordinal < count →
    (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
        ((acc1, count), none)).val.2 = none := by
  induction xs with
  | nil => intro acc1 count _; rfl
  | cons a xs ih =>
    intro acc1 count hlt
    obtain ⟨cur, done⟩ := acc1
    cases done with
    | true => exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw (a :: xs) cur true
        count (Or.inr rfl)
    | false =>
      cases cur with
      | none => exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw (a :: xs) none
          false count (Or.inl rfl)
      | some current =>
        by_cases hallow : current.attempts < s.restartCap
        · rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ tape s q w ordinal draw current
            count hallow (by omega)]
          cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state
              current.bitCursor).val with
          | none =>
            simp only
            exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw xs none true
              (count + 1) (Or.inl rfl)
          | some result =>
            obtain ⟨state, bitCursor⟩ := result
            simp only
            exact ih _ (count + 1) (by omega)
        · rw [probedBody_scan_cons, probedBody_refused r o₁ o₂ tape s q w ordinal draw current
            count hallow]
          simp only
          exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw xs none true count
            (Or.inl rfl)

/-- INTERNAL: Interval replay for the probe's own capped return scan'''
s=s.replace('/-- INTERNAL: Interval replay for the probe\'s own capped return scan',lemma,1)
open(p,'w').write(s)
