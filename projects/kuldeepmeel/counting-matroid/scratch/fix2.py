p='CountingMatroid/Analysis/RestartDrawProbeScanReplay.lean'
s=open(p).read()
s=s.replace('''    | true => exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw (a :: xs) cur true
        count (Or.inr rfl)''','''    | true =>
      exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw (a :: xs) cur true
        count (Or.inr rfl)''')
s=s.replace('''      | none => exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw (a :: xs) none
          false count (Or.inl rfl)''','''      | none =>
        exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw (a :: xs) none
          false count (Or.inl rfl)''')
s=s.replace('''              rw [key tape d hsite0] at h0
              cases h0
''','''              rw [key tape d hsite0] at h0
              have hd : d = out := Option.some.inj h0
              subst hd
''')
s=s.replace('''              rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ tape s q w ordinal draw current
                count hallow hcm, heqstep]''','''              beta_reduce at heqstep heqrest ⊢
              rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ other s q w ordinal draw current
                count hallow hcm, heqstep]''')
open(p,'w').write(s)
