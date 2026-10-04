import Nfa.Model.Prelude

/-!
# The step budgets of `countNFA`, as natural-number expressions

The running-time count of analysis.tex:40-55, 67-68 is carried out in two
stages.  `Nfa.Analysis.coreRun_cost` bounds `m` times the steps of one core run by
`coreBound m n W P`, and the parent bounds `m` times the steps of `countNFA` by
`countBound m n W P`; here `m = |Q|`, `W` is the price of one witness product and
`P` the parameter block.  The factor `m` keeps the `⌈|S^{i-1}|/m⌉` witness blocks
of computeCache exact in `ℕ`.  `Nfa.Analysis.countBound_le_target` then turns
`countBound` into the theorem's real bound.

The pieces of `coreBound`:

* `easFixed P = 3γ(β+1) + 2α + 12`: the part of one `estimateAndSample` call that
  does not grow with the stored samples (the predecessor scan aside);
* `layerFixed m W P`: `m` times the part of one layer that does not grow with the
  stored samples — two roster/arith steps, the `+1` block of each of the two
  `⌈rows/m⌉` witness loops, and `m` calls of `estimateAndSample` with their
  interrupt tests;
* `sampleCoef m W = 14m² + 2W`: what each sample of the previous layer costs,
  times `m` (it is read by up to `m` calls, and it pays `2W/m` of witness blocks);
* `cacheCoef m = m(m+2)`: what each sample of the current layer costs in
  updateCache, times `m`;
* `totalCap P = θ + α`: the most samples a run stores before it is interrupted.
-/

set_option autoImplicit false

namespace Nfa.Analysis

/-- INTERNAL: the sample-independent cost of one `estimateAndSample` call, apart
from its `4|prev|` predecessor scan.
TEXLINE: analysis.tex:40-55 -/
def easFixed (P : Params) : ℕ := 3 * P.γ * (P.β + 1) + 2 * P.α + 12

/-- INTERNAL: `m` times the sample-independent cost of one layer.
TEXLINE: analysis.tex:40-55 -/
def layerFixed (m W : ℕ) (P : Params) : ℕ :=
  2 * m + 2 * W * m + m ^ 2 * (4 * m + easFixed P + 1)

/-- INTERNAL: `m` times the cost charged to one sample of the previous layer.
TEXLINE: analysis.tex:40-55 -/
def sampleCoef (m W : ℕ) : ℕ := 14 * m ^ 2 + 2 * W

/-- INTERNAL: `m` times the cost charged to one sample of the current layer by
updateCache.
TEXLINE: algorithm.tex:129-161 -/
def cacheCoef (m : ℕ) : ℕ := m * (m + 2)

/-- INTERNAL: the most samples a core run holds while it is not interrupted.
TEXLINE: algorithm.tex:90-112 -/
def totalCap (P : Params) : ℕ := P.θ + P.α

/-- INTERNAL: `m` times the steps of one core run, at most.
TEXLINE: analysis.tex:40-55 -/
def coreBound (m n W : ℕ) (P : Params) : ℕ :=
  m * (6 + 2 * P.α + (n + 1) * m * P.α) + n * layerFixed m W P +
    (sampleCoef m W + cacheCoef m) * totalCap P

/-- INTERNAL: `m` times the steps of `countNFA`, at most.
TEXLINE: analysis.tex:67-68 -/
def countBound (m n W : ℕ) (P : Params) : ℕ :=
  m * (2 * n * m ^ 2 + m) + P.μ * (coreBound m n W P + m) + m

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · stated · budget definitions `coreBound`, `countBound` and their pieces
-/
