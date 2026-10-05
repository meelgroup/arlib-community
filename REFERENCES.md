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
