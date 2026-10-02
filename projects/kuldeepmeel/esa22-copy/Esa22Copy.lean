/-
# Esa22Copy

Root module. Importing `Esa22Copy` must pull in the headline theorem, so that
`import Esa22Copy` and a bare `lake build` both compile *and expose* the result.

Keep this file a pure aggregation of area roots — put content in the modules.
-/

import Esa22Copy.Model.Theorem

/-
The whole-development checks. Imported here and nowhere else, because a file
nothing imports is a file `lake build` never compiles — and a check that never
runs is worse than no check, since it will be believed.
-/
import Esa22Copy.Meta.Audit
