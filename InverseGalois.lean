import InverseGalois.CFT
import InverseGalois.Core
import InverseGalois.Groups
import InverseGalois.Hilbert
import InverseGalois.NumberTheory
import InverseGalois.Reflection
import InverseGalois.Resolvent
import InverseGalois.Rigidity
import InverseGalois.GeneralLinear
import InverseGalois.Solvable
import InverseGalois.Shafarevich
import InverseGalois.Catalogue

/-!
# The inverse Galois problem over `ℚ`

This is the public entry point for the project.  The source tree is divided into core
notions, general polynomial tools, resolvents, concrete groups, Hilbert irreducibility,
reflection, the rigidity method, the group-theoretic reductions for solvable groups, and
auxiliary number theory.  `InverseGalois.CFT` collects the class field theory that the solvable
case calls for.

`InverseGalois.Shafarevich` joins the two routes towards the solvable case: the arithmetic
Scholz–Reichardt induction, which covers the odd primes, and the geometric wreath product
construction, which covers the prime `2`.

`InverseGalois.Catalogue` indexes the groups the project realizes, in the strongest form each
construction gives — regularly over `ℚ(T)` in every case.
-/
