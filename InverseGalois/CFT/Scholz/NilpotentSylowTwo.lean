import Mathlib
import InverseGalois.CFT.Scholz.NilpotentOdd

/-!
# Nilpotent groups whose Sylow `2`-subgroup is realised by other means

The Scholz–Reichardt induction is available for the odd primes only: the argument that the
induction rests on fails at `2`, and the theorem is stated for `ℓ` odd.  A finite nilpotent group,
however, is the direct product of its Sylow subgroups, and the inverse Galois property is closed
under products of groups of coprime order.  The odd Sylow subgroups are therefore realised by the
induction and the prime `2` is the only one left; whenever a realization of the Sylow `2`-subgroup
is available from any other source, the whole group is realised.

The hypothesis on the prime `2` is stated as an assumption here, so that the file stays inside the
class field theory layer.  It is discharged unconditionally for a large class of `2`-groups by the
regular constructions of the rigidity layer.

## Main results

* `InverseGalois.CFT.isInverseGalois_of_isNilpotent_of_sylow_two`: **granted the central step for
  the odd primes, a finite nilpotent group whose Sylow `2`-subgroups are Galois groups over `ℚ` is
  a Galois group over `ℚ`.**
* `InverseGalois.CFT.isInverseGalois_of_nilpotent_of_sylow_two`: the same conclusion with
  nilpotency supplied as an ordinary hypothesis rather than an instance.
-/

namespace InverseGalois.CFT

/-- **Granted the central step for the odd primes, a finite nilpotent group whose Sylow
`2`-subgroups are Galois groups over `ℚ` is a Galois group over `ℚ`.**  A finite nilpotent group is
the direct product of its Sylow subgroups, whose orders are pairwise coprime; the Sylow subgroup
for an odd prime is realised by the Scholz–Reichardt induction, and the one for the prime `2` is
realised by hypothesis. -/
theorem isInverseGalois_of_isNilpotent_of_sylow_two
    (hstep : ∀ q : ℕ, q.Prime → Odd q → IsCentralStepSolvable q) (G : Type) [Group G] [Finite G]
    [Group.IsNilpotent G] (h2 : ∀ P : Sylow 2 G, IsInverseGalois ↥(P : Subgroup G)) :
    IsInverseGalois G := by
  refine isInverseGalois_of_isNilpotent fun p hp P => ?_
  rcases eq_or_ne p 2 with rfl | hp2
  · exact h2 P
  · exact isInverseGalois_of_isPGroup_odd hstep hp.out (hp.out.odd_of_ne_two hp2) _ P.isPGroup'

/-- **Granted the central step for the odd primes, a finite nilpotent group whose Sylow
`2`-subgroups are Galois groups over `ℚ` is a Galois group over `ℚ`**, with the nilpotency supplied
as an ordinary hypothesis. -/
theorem isInverseGalois_of_nilpotent_of_sylow_two
    (hstep : ∀ q : ℕ, q.Prime → Odd q → IsCentralStepSolvable q) (G : Type) [Group G] [Finite G]
    (hnil : Group.IsNilpotent G) (h2 : ∀ P : Sylow 2 G, IsInverseGalois ↥(P : Subgroup G)) :
    IsInverseGalois G :=
  haveI := hnil
  isInverseGalois_of_isNilpotent_of_sylow_two hstep G h2

end InverseGalois.CFT
