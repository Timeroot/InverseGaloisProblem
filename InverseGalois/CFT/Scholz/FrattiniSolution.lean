/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.FrattiniStep
import InverseGalois.CFT.Scholz.ResidueCorrection

/-!
# The central step of the Scholz–Reichardt induction

The three stages of the construction now meet.  A central Frattini embedding problem with kernel of
prime order over a realization at the next level is first solved over the cyclotomic base and
descended; the unwanted ramification of that solution is then removed prime by prime; and finally
the residue degrees are corrected by a twist read off an auxiliary modulus.  What comes out is a
realization of the source of the embedding problem at the level the induction asks for, which is
exactly the central step in the form the Frattini reduction leaves it.

One local ingredient is carried through all of this untouched: at the residue characteristic itself
the inertia subgroup need not be cyclic, and the correcting twist needs to know that the
homomorphisms of order dividing the residue characteristic are nonetheless all powers of one of
them.  That is the rank one condition, and it is the only hypothesis of the central step that is
not discharged here.

## Main results

* `InverseGalois.CFT.isFrattiniCentralStepSolvable_of_isInertiaRankOneAt`: **granted the rank one
  condition at an odd prime, the central embedding step is solvable for kernels inside the Frattini
  subgroup.**
* `InverseGalois.CFT.isCentralStepSolvable_of_isInertiaRankOneAt`: **granted the rank one condition
  at an odd prime, the central embedding step is solvable.**

## Tags

Scholz–Reichardt, embedding problem, Frattini subgroup, central extension, inertia subgroup
-/

namespace InverseGalois.CFT

variable {ℓ : ℕ}

/-- **Granted the rank one condition at an odd prime, the central embedding step is solvable for
kernels inside the Frattini subgroup.**  The solution ramifying no more than the field below is
corrected at the primes ramified there by a twist whose power residue symbols are the Frobenius
defects, and the primes brought in by the correction split completely below and so are handled by
the prime order of the kernel. -/
theorem isFrattiniCentralStepSolvable_of_isInertiaRankOneAt (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hrank : IsInertiaRankOneAt ℓ) : IsFrattiniCentralStepSolvable ℓ := by
  intro N G H _ _ _ f hpg hsurj hker hcard hdvd hfr hH
  exact isScholzRealizable_of_centralStep hℓ hodd hrank hsurj hpg hker hfr hcard hdvd hH

/-- **Granted the rank one condition at an odd prime, the central embedding step is solvable.**  A
kernel of prime order escaping the Frattini subgroup is complemented by a maximal subgroup, so the
extension splits and the compositum construction realises it; the remaining kernels are the ones
the Scholz–Reichardt construction handles. -/
theorem isCentralStepSolvable_of_isInertiaRankOneAt (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hrank : IsInertiaRankOneAt ℓ) : IsCentralStepSolvable ℓ :=
  IsCentralStepSolvable.of_frattini hℓ
    (isFrattiniCentralStepSolvable_of_isInertiaRankOneAt hℓ hodd hrank)

end InverseGalois.CFT
