/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.ComapIso
import InverseGalois.CFT.Profinite.ShaCoeff
import InverseGalois.CFT.Units.HasseDecomposition

/-!
# Reading an everywhere locally trivial class at a level, along a map of the coefficients

Inflation from a finite Galois level is pullback along restriction to that level, and pullback
commutes with a map of the coefficients, so inflation does too.  An everywhere locally trivial class
of the first cohomology is determined by the class of the level it inflates from, and inflation is
injective, so the reading at the level is determined by what it inflates to; comparing the two
readings therefore comes down to comparing what they inflate to, and there the two operations
commute for the reason just given.

The upshot is that **reading an everywhere locally trivial class at the level commutes with a map of
the coefficients.**  It is the statement a duality argument needs in order to move the dual side of
the pairing while the class it is being tested against stays fixed.

## Main results

* `InverseGalois.CFT.galInflH1_coeffH1`: inflation from a finite Galois level commutes with a map of
  the coefficients.
* `InverseGalois.CFT.shaInflH1_shaCoeffH1`: **reading an everywhere locally trivial class at the
  level commutes with a map of the coefficients.**

## Tags

Galois cohomology, inflation, local-global principle, Shafarevich group, coefficients
-/

namespace InverseGalois.CFT

/-! ### Inflation and the coefficients -/

section Inflation

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {M N : Type*} [CommGroup M] [CommGroup N]
  [MulDistribMulAction Gal(K/k) M] [MulDistribMulAction Gal(K/k) N]
  (F : IntermediateField k K) [FiniteDimensional k F] [IsGalois k F]
  [MulDistribMulAction (F ≃ₐ[k] F) M] [MulDistribMulAction (F ≃ₐ[k] F) N]
  (hπM : ∀ (g : Gal(K/k)) (m : M), g • m = AlgEquiv.restrictNormalHom F g • m)
  (hπN : ∀ (g : Gal(K/k)) (n : N), g • n = AlgEquiv.restrictNormalHom F g • n)
  (φ : M →* N) (hφK : ∀ (g : Gal(K/k)) (m : M), φ (g • m) = g • φ m)
  (hφF : ∀ (g : F ≃ₐ[k] F) (m : M), φ (g • m) = g • φ m)

omit [IsGalois k K] in
include hπM hπN hφK hφF in
/-- **Inflation from a finite Galois level commutes with a map of the coefficients**: inflation is
pullback along restriction to the level, and pullback composes a cocycle on the other side from the
map of the coefficients. -/
theorem galInflH1_coeffH1 (x : SmoothH1 (↥F ≃ₐ[k] ↥F) M) :
    coeffH1 φ hφK (galInflH1 F hπM x) = galInflH1 F hπN (coeffH1 φ hφF x) :=
  coeffH1_comapH1 hπM hπN (isSmoothHom_restrictNormalHom F) hφK hφF x

end Inflation

/-! ### The reading at the level and the coefficients -/

section Sha

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {M N : Type*} [CommGroup M] [CommGroup N]
  [MulDistribMulAction Gal(K/k) M] [IsSmoothAction Gal(K/k) M]
  [MulDistribMulAction Gal(K/k) N] [IsSmoothAction Gal(K/k) N]
  (F : IntermediateField k K) [FiniteDimensional k F] [IsGalois k F] [NumberField ↥F]
  [MulDistribMulAction (F ≃ₐ[k] F) M] [MulDistribMulAction (F ≃ₐ[k] F) N]
  (hπM : ∀ (g : Gal(K/k)) (m : M), g • m = AlgEquiv.restrictNormalHom F g • m)
  (hπN : ∀ (g : Gal(K/k)) (n : N), g • n = AlgEquiv.restrictNormalHom F g • n)
  (φ : M →* N) (hφK : ∀ (g : Gal(K/k)) (m : M), φ (g • m) = g • φ m)
  (hφF : ∀ (g : F ≃ₐ[k] F) (m : M), φ (g • m) = g • φ m)

include hπM hπN hφK hφF

/-- **Reading an everywhere locally trivial class at the level commutes with a map of the
coefficients.**  Both readings inflate to the class carried along the map, and inflation from a
level is injective. -/
theorem shaInflH1_shaCoeffH1 (z : ↥(sha1 M (decompositionSubgroups k K))) :
    shaInflH1 N F hπN (shaCoeffH1 φ hφK (decompositionSubgroups k K) z)
      = coeffH1 φ hφF (shaInflH1 M F hπM z) := by
  refine galInflH1_injective F hπN ?_
  rw [galInflH1_shaInflH1, ← galInflH1_coeffH1 F hπM hπN φ hφK hφF, coe_shaCoeffH1,
    galInflH1_shaInflH1]

end Sha

end InverseGalois.CFT
