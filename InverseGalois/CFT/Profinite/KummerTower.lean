/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerTwist
import InverseGalois.CFT.Profinite.TwistRes

/-!
# The Kummer classes of a tower, and the twist along it

A unit of an intermediate field is also a unit of every larger intermediate field, and Kummer
theory attaches a class of the first cohomology to it in both places.  The subgroup fixing the
larger field sits inside the subgroup fixing the smaller one, so a class over the smaller field can
be restricted; and **the restriction of the Kummer class of a unit is the Kummer class of that same
unit read in the larger field.**

The reason is again that the Kummer cochain is characterised rather than merely constructed: it is
the only cochain whose image in the units of the ambient extension is the coboundary of a root of
the unit.  The chosen root over the larger field and the chosen root over the smaller one are two
roots of the same element of the ambient extension, so they have the same coboundary, and the two
cochains agree before any class is taken.

Twisting by a homomorphism of the coefficients is functorial in the group, so the same statement
holds for the coefficients of a lifting problem.  Read through the identification of the first
cohomology with the tensor product of the units with the homomorphisms of the roots of unity,
**restricting a class to the larger field is including the units into the larger field.**  For a
decomposition subgroup this is the localisation of a class at a place.

## Main results

* `InverseGalois.CFT.kummerSubCochain_tower`: the Kummer cochain of a unit, restricted, is the
  Kummer cochain of its image.
* `InverseGalois.CFT.resInclH1_kummerSubHom`: **the Kummer homomorphisms of a tower are compatible
  with restriction.**
* `InverseGalois.CFT.resInclH1_kummerTwistEquiv`: **the Kummer twist is compatible with
  restriction**, corresponding to the inclusion of the units.

## Tags

Kummer theory, tower of fields, restriction, localisation, Galois cohomology, twist
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IntermediateField groupCohomology TensorProduct

/-! ### The Kummer cochain of a tower -/

section Tower

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K L : IntermediateField k Ω}
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/↥L) M] [MulDistribMulAction Gal(Ω/k) M]
variable {ιK : M →* (↥K)ˣ} {ιL : M →* (↥L)ˣ} {p : ℕ} [NeZero p]
variable (hK : IsKummerData ↥K Ω M ιK p) (hL : IsKummerData ↥L Ω M ιL p)
variable (j : (↥K)ˣ →* (↥L)ˣ)
variable (hj : ∀ a : (↥K)ˣ, Units.map (algebraMap ↥L Ω : ↥L →* Ω) (j a)
  = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)
variable (hιj : ∀ m : M, Units.map (algebraMap ↥L Ω : ↥L →* Ω) (ιL m)
  = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m))
variable (hle : L.fixingSubgroup ≤ K.fixingSubgroup)

omit [MulDistribMulAction Gal(Ω/k) M] in
include hj hιj in
/-- **The Kummer cochain of a unit, read on the subgroup fixing a larger field, is the Kummer
cochain of its image there.** -/
theorem kummerSubCochain_tower (a : (↥K)ˣ) (y : ↥L.fixingSubgroup) :
    kummerSubCochain hK a (Subgroup.inclusion hle y) = kummerSubCochain hL (j a) y := by
  refine injective_units_algebraMap_comp (Ω := Ω) hL.injective ?_
  show Units.map (algebraMap ↥L Ω : ↥L →* Ω)
      (ιL (kummerSubCochain hK a (Subgroup.inclusion hle y)))
    = Units.map (algebraMap ↥L Ω : ↥L →* Ω) (ιL (kummerSubCochain hL (j a) y))
  rw [hιj (kummerSubCochain hK a (Subgroup.inclusion hle y)), kummerSubCochain_spec,
    kummerSubCochain_spec]
  have hpow : hK.root a ^ p = hL.root (j a) ^ p := by
    rw [hK.root_pow, hL.root_pow, hj]
  exact smul_div_eq_of_pow_eq hL.isPrimitiveRoot_primitiveRoot hL.exists_ι_eq hpow
    (fixingSubgroupEquiv L y)

include hj hιj in
/-- **The Kummer class of a unit restricts to the Kummer class of its image in a larger field.** -/
theorem resInclH1_kummerSubClass (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) (a : (↥K)ˣ) :
    resInclH1 hle (kummerSubClass hK htriv a) = kummerSubClass hL htriv (j a) := by
  refine Eq.trans (resInclH1_smoothH1Mk hle (isMulCocycle₁_kummerSubCochain hK htriv a)
    (isSmooth₁_kummerSubCochain hK a)) ?_
  exact smoothH1Mk_congr (funext fun y => kummerSubCochain_tower hK hL j hj hιj hle a y) _ _ _ _

variable [FiniteDimensional k ↥K] [FiniteDimensional k ↥L]

include hj hιj in
/-- **The Kummer homomorphisms of a tower are compatible with restriction**: restricting the class
of a unit gives the class of that unit read in the larger field. -/
theorem resInclH1_kummerSubHom (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) (a : (↥K)ˣ) :
    resInclH1 hle (kummerSubHom hK htriv a) = kummerSubHom hL htriv (j a) :=
  resInclH1_kummerSubClass hK hL j hj hιj hle htriv a

end Tower

/-! ### The twist along a tower -/

section TwistTower

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K L : IntermediateField k Ω} [FiniteDimensional k ↥K] [FiniteDimensional k ↥L]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/↥L) M] [MulDistribMulAction Gal(Ω/k) M]
variable {ιK : M →* (↥K)ˣ} {ιL : M →* (↥L)ˣ} {p : ℕ} [NeZero p]
variable {E : Type*} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (hK : IsKummerData ↥K Ω M ιK p) (hL : IsKummerData ↥L Ω M ιL p)
variable (j : (↥K)ˣ →* (↥L)ˣ)
variable (hj : ∀ a : (↥K)ˣ, Units.map (algebraMap ↥L Ω : ↥L →* Ω) (j a)
  = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)
variable (hιj : ∀ m : M, Units.map (algebraMap ↥L Ω : ↥L →* Ω) (ιL m)
  = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m))
variable (hle : L.fixingSubgroup ≤ K.fixingSubgroup)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivEK : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable (htrivEL : ∀ (x : ↥L.fixingSubgroup) (e : E), x • e = e)

include hj hιj in
/-- **A twisted Kummer class restricts to the twisted Kummer class of the image of the unit.** -/
theorem resInclH1_kummerTwistClass (a : (↥K)ˣ) (w : M →* E) :
    resInclH1 hle (twistClass (smul_fixingSubgroup_eq_of_trivial htriv) htrivEK
        (kummerSubHom hK htriv) a w)
      = twistClass (smul_fixingSubgroup_eq_of_trivial htriv) htrivEL (kummerSubHom hL htriv)
        (j a) w :=
  resInclH1_twistClass hle (smul_fixingSubgroup_eq_of_trivial htriv) htrivEK
    (smul_fixingSubgroup_eq_of_trivial htriv) htrivEL (kummerSubHom hK htriv)
    (kummerSubHom hL htriv) j (resInclH1_kummerSubHom hK hL j hj hιj hle htriv) a w

include hj hιj in
/-- **The twisting map is natural for restriction to a larger field**, which on the units is the
inclusion. -/
theorem resInclH1_kummerTwistMap (z : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (resInclH1 hle)
        (twistMap (smul_fixingSubgroup_eq_of_trivial htriv) htrivEK (kummerSubHom hK htriv) z)
      = twistMap (smul_fixingSubgroup_eq_of_trivial htriv) htrivEL (kummerSubHom hL htriv)
        (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id z) :=
  resInclH1_twistMap hle (smul_fixingSubgroup_eq_of_trivial htriv) htrivEK
    (smul_fixingSubgroup_eq_of_trivial htriv) htrivEL (kummerSubHom hK htriv)
    (kummerSubHom hL htriv) j (resInclH1_kummerSubHom hK hL j hj hιj hle htriv) z

variable {J : Type*} [Fintype J] [DecidableEq J] (α : E ≃* (J → M)) (hEp : ∀ e : E, e ^ p = 1)

include hj hιj in
/-- **The Kummer twist is compatible with restriction to a larger field**: under the identification
of the first cohomology of the subgroup fixing a field with the tensor product of the units of that
field with the homomorphisms of the roots of unity into the coefficients, restricting a class is
including the units. -/
theorem resInclH1_kummerTwistEquiv [IsCyclic M] (z : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (resInclH1 hle) (kummerTwistEquiv hK htriv htrivEK α hEp z)
      = kummerTwistEquiv hL htriv htrivEL α hEp
        (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id z) :=
  resInclH1_kummerTwistMap hK hL j hj hιj hle htriv htrivEK htrivEL z

end TwistTower

end InverseGalois.CFT
