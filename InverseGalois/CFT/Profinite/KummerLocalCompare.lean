/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerLocalSurjective
import InverseGalois.CFT.Profinite.TransgressionRestrict

/-!
# A local condition read against any other localisation of the coefficients

A class of the first cohomology of a decomposition subgroup, with values in the first cohomology of
the subgroup fixing a level, is localised by restricting its coefficients along the comparison with
the subgroup fixing the compositum of the level with the fixed field of the place.  That comparison
is a map of the coefficients, so a class it kills is compared with the classes killed by any other
map of the coefficients through the general principle that a surjective map of the coefficients
kills the least it can.

Both hypotheses of that principle are available for the compositum: the comparison is surjective as
soon as the inclusion of the units into the units of the compositum is surjective modulo the
coefficients, and what it kills is the twisted Kummer classes whose datum that inclusion kills.  So
**a class trivial after localisation at the compositum is trivial after any map of the coefficients
which kills those data** — in particular after the map to the units of the completion at the place
below, for which killing them is the statement that a unit which becomes a power in the compositum
becomes a power in the completion.

## Main results

* `InverseGalois.CFT.coeffH1_eq_one_of_coeffH1_resSubH1_eq_one`: **a class killed by localisation at
  the compositum is killed by every map of the coefficients which kills the data the inclusion of
  the units kills.**
* `InverseGalois.CFT.coeffH1_resH1_eq_one_of_resCoeffH1_eq_one`: the same for a global class,
  written against the localisation of the first cohomology of the whole group.

## Tags

Kummer theory, Galois cohomology, decomposition group, localisation, compositum, completion
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IntermediateField groupCohomology TensorProduct

section Compare

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K F : IntermediateField k Ω} [K.fixingSubgroup.Normal]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/↥(K ⊔ F)) M] [MulDistribMulAction Gal(Ω/k) M]
variable {ιK : M →* (↥K)ˣ} {ιL : M →* (↥(K ⊔ F))ˣ} {p : ℕ} [NeZero p]
variable {E : Type*} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (hK : IsKummerData ↥K Ω M ιK p) (hL : IsKummerData ↥(K ⊔ F) Ω M ιL p)
variable (j : (↥K)ˣ →* (↥(K ⊔ F))ˣ)
variable (hj : ∀ a : (↥K)ˣ, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (j a)
  = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)
variable (hιj : ∀ m : M, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (ιL m)
  = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m))
variable {D : Subgroup Gal(Ω/k)} (hD : F.fixingSubgroup = D)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivEK : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable (htrivEL : ∀ (x : ↥(K ⊔ F).fixingSubgroup) (e : E), x • e = e)
variable {J : Type*} [Fintype J] [DecidableEq J] (α : E ≃* (J → M)) (hEp : ∀ e : E, e ^ p = 1)
variable {P : Type*} [CommGroup P] [MulDistribMulAction ↥D P]
variable (ψ : SmoothH1 ↥K.fixingSubgroup E →* P)
variable (hψ : ∀ (g : ↥D) (z : SmoothH1 ↥K.fixingSubgroup E), ψ (g • z) = g • ψ z)

include hj hιj hK hL hD htriv htrivEK htrivEL α hEp in
/-- **A class of a decomposition subgroup killed by localisation at the compositum is killed by
every map of the coefficients which kills the twisted Kummer data that the inclusion of the units
kills.**  Localisation is surjective on the coefficients and kills exactly those data, so it kills
the least a map of the coefficients can. -/
theorem coeffH1_eq_one_of_coeffH1_resSubH1_eq_one [IsCyclic M]
    (hsurj : Function.Surjective (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap
      (LinearMap.id : Additive (M →* E) →ₗ[ℤ] Additive (M →* E))))
    (hψker : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id t = 0 →
        ψ (Additive.toMul (kummerTwistEquiv hK htriv htrivEK α hEp t)) = 1)
    {x : SmoothH1 ↥D (SmoothH1 ↥K.fixingSubgroup E)}
    (hx : coeffH1 (resSubH1 K.fixingSubgroup D) (resSubH1_smul D) x = 1) :
    coeffH1 ψ hψ x = 1 :=
  coeffH1_eq_one_of_coeffH1_eq_one _ (resSubH1_smul D) ψ hψ
    (surjective_resSubH1_of_surjective_tensor hK hL j hj hιj hD htriv htrivEK htrivEL α hEp hsurj)
    (ker_resSubH1_le hK hL j hj hιj hD htriv htrivEK htrivEL α hEp ψ hψker) hx

include hj hιj hK hL hD htriv htrivEK htrivEL α hEp in
/-- **A globally defined class whose localisation at a place is trivial is trivial after every map
of the coefficients which kills the twisted Kummer data that the inclusion of the units kills.**
Localisation of a global class is restriction to the place followed by localisation of the
coefficients. -/
theorem coeffH1_resH1_eq_one_of_resCoeffH1_eq_one [IsCyclic M]
    (hsurj : Function.Surjective (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap
      (LinearMap.id : Additive (M →* E) →ₗ[ℤ] Additive (M →* E))))
    (hψker : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id t = 0 →
        ψ (Additive.toMul (kummerTwistEquiv hK htriv htrivEK α hEp t)) = 1)
    {z : SmoothH1 Gal(Ω/k) (SmoothH1 ↥K.fixingSubgroup E)}
    (hz : resCoeffH1 K.fixingSubgroup D z = 1) :
    coeffH1 ψ hψ (resH1 D z) = 1 :=
  coeffH1_eq_one_of_coeffH1_resSubH1_eq_one hK hL j hj hιj hD htriv htrivEK htrivEL α hEp ψ hψ
    hsurj hψker hz

end Compare

end InverseGalois.CFT
