/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerLocalCompare
import InverseGalois.CFT.Profinite.TransgressionInflate

/-!
# The local condition at a place, read on the finite quotient of the decomposition subgroup

The obstruction of a Kummer embedding problem lives in the second cohomology of the whole Galois
group, and the transgression that measures it is controlled by the classes of the first cohomology
which are locally trivial everywhere.  Local triviality was recorded on the decomposition subgroup
itself; but the coefficients of these classes are acted on through the quotient by the subgroup
fixing the level, and so the condition is already a statement about the *finite* quotient of the
decomposition subgroup by its part fixing that level.  That is the form the obstruction consumes,
and it is the form in which the comparison of a level with a completion at the place can be read
against a finite Galois group.

Rewriting the comparison over the quotient costs nothing.  Surjectivity of the localisation of the
coefficients and the description of what it kills are statements about the coefficients alone, with
no reference to the acting group, and the quotient acts on those coefficients compatibly.  So **a
class of the quotient killed by localisation at the compositum is killed by every map of the
coefficients which kills the twisted Kummer data that the inclusion of the units kills**, and a
globally defined class which is locally trivial everywhere is killed at each place of the family.

## Main results

* `InverseGalois.CFT.coeffH1_eq_one_of_coeffQuotH1_eq_one`: **a class of the quotient of a
  decomposition subgroup, killed by localisation at the compositum, is killed by every map of the
  coefficients which kills the data the inclusion of the units kills.**
* `InverseGalois.CFT.coeffH1_resQuotH1_eq_one_of_resCoeffQuotH1_eq_one`: the same for a global
  class, written against the localisation of the first cohomology of the quotient by the level.
* `InverseGalois.CFT.coeffH1_resQuotH1_eq_one_of_mem_sha1Level`: **a class which is locally trivial
  at every subgroup of a family is killed at each member of that family** by every such map of the
  coefficients.

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
variable {P : Type*} [CommGroup P]
  [MulDistribMulAction (↥D ⧸ K.fixingSubgroup.subgroupOf D) P]
variable (ψ : SmoothH1 ↥K.fixingSubgroup E →* P)
variable (hψ : ∀ (g : ↥D ⧸ K.fixingSubgroup.subgroupOf D) (z : SmoothH1 ↥K.fixingSubgroup E),
  ψ (g • z) = g • ψ z)

include hj hιj hK hL hD htriv htrivEK htrivEL α hEp in
/-- **A class of the quotient of a decomposition subgroup by its part fixing the level, killed by
localisation at the compositum, is killed by every map of the coefficients which kills the twisted
Kummer data that the inclusion of the units kills.**  Localisation is surjective on the coefficients
and kills exactly those data, both without reference to the acting group, so it kills the least a
map of the coefficients can. -/
theorem coeffH1_eq_one_of_coeffQuotH1_eq_one [IsCyclic M]
    (hsurj : Function.Surjective (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap
      (LinearMap.id : Additive (M →* E) →ₗ[ℤ] Additive (M →* E))))
    (hψker : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id t = 0 →
        ψ (Additive.toMul (kummerTwistEquiv hK htriv htrivEK α hEp t)) = 1)
    {x : SmoothH1 (↥D ⧸ K.fixingSubgroup.subgroupOf D) (SmoothH1 ↥K.fixingSubgroup E)}
    (hx : coeffQuotH1 K.fixingSubgroup D x = 1) :
    coeffH1 ψ hψ x = 1 :=
  coeffH1_eq_one_of_coeffH1_eq_one _ (resSubH1_smul_quot (N := K.fixingSubgroup) D) ψ hψ
    (surjective_resSubH1_of_surjective_tensor hK hL j hj hιj hD htriv htrivEK htrivEL α hEp hsurj)
    (ker_resSubH1_le hK hL j hj hιj hD htriv htrivEK htrivEL α hEp ψ hψker) hx

include hj hιj hK hL hD htriv htrivEK htrivEL α hEp in
/-- **A globally defined class whose localisation at a place is trivial is trivial after every map
of the coefficients which kills the twisted Kummer data that the inclusion of the units kills**,
read on the quotient by the subgroup fixing the level.  Localisation of a global class is
restriction to the place followed by localisation of the coefficients. -/
theorem coeffH1_resQuotH1_eq_one_of_resCoeffQuotH1_eq_one [IsCyclic M]
    (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))
    (hsurj : Function.Surjective (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap
      (LinearMap.id : Additive (M →* E) →ₗ[ℤ] Additive (M →* E))))
    (hψker : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id t = 0 →
        ψ (Additive.toMul (kummerTwistEquiv hK htriv htrivEK α hEp t)) = 1)
    {z : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)}
    (hz : resCoeffQuotH1 K.fixingSubgroup D hop z = 1) :
    coeffH1 ψ hψ (resQuotH1 K.fixingSubgroup D hop z) = 1 :=
  coeffH1_eq_one_of_coeffQuotH1_eq_one hK hL j hj hιj hD htriv htrivEK htrivEL α hEp ψ hψ
    hsurj hψker hz

include hj hιj hK hL hD htriv htrivEK htrivEL α hEp in
/-- **A class which is locally trivial at every subgroup of a family is killed at each member of
that family** by every map of the coefficients which kills the twisted Kummer data that the
inclusion of the units kills.  Membership of the locally trivial classes of a level is exactly
triviality of the localisation at each subgroup of the family. -/
theorem coeffH1_resQuotH1_eq_one_of_mem_sha1Level [IsCyclic M]
    (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))
    (hsurj : Function.Surjective (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap
      (LinearMap.id : Additive (M →* E) →ₗ[ℤ] Additive (M →* E))))
    (hψker : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id t = 0 →
        ψ (Additive.toMul (kummerTwistEquiv hK htriv htrivEK α hEp t)) = 1)
    {S : Set (Subgroup Gal(Ω/k))} (hDS : D ∈ S)
    {z : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)}
    (hz : z ∈ sha1Level E K.fixingSubgroup hop S) :
    coeffH1 ψ hψ (resQuotH1 K.fixingSubgroup D hop z) = 1 :=
  coeffH1_resQuotH1_eq_one_of_resCoeffQuotH1_eq_one hK hL j hj hιj hD htriv htrivEK htrivEL α hEp
    ψ hψ hop hsurj hψker (mem_sha1Level_iff.1 hz D hDS)

end Compare

end InverseGalois.CFT
