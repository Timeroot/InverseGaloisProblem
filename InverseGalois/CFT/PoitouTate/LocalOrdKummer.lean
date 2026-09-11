/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.LocalOrdBridge
import InverseGalois.CFT.Profinite.KummerLocalSurjective

/-!
# The dictionary at a place, from the units of a compositum

The dictionary at a place asks for an equivariant homomorphism out of the first cohomology of the
decomposition subgroup there which computes, on a twisted Kummer class, the valuation of that class
at the place.  Such a homomorphism exists as soon as localisation at the place is surjective and
kills only classes whose valuation vanishes: the first makes the homomorphism defined everywhere,
the second makes it well defined, and equivariance is inherited from equivariance of the two maps
being compared, the decomposition subgroup fixing the place.

Under the twisted Kummer identification both conditions are conditions on the inclusion of the
units of the subextension into the units of its compositum with the fixed field of the
decomposition subgroup, tensored with the coefficients: **surjectivity of that inclusion** and
**vanishing of the valuation on what it kills**.  The second is in turn a consequence of the
valuation factoring through any homomorphism of the units whose kernel the inclusion already meets.

## Main results

* `InverseGalois.CFT.tensorVal_eq_zero_of_tensorMap_eq_zero`: **the valuation at a place of a
  tensor killed by a homomorphism through which the valuation factors vanishes.**
* `InverseGalois.CFT.hasLocalOrdHom_of_surjective_tensor`: **the dictionary at a place, from
  surjectivity of the inclusion of the units and vanishing of the valuation on its kernel.**

## Tags

Kummer theory, Galois cohomology, decomposition group, localisation, valuation
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open groupCohomology TensorProduct

/-! ### A valuation which factors -/

section Factor

variable {Q : Type*} [Group Q] {A : Type*} [CommGroup A] [MulDistribMulAction Q A]
variable {A' : Type*} [CommGroup A']
variable (C : Type*) [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type*} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ))

/-- **The valuation at a place of a tensor killed by a homomorphism through which the valuation
factors vanishes.**  The valuation at the place, read on the tensor, is the given homomorphism
tensored with the coefficients followed by evaluation, so it vanishes wherever that homomorphism
tensored with the coefficients does. -/
theorem tensorVal_eq_zero_of_tensorMap_eq_zero (γ : Additive A →+ Additive A')
    (γx : Additive A' →+ ℤ) (x : X) (hcomm : ∀ a : Additive A, γx (γ a) = g a x)
    {t : Additive A ⊗[ℤ] Additive C}
    (ht : TensorProduct.map γ.toIntLinearMap (LinearMap.id : Additive C →ₗ[ℤ] Additive C) t = 0) :
    tensorVal C g t x = 0 := by
  have key : ∀ s : Additive A ⊗[ℤ] Additive C,
      tensorVal C g s x
        = (TensorProduct.lid ℤ (Additive C))
            (LinearMap.rTensor (Additive C) γx.toIntLinearMap
              (TensorProduct.map γ.toIntLinearMap LinearMap.id s)) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a w =>
      have hL : tensorVal C g (a ⊗ₜ[ℤ] w) x = g a x • w :=
        tensorVal_tmul_apply C g (Additive.toMul a) (Additive.toMul w) x
      rw [hL, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.rTensor_tmul,
        TensorProduct.lid_tmul, ← hcomm a]
      rfl
    | add s s' hs hs' =>
      simp only [map_add, Finsupp.add_apply, hs, hs']
  rw [key, ht, map_zero, map_zero]

end Factor

/-! ### The dictionary -/

section Dict

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K F : IntermediateField k Ω}
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ι : M →* (↥K)ˣ}
variable [MulDistribMulAction Gal(Ω/↥(K ⊔ F)) M] {ιL : M →* (↥(K ⊔ F))ˣ}
variable {p : ℕ} [NeZero p] [MulDistribMulAction Gal(Ω/k) M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (h : IsKummerData ↥K Ω M ι p) (hL : IsKummerData ↥(K ⊔ F) Ω M ιL p)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivE : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable (htrivEL : ∀ (x : ↥(K ⊔ F).fixingSubgroup) (e : E), x • e = e)
variable {J : Type} [Fintype J] [DecidableEq J] (α : E ≃* (J → M))
variable (hEp : ∀ e : E, e ^ p = 1) [Normal k ↥K] [IsCyclic M]
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
variable [ActsTrivially K.fixingSubgroup (M →* E)]
variable {X : Type} [MulAction (Gal(Ω/k) ⧸ K.fixingSubgroup) X] [DecidableEq X]
variable (g : Additive (↥K)ˣ →+ (X →₀ ℤ))
variable (jU : (↥K)ˣ →* (↥(K ⊔ F))ˣ)
variable (hj : ∀ a : (↥K)ˣ, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (jU a)
  = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)
variable (hιj : ∀ m : M, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (ιL m)
  = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))

include hL hj hιj htrivEL hfix in
/-- **The dictionary at a place, from surjectivity of the inclusion of the units and vanishing of
the valuation on its kernel.**  Localisation at the place is surjective and kills only twisted
Kummer classes whose datum the inclusion kills, hence only classes whose valuation at the place
vanishes; so the valuation factors through localisation.  The factorisation is equivariant for the
decomposition subgroup because both the valuation and localisation are, the subgroup fixing the
place. -/
theorem hasLocalOrdHom_of_surjective_tensor {S : Set (Subgroup Gal(Ω/k))}
    {D : Subgroup Gal(Ω/k)} (hDS : D ∈ S) (hD : F.fixingSubgroup = D) {x : X}
    (hstab : ∀ ρ : Gal(Ω/k) ⧸ K.fixingSubgroup, ρ • x = x →
      ∃ σ ∈ D, (QuotientGroup.mk σ : Gal(Ω/k) ⧸ K.fixingSubgroup) = ρ)
    (hDx : ∀ σ ∈ D, (QuotientGroup.mk σ : Gal(Ω/k) ⧸ K.fixingSubgroup) • x = x)
    (hgeq : ∀ (σ : Gal(Ω/k) ⧸ K.fixingSubgroup) (a : (↥K)ˣ) (y : X),
      g (Additive.ofMul (σ • a)) y = g (Additive.ofMul a) (σ⁻¹ • y))
    (hsurj : Function.Surjective (TensorProduct.map (MonoidHom.toAdditive jU).toIntLinearMap
      (LinearMap.id : Additive (M →* E) →ₗ[ℤ] Additive (M →* E))))
    (hker : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive jU).toIntLinearMap LinearMap.id t = 0 →
        tensorVal (M →* E) g t x = 0) :
    HasLocalOrdHom h htriv htrivE α hEp g S x := by
  classical
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SmoothH1 ↥K.fixingSubgroup E →* (M →* E), ∀ z, ψ z =
      Additive.toMul (tensorVal (M →* E) g
        ((kummerTwistEquiv h htriv htrivE α hEp).symm (Additive.ofMul z)) x) :=
    ⟨{ toFun := fun z => Additive.toMul (tensorVal (M →* E) g
          ((kummerTwistEquiv h htriv htrivE α hEp).symm (Additive.ofMul z)) x)
       map_one' := by
         rw [show (Additive.ofMul (1 : SmoothH1 ↥K.fixingSubgroup E)) = 0 from rfl, map_zero,
           map_zero, Finsupp.coe_zero, Pi.zero_apply]
         rfl
       map_mul' := fun z z' => by
         rw [_root_.ofMul_mul, map_add, map_add, Finsupp.add_apply, _root_.toMul_add] },
      fun _ => rfl⟩
  have hcomp : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      ψ (Additive.toMul (kummerTwistEquiv h htriv htrivE α hEp t))
        = Additive.toMul (tensorVal (M →* E) g t x) := by
    intro t
    rw [hψ, show (Additive.ofMul (Additive.toMul (kummerTwistEquiv h htriv htrivE α hEp t)))
      = kummerTwistEquiv h htriv htrivE α hEp t from rfl, AddEquiv.symm_apply_apply]
  have hsurjR : Function.Surjective (resSubH1 K.fixingSubgroup D (M := E)) :=
    surjective_resSubH1_of_surjective_tensor h hL jU hj hιj hD htriv htrivE htrivEL α hEp hsurj
  have hle : (resSubH1 K.fixingSubgroup D (M := E)).ker ≤ ψ.ker :=
    ker_resSubH1_le h hL jU hj hιj hD htriv htrivE htrivEL α hEp ψ (fun t ht => by
      rw [hcomp t, hker t ht]
      rfl)
  refine ⟨D, hDS, hstab, (resSubH1 K.fixingSubgroup D).liftOfRightInverse
    (Function.surjInv hsurjR) (Function.rightInverse_surjInv hsurjR) ⟨ψ, hle⟩, ?_, ?_⟩
  · intro σ z
    obtain ⟨w, rfl⟩ := hsurjR z
    rw [← resSubH1_smul D σ w, MonoidHom.liftOfRightInverse_comp_apply,
      MonoidHom.liftOfRightInverse_comp_apply]
    have hsm : (σ • w : SmoothH1 ↥K.fixingSubgroup E) = (σ : Gal(Ω/k)) • w := rfl
    have hq : (QuotientGroup.mk (σ : Gal(Ω/k)) : Gal(Ω/k) ⧸ K.fixingSubgroup) • x = x :=
      hDx (σ : Gal(Ω/k)) σ.2
    have hqinv : (QuotientGroup.mk (σ : Gal(Ω/k)) : Gal(Ω/k) ⧸ K.fixingSubgroup)⁻¹ • x = x := by
      rw [inv_smul_eq_iff, hq]
    have hesymm : (kummerTwistEquiv h htriv htrivE α hEp).symm
        (Additive.ofMul ((σ : Gal(Ω/k)) • w))
        = (QuotientGroup.mk (σ : Gal(Ω/k)) : Gal(Ω/k) ⧸ K.fixingSubgroup) •
          (kummerTwistEquiv h htriv htrivE α hEp).symm (Additive.ofMul w) := by
      refine (kummerTwistEquiv h htriv htrivE α hEp).injective ?_
      rw [AddEquiv.apply_symm_apply, kummerTwistEquiv_smul h htriv htrivE α hEp hfix,
        AddEquiv.apply_symm_apply]
      rfl
    show ψ (σ • w) = (σ : Gal(Ω/k)) • ψ w
    rw [hψ, hψ, hsm, hesymm, tensorVal_smul (M →* E) g hgeq, hqinv]
    exact quotientMk_smul K.fixingSubgroup (M →* E) (σ : Gal(Ω/k)) _
  · intro t
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    exact hcomp t

end Dict

end InverseGalois.CFT
