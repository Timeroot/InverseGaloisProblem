/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerLocal

/-!
# Localising a Kummer class at a place is surjective, and what it kills

Localising a class of the first cohomology at a place is restricting it to the part of the ambient
subgroup lying inside the decomposition subgroup, and that part is the subgroup fixing the
compositum of the subextension with the fixed field of the place.  The comparison between the two
readings of that part is an isomorphism of topological groups, so it induces an isomorphism in
cohomology; spelling out the inverse gives a two sided inverse of the comparison map, hence its
bijectivity.

Under the twisted Kummer identification the localisation becomes the inclusion of the units of the
field into the units of the compositum, tensored with the coefficients.  Bijectivity of the
comparison therefore transports two properties of that inclusion into two properties of the
localisation: **it is surjective as soon as the inclusion is**, and **a class it kills is a class
whose Kummer datum the inclusion kills**.  Both are exactly what is needed to compare the
localisation with any other map of the coefficients that kills at least as much.

## Main definitions

* `InverseGalois.CFT.comapInterH1Symm`: the inverse of the comparison map between the two readings
  of the part of a subgroup lying inside another one.

## Main results

* `InverseGalois.CFT.comapInterH1_injective`, `InverseGalois.CFT.comapInterH1_surjective`: **the
  comparison map is bijective.**
* `InverseGalois.CFT.resSubH1_kummerTwistEquiv_eq_one_iff`: **a twisted Kummer class dies under
  localisation exactly when its datum dies under the inclusion of the units.**
* `InverseGalois.CFT.surjective_resSubH1_of_surjective_tensor`: **localisation is surjective as soon
  as the inclusion of the units is.**
* `InverseGalois.CFT.ker_resSubH1_le`: **what localisation kills is killed by every map that kills
  the image of the inclusion of the units.**

## Tags

Kummer theory, Galois cohomology, decomposition group, localisation, compositum, surjectivity
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IntermediateField groupCohomology TensorProduct

/-! ### The comparison map is bijective -/

section Inter

variable {G : Type*} [Group G] [TopologicalSpace G] (N D : Subgroup G) {H : Subgroup G}
variable {A : Type*} [CommGroup A] [MulDistribMulAction G A]

/-- **The inverse of the comparison map between the two readings of the part of a subgroup lying
inside another one.**  It is the map induced by the inverse of the comparison isomorphism, which is
continuous for the same reason the comparison itself is. -/
def comapInterH1Symm (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D) :
    SmoothH1 ↥(N.subgroupOf D) A →* SmoothH1 ↥H A :=
  comapH1 (interEquiv N D hH).symm.toMonoidHom (fun _ _ => rfl)
    (isSmoothHom_of_continuous (continuous_interEquiv_symm N D hH))

/-- The inverse of the comparison map undoes it.  Both are computed by composing a cocycle with a
homomorphism of the groups, and the two homomorphisms are mutually inverse. -/
theorem comapInterH1Symm_comapInterH1 (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D)
    (z : SmoothH1 ↥H A) :
    comapInterH1Symm N D hH (comapInterH1 N D hH z) = z := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  rfl

/-- The comparison map undoes its inverse. -/
theorem comapInterH1_comapInterH1Symm (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D)
    (z : SmoothH1 ↥(N.subgroupOf D) A) :
    comapInterH1 N D hH (comapInterH1Symm N D hH z) = z := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  rfl

/-- **The comparison map is injective.** -/
theorem comapInterH1_injective (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D) :
    Function.Injective (comapInterH1 N D hH (M := A)) :=
  Function.LeftInverse.injective (comapInterH1Symm_comapInterH1 N D hH)

/-- **The comparison map is surjective.** -/
theorem comapInterH1_surjective (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D) :
    Function.Surjective (comapInterH1 N D hH (M := A)) :=
  Function.RightInverse.surjective (comapInterH1_comapInterH1Symm N D hH)

end Inter

/-! ### Localising a twisted Kummer class -/

section Kummer

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K F : IntermediateField k Ω}
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

include hj hιj hL hD htrivEL in
/-- **A twisted Kummer class dies under localisation exactly when its datum dies under the inclusion
of the units into the units of the compositum.**  Localisation is the comparison map applied to the
twisted class of the image datum, the comparison map is injective, and the twisted identification is
an isomorphism, so the three vanishings are the same statement. -/
theorem resSubH1_kummerTwistEquiv_eq_one_iff [IsCyclic M]
    (s : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    resSubH1 K.fixingSubgroup D
        (Additive.toMul (kummerTwistEquiv hK htriv htrivEK α hEp s)) = 1
      ↔ TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id s = 0 := by
  have h := resSubH1_kummerTwistEquiv_sup hK hL j hj hιj hD htriv htrivEK htrivEL α hEp s
  constructor
  · intro hz
    have h0 : MonoidHom.toAdditive (comapInterH1 K.fixingSubgroup D
        (mem_fixingSubgroup_sup_iff K F hD))
          (kummerTwistEquiv hL htriv htrivEL α hEp
            (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id s)) = 0 := by
      rw [← h]
      exact hz
    have h1 : comapInterH1 K.fixingSubgroup D (mem_fixingSubgroup_sup_iff K F hD)
        (Additive.toMul (kummerTwistEquiv hL htriv htrivEL α hEp
          (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id s))) = 1 := h0
    have h2 : Additive.toMul (kummerTwistEquiv hL htriv htrivEL α hEp
        (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id s)) = 1 := by
      refine comapInterH1_injective K.fixingSubgroup D
        (mem_fixingSubgroup_sup_iff K F hD) (A := E) ?_
      rw [h1, map_one]
    have h3 : kummerTwistEquiv hL htriv htrivEL α hEp
        (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id s) = 0 := h2
    exact (kummerTwistEquiv hL htriv htrivEL α hEp).injective (by rw [h3, map_zero])
  · intro hz
    rw [hz, map_zero] at h
    have h1 : MonoidHom.toAdditive (comapInterH1 K.fixingSubgroup D
        (mem_fixingSubgroup_sup_iff K F hD)) (0 : Additive (SmoothH1 ↥(K ⊔ F).fixingSubgroup E))
          = 0 := map_zero _
    rw [h1] at h
    exact h

include hj hιj hK hL hD htriv htrivEK htrivEL α hEp in
/-- **Localisation at a place is surjective as soon as the inclusion of the units into the units of
the compositum is surjective modulo the coefficients.**  A class at the place is a twisted Kummer
class of the compositum by the comparison isomorphism; a datum of that class comes from a datum of
the field, and the twisted class of the latter localises to the former. -/
theorem surjective_resSubH1_of_surjective_tensor [IsCyclic M]
    (hsurj : Function.Surjective (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap
      (LinearMap.id : Additive (M →* E) →ₗ[ℤ] Additive (M →* E)))) :
    Function.Surjective (resSubH1 K.fixingSubgroup D (M := E)) := by
  intro y
  obtain ⟨t, ht⟩ := (kummerTwistEquiv hL htriv htrivEL α hEp).surjective
    (Additive.ofMul (comapInterH1Symm K.fixingSubgroup D
      (mem_fixingSubgroup_sup_iff K F hD) y))
  obtain ⟨s, rfl⟩ := hsurj t
  refine ⟨Additive.toMul (kummerTwistEquiv hK htriv htrivEK α hEp s), ?_⟩
  have h := resSubH1_kummerTwistEquiv_sup hK hL j hj hιj hD htriv htrivEK htrivEL α hEp s
  rw [ht] at h
  have h1 : resSubH1 K.fixingSubgroup D
      (Additive.toMul (kummerTwistEquiv hK htriv htrivEK α hEp s))
      = comapInterH1 K.fixingSubgroup D (mem_fixingSubgroup_sup_iff K F hD)
        (comapInterH1Symm K.fixingSubgroup D (mem_fixingSubgroup_sup_iff K F hD) y) := h
  rw [h1, comapInterH1_comapInterH1Symm]

include hj hιj hL hD htrivEL in
/-- **What localisation at a place kills is killed by every homomorphism that kills the twisted
Kummer classes whose datum the inclusion of the units kills.**  Every class is twisted Kummer, and
for such a class the two conditions are the same. -/
theorem ker_resSubH1_le [IsCyclic M] {P : Type*} [CommGroup P]
    (ψ : SmoothH1 ↥K.fixingSubgroup E →* P)
    (hψ : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id t = 0 →
        ψ (Additive.toMul (kummerTwistEquiv hK htriv htrivEK α hEp t)) = 1) :
    (resSubH1 K.fixingSubgroup D (M := E)).ker ≤ ψ.ker := by
  intro z hz
  obtain ⟨s, hs⟩ := (kummerTwistEquiv hK htriv htrivEK α hEp).surjective (Additive.ofMul z)
  have hzs : z = Additive.toMul (kummerTwistEquiv hK htriv htrivEK α hEp s) := by
    rw [hs]
    rfl
  rw [MonoidHom.mem_ker, hzs]
  refine hψ s ?_
  rw [← resSubH1_kummerTwistEquiv_eq_one_iff hK hL j hj hιj hD htriv htrivEK htrivEL α hEp s]
  rw [← hzs]
  exact hz

end Kummer

end InverseGalois.CFT
