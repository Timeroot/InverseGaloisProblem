/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerTower

/-!
# Localising a Kummer class at a place

A place of a number field is a decomposition subgroup of the Galois group of the base, and
localising a class of the first cohomology at that place is restricting it to that subgroup.  The
classes being localised are those of the subgroup fixing a normal subextension, so what has to be
restricted is the part of that subgroup lying inside the decomposition subgroup — and **that part
is the subgroup fixing the compositum of the subextension with the fixed field of the place.**

Half of the identification is elementary once it is said correctly: the part of a subgroup lying
inside another one and the intersection of the two have the same elements when both are read in the
big group, and each carries the topology inherited from the big group, so they are the same
topological group and induce the same map in the first cohomology.  The other half is arithmetic:
the subgroup fixing a compositum is the intersection of the two subgroups fixing the factors, and a
closed subgroup is the subgroup fixing its own fixed field.

Putting the two together, **localising a Kummer class at a place is including the units of the
field into the units of the compositum**, and the same holds for the twisted identification which
carries the coefficients of a lifting problem.  The fixed field of a decomposition subgroup is an
infinite extension of the base, so all of this is available only because the Kummer tower asks
nothing of the size of the intermediate field.

## Main definitions

* `InverseGalois.CFT.interEquiv`: the part of a subgroup lying inside another one, read as their
  intersection.
* `InverseGalois.CFT.comapInterH1`: the map it induces in the first cohomology.

## Main results

* `InverseGalois.CFT.resSubH1_eq_comapInterH1`: **localisation at a subgroup is restriction to the
  intersection.**
* `InverseGalois.CFT.fixingSubgroup_fixedField_of_isClosed`: a closed subgroup fixes exactly its
  own fixed field.
* `InverseGalois.CFT.mem_fixingSubgroup_sup_iff`: the subgroup fixing a compositum.
* `InverseGalois.CFT.resSubH1_kummerSubHom_sup`: **the localisation of a Kummer class is the Kummer
  class of the same unit read in the compositum.**
* `InverseGalois.CFT.resSubH1_kummerTwistEquiv_sup`: **the same for the twisted identification**,
  which is what a local condition on an obstruction is read against.

## Tags

Kummer theory, Galois cohomology, decomposition group, localisation, compositum, place
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IntermediateField groupCohomology TensorProduct

/-! ### The part of a subgroup inside another one is the intersection -/

section Inter

variable {G : Type*} [Group G] [TopologicalSpace G] (N D : Subgroup G) {H : Subgroup G}

/-- **The part of a subgroup lying inside another one, read as their intersection.**  An element of
either is an element of the big group lying in both subgroups, and nothing else is being said. -/
def interEquiv (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D) : ↥(N.subgroupOf D) ≃* ↥H where
  toFun y := ⟨((y : ↥D) : G), (hH _).2 ⟨Subgroup.mem_subgroupOf.1 y.2, (y : ↥D).2⟩⟩
  invFun z := ⟨⟨(z : G), ((hH _).1 z.2).2⟩, Subgroup.mem_subgroupOf.2 ((hH _).1 z.2).1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [TopologicalSpace G] in
/-- Reading the part of a subgroup inside another one as the intersection does not change the
underlying element of the big group. -/
theorem coe_interEquiv (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D) (y : ↥(N.subgroupOf D)) :
    ((interEquiv N D hH y : ↥H) : G) = ((y : ↥D) : G) := rfl

/-- Both sides carry the topology inherited from the big group, so the identification is
continuous. -/
theorem continuous_interEquiv (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D) :
    Continuous (interEquiv N D hH) := by
  have h : Continuous fun y : ↥(N.subgroupOf D) => ((y : ↥D) : G) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact continuous_induced_rng.2 h

/-- So is the identification the other way. -/
theorem continuous_interEquiv_symm (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D) :
    Continuous (interEquiv N D hH).symm :=
  continuous_induced_rng.2 (continuous_induced_rng.2 continuous_subtype_val)

/-- The identification is a smooth homomorphism, so it carries continuous cochains to continuous
cochains. -/
theorem isSmoothHom_interEquiv (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D) :
    IsSmoothHom (interEquiv N D hH).toMonoidHom :=
  isSmoothHom_of_continuous (continuous_interEquiv N D hH)

variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- **The first cohomology of the intersection, read on the part of one subgroup inside the
other.** -/
def comapInterH1 (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D) :
    SmoothH1 ↥H M →* SmoothH1 ↥(N.subgroupOf D) M :=
  comapH1 (interEquiv N D hH).toMonoidHom (fun _ _ => rfl) (isSmoothHom_interEquiv N D hH)

/-- **Localising a class at a subgroup is restricting it to the intersection.**  Both sides
substitute the same element of the big group into the cocycle, so the two cochains agree before any
class is taken. -/
theorem resSubH1_eq_comapInterH1 (hH : ∀ g : G, g ∈ H ↔ g ∈ N ∧ g ∈ D) (hle : H ≤ N)
    (z : SmoothH1 ↥N M) :
    resSubH1 N D z = comapInterH1 N D hH (resInclH1 hle z) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  rfl

end Inter

/-! ### The subgroup fixing a compositum -/

section Field

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- **A closed subgroup is the subgroup fixing its own fixed field**, which is the infinite Galois
correspondence.  A decomposition subgroup is closed, so it is the subgroup fixing a field. -/
theorem fixingSubgroup_fixedField_of_isClosed {D : Subgroup Gal(Ω/k)}
    (hD : IsClosed (D : Set Gal(Ω/k))) :
    (IntermediateField.fixedField D).fixingSubgroup = D :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨D, hD⟩

omit [IsGalois k Ω] in
/-- **An automorphism fixes a compositum exactly when it fixes both factors.** -/
theorem mem_fixingSubgroup_sup_iff (K F : IntermediateField k Ω) {D : Subgroup Gal(Ω/k)}
    (hD : F.fixingSubgroup = D) (g : Gal(Ω/k)) :
    g ∈ (K ⊔ F).fixingSubgroup ↔ g ∈ K.fixingSubgroup ∧ g ∈ D := by
  rw [IntermediateField.fixingSubgroup_sup, ← hD, Subgroup.mem_inf]

omit [IsGalois k Ω] in
/-- An automorphism fixing a compositum fixes each of its factors. -/
theorem fixingSubgroup_sup_le (K F : IntermediateField k Ω) :
    (K ⊔ F).fixingSubgroup ≤ K.fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone le_sup_left

end Field

/-! ### The localisation of a Kummer class -/

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

include hj hιj in
/-- **The localisation of a Kummer class at a place is the Kummer class of the same unit read in
the compositum of the field with the fixed field of the place.** -/
theorem resSubH1_kummerSubHom_sup (a : (↥K)ˣ) :
    resSubH1 K.fixingSubgroup D (kummerSubHom hK htriv a)
      = comapInterH1 K.fixingSubgroup D (mem_fixingSubgroup_sup_iff K F hD)
        (kummerSubHom hL htriv (j a)) := by
  rw [resSubH1_eq_comapInterH1 K.fixingSubgroup D (mem_fixingSubgroup_sup_iff K F hD)
    (fixingSubgroup_sup_le K F), resInclH1_kummerSubHom hK hL j hj hιj
    (fixingSubgroup_sup_le K F) htriv]

variable {J : Type*} [Fintype J] [DecidableEq J] (α : E ≃* (J → M)) (hEp : ∀ e : E, e ^ p = 1)

include hj hιj in
/-- **The twisted Kummer identification is compatible with localisation at a place**: through it,
localising a class is including the units of the field into the units of the compositum of the
field with the fixed field of the place. -/
theorem resSubH1_kummerTwistEquiv_sup [IsCyclic M]
    (z : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (resSubH1 K.fixingSubgroup D)
        (kummerTwistEquiv hK htriv htrivEK α hEp z)
      = MonoidHom.toAdditive (comapInterH1 K.fixingSubgroup D
          (mem_fixingSubgroup_sup_iff K F hD))
        (kummerTwistEquiv hL htriv htrivEL α hEp
          (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id z)) := by
  rw [← resInclH1_kummerTwistEquiv hK hL j hj hιj (fixingSubgroup_sup_le K F) htriv htrivEK
    htrivEL α hEp z]
  exact congrArg Additive.ofMul
    (resSubH1_eq_comapInterH1 _ _ (mem_fixingSubgroup_sup_iff K F hD)
      (fixingSubgroup_sup_le K F) _)

end Kummer

end InverseGalois.CFT
