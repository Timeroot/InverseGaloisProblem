/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNTorsion
import InverseGalois.CFT.Units.InfiniteHilbert90

/-!
# The decomposition field of an infinite place

Let `K / k` be a Galois extension of number fields and let `w` be an infinite place of `K`.  The
subfield of `K` fixed by the decomposition group at `w` is the decomposition field at `w`.  An
element of `K` fixed by the decomposition group has its image in the completion at `w` fixed by
that group as well, and the elements of the completion so fixed are exactly the ones coming from
the completion of the base field at the place below.  So the decomposition field embeds into the
completion of the base field, compatibly with the embedding of both into the completion of `K`.

That embedding is what turns the completion of the base field into a field over which the extension
`K` becomes, after completing, a Galois extension with the *whole* Galois group of `K` over the
decomposition field, and not just a subgroup of it.  This is the situation in which a crossed
product base changes to a crossed product for the local extension.

## Main definitions

* `InverseGalois.CFT.infiniteDecompositionField`: **the subfield fixed by the decomposition group
  at an infinite place.**
* `InverseGalois.CFT.infiniteDecompositionFieldHom`: **the embedding of the decomposition field
  into the completion of the base field at the place below.**
* `InverseGalois.CFT.localInfiniteDecompositionEquiv`: **the automorphism group of the completion
  is the Galois group of the extension over the decomposition field.**

## Main results

* `InverseGalois.CFT.infiniteCoe_mem_range`: an element of the decomposition field has its image in
  the completion coming from the completion of the base field.
* `InverseGalois.CFT.algebraMap_localInfiniteDecompositionEquiv`: the identification of Galois
  groups is compatible with the embedding of the extension into its completion.

## Tags

number field, infinite place, completion, decomposition group, decomposition field
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open Module MulAction NumberField

section InfiniteDecompositionField

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : InfinitePlace K)

variable (k) in
/-- **The decomposition field at an infinite place**, the subfield of the extension fixed by the
decomposition group. -/
def infiniteDecompositionField : IntermediateField k K :=
  IntermediateField.fixedField (stabilizer Gal(K/k) w)

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- An element of the extension lies in the decomposition field exactly when the decomposition
group fixes it. -/
theorem mem_infiniteDecompositionField_iff {x : K} :
    x ∈ infiniteDecompositionField k w ↔ ∀ σ : ↥(stabilizer Gal(K/k) w), (σ : Gal(K/k)) x = x := by
  simp [infiniteDecompositionField, Subtype.forall]

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- The decomposition group fixes the decomposition field. -/
theorem eq_of_mem_infiniteDecompositionField {x : K} (hx : x ∈ infiniteDecompositionField k w)
    (σ : ↥(stabilizer Gal(K/k) w)) : (σ : Gal(K/k)) x = x :=
  (mem_infiniteDecompositionField_iff k w).1 hx σ

variable (k) in
/-- **The Galois group of the extension over the decomposition field is the decomposition
group.** -/
noncomputable def infiniteDecompositionFieldEquiv :
    ↥(stabilizer Gal(K/k) w) ≃* Gal(K/↥(infiniteDecompositionField k w)) :=
  IntermediateField.subgroupEquivAlgEquiv (stabilizer Gal(K/k) w)

variable (k) in
omit [IsGalois k K] in
@[simp]
theorem infiniteDecompositionFieldEquiv_apply (σ : ↥(stabilizer Gal(K/k) w)) (x : K) :
    infiniteDecompositionFieldEquiv k w σ x = (σ : Gal(K/k)) x := rfl

/-! ### The decomposition field inside the completion of the base -/

variable (k) in
/-- **The image in the completion of an element of the decomposition field comes from the
completion of the base field**, being fixed by the decomposition group. -/
theorem infiniteCoe_mem_range (x : ↥(infiniteDecompositionField k w)) :
    algebraMap K w.Completion (x : K)
      ∈ Set.range (algebraMap (w.comap (algebraMap k K)).Completion w.Completion) := by
  rw [← mem_range_algebraMap_iff_forall_stabilizer_smul_eq_infinite]
  intro σ
  have h : σ • algebraMap K w.Completion (x : K)
      = algebraMap K w.Completion ((σ : Gal(K/k)) (x : K)) := smul_infiniteCoe w σ (x : K)
  rw [h, eq_of_mem_infiniteDecompositionField k w x.2 σ]

variable (k) in
/-- The completion of the base field at an infinite place is isomorphic to its image in the
completion of the extension. -/
noncomputable def rangeEquivBaseInfiniteCompletion :
    (w.comap (algebraMap k K)).Completion ≃+*
      ↥(algebraMap (w.comap (algebraMap k K)).Completion w.Completion).range :=
  RingEquiv.ofBijective
    (algebraMap (w.comap (algebraMap k K)).Completion w.Completion).rangeRestrict
    ⟨fun _ _ h => (algebraMap (w.comap (algebraMap k K)).Completion w.Completion).injective
        (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
@[simp]
theorem coe_rangeEquivBaseInfiniteCompletion (c : (w.comap (algebraMap k K)).Completion) :
    (rangeEquivBaseInfiniteCompletion k w c : w.Completion)
      = algebraMap (w.comap (algebraMap k K)).Completion w.Completion c := rfl

variable (k) in
/-- **The decomposition field embeds into the completion of the base field at the place
below.** -/
noncomputable def infiniteDecompositionFieldHom :
    ↥(infiniteDecompositionField k w) →+* (w.comap (algebraMap k K)).Completion :=
  (rangeEquivBaseInfiniteCompletion k w).symm.toRingHom.comp
    (((algebraMap K w.Completion).comp
        (algebraMap ↥(infiniteDecompositionField k w) K)).codRestrict
      (algebraMap (w.comap (algebraMap k K)).Completion w.Completion).range
      (infiniteCoe_mem_range k w))

variable (k) in
/-- **The embedding of the decomposition field into the completion of the base field is compatible
with the embedding of both into the completion of the extension.** -/
@[simp]
theorem algebraMap_infiniteDecompositionFieldHom (x : ↥(infiniteDecompositionField k w)) :
    algebraMap (w.comap (algebraMap k K)).Completion w.Completion
        (infiniteDecompositionFieldHom k w x) = algebraMap K w.Completion (x : K) := by
  rw [← coe_rangeEquivBaseInfiniteCompletion k w]
  exact congrArg Subtype.val ((rangeEquivBaseInfiniteCompletion k w).apply_symm_apply _)

variable (k) in
/-- The completion of the base field at an infinite place is an algebra over the decomposition
field. -/
noncomputable instance algebraInfiniteDecompositionField :
    Algebra ↥(infiniteDecompositionField k w) (w.comap (algebraMap k K)).Completion :=
  (infiniteDecompositionFieldHom k w).toAlgebra

variable (k) in
theorem algebraMap_infiniteDecompositionField_eq (x : ↥(infiniteDecompositionField k w)) :
    algebraMap ↥(infiniteDecompositionField k w) (w.comap (algebraMap k K)).Completion x
      = infiniteDecompositionFieldHom k w x := rfl

variable (k) in
/-- The completion of the extension is an algebra over the completion of the base field in a way
compatible with the decomposition field. -/
instance isScalarTower_infiniteDecompositionField :
    IsScalarTower ↥(infiniteDecompositionField k w) (w.comap (algebraMap k K)).Completion
      w.Completion :=
  IsScalarTower.of_algebraMap_eq fun x => (algebraMap_infiniteDecompositionFieldHom k w x).symm

variable (k) in
/-- The algebra structure of the completion of the base field over the decomposition field extends
its algebra structure over the base field. -/
instance isScalarTower_base_infiniteDecompositionField :
    IsScalarTower k ↥(infiniteDecompositionField k w) (w.comap (algebraMap k K)).Completion :=
  IsScalarTower.of_algebraMap_eq fun c => by
    refine (algebraMap (w.comap (algebraMap k K)).Completion w.Completion).injective ?_
    rw [algebraMap_infiniteDecompositionField_eq k w, algebraMap_infiniteDecompositionFieldHom k w,
      ← IsScalarTower.algebraMap_apply k (w.comap (algebraMap k K)).Completion w.Completion]
    show algebraMap k w.Completion c = algebraMap K w.Completion (algebraMap k K c)
    rw [IsScalarTower.algebraMap_apply k K w.Completion]

/-! ### The automorphism group of the completion -/

variable (k) in
/-- **The automorphism group of the completion over the completion of the base is the Galois group
of the extension over the decomposition field.** -/
noncomputable def localInfiniteDecompositionEquiv :
    (w.Completion ≃ₐ[(w.comap (algebraMap k K)).Completion] w.Completion) ≃*
      Gal(K/↥(infiniteDecompositionField k w)) :=
  (stabilizerAlgEquivInfinite k w).symm.trans (infiniteDecompositionFieldEquiv k w)

variable (k) in
/-- **The identification of the automorphism group of the completion with the Galois group over the
decomposition field is compatible with the embedding of the extension into its completion.** -/
theorem algebraMap_localInfiniteDecompositionEquiv
    (τ : w.Completion ≃ₐ[(w.comap (algebraMap k K)).Completion] w.Completion) (x : K) :
    τ (algebraMap K w.Completion x)
      = algebraMap K w.Completion (localInfiniteDecompositionEquiv k w τ x) := by
  set σ := (stabilizerAlgEquivInfinite k w).symm τ with hσ
  have hτ : τ = stabilizerAlgEquivInfinite k w σ := by rw [hσ, MulEquiv.apply_symm_apply]
  show τ (algebraMap K w.Completion x) = algebraMap K w.Completion ((σ : Gal(K/k)) x)
  rw [hτ, stabilizerAlgEquivInfinite_apply]
  exact smul_infiniteCoe w σ x

end InfiniteDecompositionField

end InverseGalois.CFT
