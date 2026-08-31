/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.DecompositionGalois

/-!
# The decomposition field of a prime

Let `K / k` be a Galois extension of number fields and let `w` be a prime of `K`.  The subfield of
`K` fixed by the decomposition group at `w` is the decomposition field at `w`.  An element of `K`
fixed by the decomposition group has its image in the completion at `w` fixed by that group as
well, and the elements of the completion so fixed are exactly the ones coming from the completion
of the base field at the prime below.  So the decomposition field embeds into the completion of the
base field, compatibly with the embedding of both into the completion of `K`.

That embedding is what turns the completion at the prime below into a field over which the
extension `K` becomes, after completing, a Galois extension with the *whole* Galois group of `K`
over the decomposition field, and not just a subgroup of it: the decomposition group is everything
once the base has been enlarged to the decomposition field.  This is the situation in which a
crossed product base changes to a crossed product for the local extension.

## Main definitions

* `InverseGalois.CFT.decompositionField`: **the subfield fixed by the decomposition group.**
* `InverseGalois.CFT.decompositionFieldHom`: **the embedding of the decomposition field into the
  completion of the base field at the prime below.**
* `InverseGalois.CFT.localDecompositionEquiv`: **the Galois group of the completions is the Galois
  group of the extension over the decomposition field.**

## Main results

* `InverseGalois.CFT.toAdicCompletion_mem_range`: an element of the decomposition field has its
  image in the completion coming from the completion of the base field.
* `InverseGalois.CFT.algebraMap_localDecompositionEquiv`: the identification of Galois groups is
  compatible with the embedding of the extension into its completion.

## Tags

number field, completion, decomposition group, decomposition field, local degree
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField

section DecompositionField

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The decomposition field at a prime**, the subfield of the extension fixed by the
decomposition group. -/
def decompositionField : IntermediateField k K :=
  IntermediateField.fixedField (stabilizer Gal(K/k) w)

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- An element of the extension lies in the decomposition field exactly when the decomposition
group fixes it. -/
theorem mem_decompositionField_iff {x : K} :
    x ∈ decompositionField k w ↔ ∀ σ : ↥(stabilizer Gal(K/k) w), (σ : Gal(K/k)) x = x := by
  simp [decompositionField, Subtype.forall]

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- The decomposition group fixes the decomposition field. -/
theorem eq_of_mem_decompositionField {x : K} (hx : x ∈ decompositionField k w)
    (σ : ↥(stabilizer Gal(K/k) w)) : (σ : Gal(K/k)) x = x :=
  (mem_decompositionField_iff k w).1 hx σ

variable (k) in
/-- **The Galois group of the extension over the decomposition field is the decomposition
group.** -/
noncomputable def decompositionFieldEquiv :
    ↥(stabilizer Gal(K/k) w) ≃* Gal(K/↥(decompositionField k w)) :=
  IntermediateField.subgroupEquivAlgEquiv (stabilizer Gal(K/k) w)

variable (k) in
omit [IsGalois k K] in
@[simp]
theorem decompositionFieldEquiv_apply (σ : ↥(stabilizer Gal(K/k) w)) (x : K) :
    decompositionFieldEquiv k w σ x = (σ : Gal(K/k)) x := rfl

/-! ### The decomposition field inside the completion of the base -/

variable (k) in
/-- **The image in the completion of an element of the decomposition field comes from the
completion of the base field**, being fixed by the decomposition group. -/
theorem toAdicCompletion_mem_range (x : ↥(decompositionField k w)) :
    toAdicCompletion w (x : K) ∈ Set.range (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k)
      (w.adicCompletion K)) := by
  rw [← mem_range_algebraMap_iff_forall_stabilizer_smul_eq]
  intro σ
  have h : σ • toAdicCompletion w (x : K) = toAdicCompletion w ((σ : Gal(K/k)) (x : K)) := by
    rw [stabilizer_smul_adicCompletion_def]
    exact adicCompletionAut_coe w (σ : Gal(K/k)) (mem_stabilizer_iff.mp σ.2) (x : K)
  rw [h, eq_of_mem_decompositionField k w x.2 σ]

variable (k) in
/-- The completion of the base field at a prime is isomorphic to its image in the completion of
the extension. -/
noncomputable def rangeEquivBaseCompletion :
    (primeUnder (𝓞 k) w).adicCompletion k ≃+*
      ↥(algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)).range :=
  RingEquiv.ofBijective (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k)
      (w.adicCompletion K)).rangeRestrict
    ⟨fun _ _ h => (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k)
        (w.adicCompletion K)).injective (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

variable (k) in
omit [IsGalois k K] in
@[simp]
theorem coe_rangeEquivBaseCompletion (c : (primeUnder (𝓞 k) w).adicCompletion k) :
    (rangeEquivBaseCompletion k w c : w.adicCompletion K)
      = algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) c := rfl

variable (k) in
/-- **The decomposition field embeds into the completion of the base field at the prime below.** -/
noncomputable def decompositionFieldHom :
    ↥(decompositionField k w) →+* (primeUnder (𝓞 k) w).adicCompletion k :=
  (rangeEquivBaseCompletion k w).symm.toRingHom.comp
    (((toAdicCompletion w).comp (algebraMap ↥(decompositionField k w) K)).codRestrict
      (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)).range
      (toAdicCompletion_mem_range k w))

variable (k) in
/-- **The embedding of the decomposition field into the completion of the base field is compatible
with the embedding of both into the completion of the extension.** -/
@[simp]
theorem algebraMap_decompositionFieldHom (x : ↥(decompositionField k w)) :
    algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
        (decompositionFieldHom k w x) = toAdicCompletion w (x : K) := by
  rw [← coe_rangeEquivBaseCompletion k w]
  exact congrArg Subtype.val ((rangeEquivBaseCompletion k w).apply_symm_apply _)

variable (k) in
/-- The completion of the base field at a prime is an algebra over the decomposition field. -/
noncomputable instance algebraDecompositionField :
    Algebra ↥(decompositionField k w) ((primeUnder (𝓞 k) w).adicCompletion k) :=
  (decompositionFieldHom k w).toAlgebra

variable (k) in
theorem algebraMap_decompositionField_eq (x : ↥(decompositionField k w)) :
    algebraMap ↥(decompositionField k w) ((primeUnder (𝓞 k) w).adicCompletion k) x
      = decompositionFieldHom k w x := rfl

variable (k) in
/-- The completion of the extension is an algebra over the completion of the base field in a way
compatible with the decomposition field. -/
instance isScalarTower_decompositionField :
    IsScalarTower ↥(decompositionField k w) ((primeUnder (𝓞 k) w).adicCompletion k)
      (w.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq fun x => (algebraMap_decompositionFieldHom k w x).symm

variable (k) in
/-- The algebra structure of the completion of the base field over the decomposition field extends
its algebra structure over the base field. -/
instance isScalarTower_base_decompositionField :
    IsScalarTower k ↥(decompositionField k w) ((primeUnder (𝓞 k) w).adicCompletion k) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    refine (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)).injective ?_
    rw [algebraMap_decompositionField_eq k w, algebraMap_decompositionFieldHom k w,
      ← IsScalarTower.algebraMap_apply k ((primeUnder (𝓞 k) w).adicCompletion k)
        (w.adicCompletion K)]
    show algebraMap k (w.adicCompletion K) c = toAdicCompletion w (algebraMap k K c)
    rw [IsScalarTower.algebraMap_apply k K (w.adicCompletion K)]
    rfl

/-! ### The Galois group of the completions -/

variable (k) in
/-- **The Galois group of the completion over the completion of the base is the Galois group of
the extension over the decomposition field.** -/
noncomputable def localDecompositionEquiv :
    (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) ≃*
      Gal(K/↥(decompositionField k w)) :=
  (decompositionEquiv k w).symm.trans (decompositionFieldEquiv k w)

variable (k) in
/-- **The identification of the Galois group of the completions with the Galois group over the
decomposition field is compatible with the embedding of the extension into its completion.** -/
theorem algebraMap_localDecompositionEquiv
    (τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
    (x : K) :
    τ (algebraMap K (w.adicCompletion K) x)
      = algebraMap K (w.adicCompletion K) (localDecompositionEquiv k w τ x) := by
  set σ := (decompositionEquiv k w).symm τ with hσ
  have hτ : τ = decompositionEquiv k w σ := by rw [hσ, MulEquiv.apply_symm_apply]
  show τ (toAdicCompletion w x) = toAdicCompletion w ((σ : Gal(K/k)) x)
  rw [hτ, decompositionEquiv_apply, stabilizer_smul_adicCompletion_def]
  exact adicCompletionAut_coe w (σ : Gal(K/k)) (mem_stabilizer_iff.mp σ.2) x

end DecompositionField

end InverseGalois.CFT
