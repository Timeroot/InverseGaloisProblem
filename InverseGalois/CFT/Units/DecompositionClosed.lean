/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.InfiniteDecomposition

/-!
# A decomposition subgroup is closed

The Galois group of an arbitrary Galois extension of a number field is a profinite group for the
Krull topology, and it acts on the extension with open stabilisers: an element is algebraic, so the
automorphisms fixing it contain the automorphisms fixing a finite level.  **The decomposition
subgroup at a place is therefore closed**, being an intersection of conditions each of which is
tested by a continuous map into a discrete space.

For a prime of the integers the condition is membership: an automorphism fixes the prime exactly
when, for every integer, it carries the integer into the prime exactly when the integer was already
in it.  For an archimedean place it is a value: an automorphism fixes the place exactly when it
preserves the absolute value of every element.  In both cases the condition at a single element
cuts out the preimage of a set in a discrete space, hence a closed set, and the decomposition
subgroup is the intersection over all elements.

Closedness is what makes a decomposition subgroup the subgroup fixing a field, by the Galois
correspondence for infinite extensions; that field is the fixed field of the subgroup, and a local
condition at the place becomes a condition on the compositum with it.

## Main results

* `InverseGalois.CFT.isClosed_stabilizer_ideal`: **the decomposition subgroup at a prime of the
  integers of an arbitrary Galois extension is closed.**
* `InverseGalois.CFT.isClosed_stabilizer_infinitePlace`: **the decomposition subgroup at an
  archimedean place of an arbitrary Galois extension is closed.**
* `InverseGalois.CFT.isClosed_of_mem_decompositionSubgroups`: **every decomposition subgroup is
  closed.**
* `InverseGalois.CFT.fixingSubgroup_fixedField_of_mem_decompositionSubgroups`: **every
  decomposition subgroup is the subgroup fixing its own fixed field.**

## Tags

number field, infinite Galois theory, Krull topology, decomposition group, closed subgroup
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### The finite places -/

section Finite

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

omit [IsGalois k Ω] in
/-- An automorphism fixes an ideal exactly when it carries an integer into the ideal precisely when
the integer was already there. -/
theorem mem_stabilizer_ideal_iff (P : Ideal (𝓞 Ω)) (σ : Gal(Ω/k)) :
    σ ∈ stabilizer Gal(Ω/k) P ↔ ∀ b : 𝓞 Ω, σ • b ∈ P ↔ b ∈ P := by
  rw [mem_stabilizer_iff]
  constructor
  · intro h b
    calc σ • b ∈ P ↔ σ • b ∈ σ • P := by rw [h]
      _ ↔ b ∈ P := Ideal.smul_mem_pointwise_smul_iff
  · intro h
    refine Ideal.ext fun x => ?_
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hx := h (σ⁻¹ • x)
    rw [smul_inv_smul] at hx
    exact hx.symm

/-- **The decomposition subgroup at a prime of the integers of an arbitrary Galois extension is
closed.**  The action on the integers is continuous for the discrete topology, so the automorphisms
respecting the membership of a single integer form a closed set, and the decomposition subgroup is
the intersection of those sets. -/
theorem isClosed_stabilizer_ideal (P : Ideal (𝓞 Ω)) :
    IsClosed (stabilizer Gal(Ω/k) P : Set Gal(Ω/k)) := by
  letI : TopologicalSpace (𝓞 Ω) := ⊥
  haveI : DiscreteTopology (𝓞 Ω) := ⟨rfl⟩
  haveI := continuousSMul_ringOfIntegers k Ω
  have hcont : ∀ b : 𝓞 Ω, Continuous fun σ : Gal(Ω/k) => σ • b := fun b =>
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  have hset : (stabilizer Gal(Ω/k) P : Set Gal(Ω/k))
      = ⋂ b : 𝓞 Ω, {σ : Gal(Ω/k) | σ • b ∈ P ↔ b ∈ P} := by
    ext σ
    simpa only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq] using
      mem_stabilizer_ideal_iff P σ
  rw [hset]
  refine isClosed_iInter fun b => ?_
  by_cases hb : b ∈ P
  · have hEq : {σ : Gal(Ω/k) | σ • b ∈ P ↔ b ∈ P}
        = (fun σ : Gal(Ω/k) => σ • b) ⁻¹' (P : Set (𝓞 Ω)) := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, hb, iff_true]
    rw [hEq]
    exact (isClosed_discrete _).preimage (hcont b)
  · have hEq : {σ : Gal(Ω/k) | σ • b ∈ P ↔ b ∈ P}
        = (fun σ : Gal(Ω/k) => σ • b) ⁻¹' ((P : Set (𝓞 Ω))ᶜ) := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, hb,
        iff_false]
    rw [hEq]
    exact (isClosed_discrete _).preimage (hcont b)

end Finite

/-! ### The infinite places -/

section Infinite

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

omit [IsGalois k Ω] in
/-- An automorphism fixes an archimedean place exactly when it preserves the absolute value of
every element. -/
theorem mem_stabilizer_infinitePlace_iff (W : InfinitePlace Ω) (σ : Gal(Ω/k)) :
    σ ∈ stabilizer Gal(Ω/k) W ↔ ∀ x : Ω, W (σ • x) = W x := by
  rw [mem_stabilizer_iff]
  constructor
  · intro h x
    calc W (σ • x) = (σ • W) (σ • x) := by rw [h]
      _ = W x := congrArg (W : Ω → ℝ) (σ.symm_apply_apply x)
  · intro h
    refine InfinitePlace.ext _ _ fun x => ?_
    show W (σ.symm x) = W x
    calc W (σ.symm x) = W (σ • σ.symm x) := (h (σ.symm x)).symm
      _ = W x := congrArg (W : Ω → ℝ) (σ.apply_symm_apply x)

/-- **The decomposition subgroup at an archimedean place of an arbitrary Galois extension is
closed.**  The action on the extension is continuous for the discrete topology, so the
automorphisms preserving the absolute value of a single element form a closed set, and the
decomposition subgroup is the intersection of those sets. -/
theorem isClosed_stabilizer_infinitePlace (W : InfinitePlace Ω) :
    IsClosed (stabilizer Gal(Ω/k) W : Set Gal(Ω/k)) := by
  letI : TopologicalSpace Ω := ⊥
  haveI : DiscreteTopology Ω := ⟨rfl⟩
  haveI : ContinuousSMul Gal(Ω/k) Ω :=
    continuousSMul_iff_stabilizer_isOpen.2 fun x => stabilizer_isOpen_of_isIntegral x
  have hcont : ∀ x : Ω, Continuous fun σ : Gal(Ω/k) => σ • x := fun x =>
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  have hset : (stabilizer Gal(Ω/k) W : Set Gal(Ω/k))
      = ⋂ x : Ω, (fun σ : Gal(Ω/k) => σ • x) ⁻¹' {y : Ω | W y = W x} := by
    ext σ
    simpa only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq] using
      mem_stabilizer_infinitePlace_iff W σ
  rw [hset]
  exact isClosed_iInter fun x => (isClosed_discrete _).preimage (hcont x)

end Infinite

/-! ### Every decomposition subgroup fixes its fixed field -/

section Family

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- **Every decomposition subgroup of an arbitrary Galois extension of a number field is closed**,
at a finite place and at an infinite one alike. -/
theorem isClosed_of_mem_decompositionSubgroups {D : Subgroup Gal(Ω/k)}
    (hD : D ∈ decompositionSubgroups k Ω) : IsClosed (D : Set Gal(Ω/k)) := by
  rcases hD with ⟨P, _, _, rfl⟩ | ⟨W, rfl⟩
  · exact isClosed_stabilizer_ideal P
  · exact isClosed_stabilizer_infinitePlace W

/-- **Every decomposition subgroup is the subgroup fixing its own fixed field**, so a condition on
a decomposition subgroup is a condition on the compositum of a field with that fixed field. -/
theorem fixingSubgroup_fixedField_of_mem_decompositionSubgroups {D : Subgroup Gal(Ω/k)}
    (hD : D ∈ decompositionSubgroups k Ω) :
    (IntermediateField.fixedField D).fixingSubgroup = D :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨D, isClosed_of_mem_decompositionSubgroups hD⟩

end Family

end InverseGalois.CFT
