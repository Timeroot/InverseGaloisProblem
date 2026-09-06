/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.NumberTheory.SplitDensity

/-!
# Avoiding a whole family of larger fields at once

A Dirichlet series is subadditive along a covering of one set of primes by two others, and
iterating that bound along a finite index set covers a set of primes by a finite set together with
a whole family.  Comparing densities then bounds the density of the covered set by the sum of the
densities of the family.

Applied to the primes splitting completely in a Galois number field, this says that if the primes
splitting completely in a field are, apart from finitely many, always split in one of finitely many
larger fields, then the reciprocal of the degree of the smaller field is at most the sum of the
reciprocals of the degrees of the larger ones.  Whenever that fails there are infinitely many
primes splitting completely in the smaller field and in none of the larger ones.  This is what a
simultaneous non-residue condition at an arbitrary number of primes needs: the enlargement factor
of each larger field only has to exceed the number of conditions imposed.

## Main results

* `InverseGalois.NumberTheory.density_le_of_subset_biUnion`: the density of a set of primes covered
  by a finite set together with a finite family of others is at most the sum of their densities.
* `InverseGalois.NumberTheory.infinite_setOf_splitsCompletely_not_splitsCompletely_family`:
  **infinitely many primes split completely in a Galois number field and in none of a finite family
  of larger ones**, as soon as the reciprocals of the larger degrees do not add up to the
  reciprocal of the smaller one.

## Tags

Dirichlet density, splitting completely, Chebotarev, union bound, number field
-/

open Filter Topology

namespace InverseGalois.NumberTheory

/-! ### The union bound for a family of exceptional sets -/

section UnionBound

/-- The Dirichlet series of the empty set of primes vanishes. -/
theorem primeSum_empty {s : ℝ} : primeSum ∅ s = 0 := by
  rw [primeSum, tsum_empty]

/-- Dirichlet series are subadditive along a covering of one set by a finite set and a finite
family of others. -/
theorem primeSum_le_of_subset_biUnion {ι : Type*} {S : Set ℕ} {T : ι → Set ℕ} {s : ℝ} (hs : 1 < s)
    (I : Finset ι) : ∀ F : Set ℕ, S ⊆ F ∪ ⋃ i ∈ I, T i →
      primeSum S s ≤ primeSum F s + ∑ i ∈ I, primeSum (T i) s := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    intro F hsub
    rw [show (⋃ i ∈ (∅ : Finset ι), T i) = (∅ : Set ℕ) by simp] at hsub
    simpa [primeSum_empty] using primeSum_le_of_subset_union hsub hs
  | insert a I' ha ih =>
    intro F hsub
    rw [Finset.set_biUnion_insert, ← Set.union_assoc] at hsub
    have h1 := ih (F ∪ T a) hsub
    have h2 := primeSum_le_of_subset_union (S := F ∪ T a) (F := F) (T := T a) subset_rfl hs
    rw [Finset.sum_insert ha]
    linarith

/-- **The density of a set of primes covered by a finite set together with a finite family of
others is at most the sum of the densities of the family.** -/
theorem density_le_of_subset_biUnion {ι : Type*} {S F : Set ℕ} {T : ι → Set ℕ} (I : Finset ι)
    (hF : F.Finite) (hsub : S ⊆ F ∪ ⋃ i ∈ I, T i) {a : ℝ} {b : ι → ℝ}
    (hS : HasDirichletDensity S a) (hT : ∀ i ∈ I, HasDirichletDensity (T i) (b i)) :
    a ≤ ∑ i ∈ I, b i := by
  have hsum : Tendsto (fun s : ℝ =>
      (primeSum F s + ∑ i ∈ I, primeSum (T i) s) / Real.log (1 / (s - 1))) (𝓝[>] 1)
      (𝓝 (∑ i ∈ I, b i)) := by
    have h0 := (hasDirichletDensity_of_finite hF).add (tendsto_finset_sum I hT)
    rw [zero_add] at h0
    refine h0.congr fun s => ?_
    rw [add_div, Finset.sum_div]
  refine le_of_tendsto_of_tendsto hS hsum ?_
  filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL
  gcongr
  exact primeSum_le_of_subset_biUnion (Set.mem_Ioi.mp hs) I F hsub

end UnionBound

/-! ### Primes split in one field and in none of a family of others -/

section Family

/-- **Infinitely many primes split completely in a Galois number field and in none of a finite
family of larger ones**, as soon as the reciprocals of the larger degrees do not add up to the
reciprocal of the smaller one.  Were they finite, the primes splitting completely in the smaller
field would be covered by a finite set together with the sets of primes splitting completely in the
larger ones, and comparing densities would contradict that. -/
theorem infinite_setOf_splitsCompletely_not_splitsCompletely_family {ι : Type*} (I : Finset ι)
    (A : Type) [Field A] [NumberField A] [IsGalois ℚ A]
    (B : ι → Type) [∀ i, Field (B i)] [∀ i, NumberField (B i)] [∀ i, IsGalois ℚ (B i)]
    (hlt : ∑ i ∈ I, 1 / (Module.finrank ℚ (B i) : ℝ) < 1 / (Module.finrank ℚ A : ℝ)) :
    {p : ℕ | p.Prime ∧ SplitsCompletely A p ∧ ∀ i ∈ I, ¬ SplitsCompletely (B i) p}.Infinite := by
  classical
  intro hfin
  have hsub : splitSet A ⊆
      {p : ℕ | p.Prime ∧ SplitsCompletely A p ∧ ∀ i ∈ I, ¬ SplitsCompletely (B i) p} ∪
        ⋃ i ∈ I, splitSet (B i) := by
    rintro p ⟨hp, hsp⟩
    by_cases h : ∀ i ∈ I, ¬ SplitsCompletely (B i) p
    · exact Or.inl ⟨hp, hsp, h⟩
    · push_neg at h
      obtain ⟨i, hi, hbi⟩ := h
      exact Or.inr (Set.mem_biUnion hi ⟨hp, hbi⟩)
  have hle := density_le_of_subset_biUnion I hfin hsub (hasDirichletDensity_splitSet A)
    fun i _ => hasDirichletDensity_splitSet (B i)
  linarith

end Family

end InverseGalois.NumberTheory
