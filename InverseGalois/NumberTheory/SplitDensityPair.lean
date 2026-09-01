/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.NumberTheory.SplitDensity

/-!
# Avoiding two larger fields at once

A Dirichlet series is subadditive along a covering of one set of primes by two others, and
iterating that bound covers a set of primes by a finite set together with two others.  Comparing
densities then bounds the density of the covered set by the sum of the two densities.

Applied to the primes splitting completely in a Galois number field, this says that if the primes
splitting completely in a field are, apart from finitely many, always split in one of two larger
fields, then the reciprocal of the degree of the smaller field is at most the sum of the
reciprocals of the degrees of the two larger ones.  Whenever that fails there are infinitely many
primes splitting completely in the smaller field and in neither of the larger two.  Two extensions
of degree three or more over the smaller field always make it fail, which is what a simultaneous
non-residue condition at two primes needs.

## Main results

* `InverseGalois.NumberTheory.density_le_of_subset_union₂`: the density of a set of primes covered
  by a finite set together with two others is at most the sum of their two densities.
* `InverseGalois.NumberTheory.infinite_setOf_splitsCompletely_not_splitsCompletely₂`: **infinitely
  many primes split completely in a Galois number field and in neither of two larger ones**, as
  soon as the reciprocals of the two larger degrees do not add up to the reciprocal of the smaller
  one.

## Tags

Dirichlet density, splitting completely, Chebotarev, union bound, number field
-/

open Filter Topology

namespace InverseGalois.NumberTheory

/-! ### The union bound for two exceptional sets -/

section UnionBound

/-- Dirichlet series are subadditive along a covering of one set by a finite set and two others. -/
theorem primeSum_le_of_subset_union₂ {S T₁ T₂ F : Set ℕ} (hsub : S ⊆ F ∪ (T₁ ∪ T₂)) {s : ℝ}
    (hs : 1 < s) : primeSum S s ≤ primeSum F s + primeSum T₁ s + primeSum T₂ s := by
  have h1 := primeSum_le_of_subset_union hsub hs
  have h2 := primeSum_le_of_subset_union (S := T₁ ∪ T₂) (F := T₁) (T := T₂) subset_rfl hs
  linarith

/-- **The density of a set of primes covered by a finite set together with two others is at most
the sum of their two densities.** -/
theorem density_le_of_subset_union₂ {S T₁ T₂ F : Set ℕ} (hF : F.Finite)
    (hsub : S ⊆ F ∪ (T₁ ∪ T₂)) {a b₁ b₂ : ℝ} (hS : HasDirichletDensity S a)
    (hT₁ : HasDirichletDensity T₁ b₁) (hT₂ : HasDirichletDensity T₂ b₂) : a ≤ b₁ + b₂ := by
  have hsum := ((hasDirichletDensity_of_finite hF).add hT₁).add hT₂
  rw [zero_add] at hsum
  refine le_of_tendsto_of_tendsto hS hsum ?_
  filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL
  rw [← add_div, ← add_div]
  gcongr
  exact primeSum_le_of_subset_union₂ hsub (Set.mem_Ioi.mp hs)

end UnionBound

/-! ### Primes split in one field and in neither of two others -/

section TwoFields

/-- **Infinitely many primes split completely in a Galois number field and in neither of two
larger ones**, as soon as the reciprocals of the two larger degrees do not add up to the
reciprocal of the smaller one.  Were they finite, the primes splitting completely in the smaller
field would be covered by a finite set together with the two sets of primes splitting completely
in the larger ones, and comparing densities would contradict that. -/
theorem infinite_setOf_splitsCompletely_not_splitsCompletely₂
    (A : Type*) [Field A] [NumberField A] [IsGalois ℚ A]
    (B₁ : Type*) [Field B₁] [NumberField B₁] [IsGalois ℚ B₁]
    (B₂ : Type*) [Field B₂] [NumberField B₂] [IsGalois ℚ B₂]
    (hlt : 1 / (Module.finrank ℚ B₁ : ℝ) + 1 / (Module.finrank ℚ B₂ : ℝ)
      < 1 / (Module.finrank ℚ A : ℝ)) :
    {p : ℕ | p.Prime ∧ SplitsCompletely A p ∧ ¬ SplitsCompletely B₁ p ∧
      ¬ SplitsCompletely B₂ p}.Infinite := by
  intro hfin
  have hsub : splitSet A ⊆
      {p : ℕ | p.Prime ∧ SplitsCompletely A p ∧ ¬ SplitsCompletely B₁ p ∧
        ¬ SplitsCompletely B₂ p} ∪ (splitSet B₁ ∪ splitSet B₂) := by
    rintro p ⟨hp, hsp⟩
    by_cases h₁ : SplitsCompletely B₁ p
    · exact Or.inr (Or.inl ⟨hp, h₁⟩)
    by_cases h₂ : SplitsCompletely B₂ p
    · exact Or.inr (Or.inr ⟨hp, h₂⟩)
    · exact Or.inl ⟨hp, hsp, h₁, h₂⟩
  have hle := density_le_of_subset_union₂ hfin hsub (hasDirichletDensity_splitSet A)
    (hasDirichletDensity_splitSet B₁) (hasDirichletDensity_splitSet B₂)
  linarith

end TwoFields

end InverseGalois.NumberTheory
