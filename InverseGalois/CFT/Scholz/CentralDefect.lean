/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.BlockDefect

/-!
# The obstruction of a prime, read on the central part of a Frobenius

Over a cover realising a group with a central subgroup, the subfields cut out by the subgroups of
that central subgroup all have the same Galois closure, and a prime of residue degree one in the
subfield cut out by the whole central subgroup admits, above each prime of the cover, a
factorisation of an arithmetic Frobenius into an inertia part and a central part.  The central part
is what decides the obstruction of the prime in every one of those subfields at once: the prime has
residue degree one in the subfield cut out by a subgroup exactly when the central part lies in that
subgroup together with the central part of the inertia group.

That turns a question about a whole tower of fields into a membership question about a single
element of the central subgroup, which is how the dyadic climb keeps track of the obstructions of
its blocks while it cuts the central subgroup down one hyperplane at a time.

## Main results

* `InverseGalois.CFT.mem_sup_iff_mem_inf_sup`: **membership in a join with a subgroup of a central
  subgroup only depends on the central part of a factorisation.**
* `InverseGalois.CFT.exists_mul_eq_of_isSplitInertiaAt`: **a prime of residue degree one in the
  subfield cut out by a subgroup factors an arithmetic Frobenius above it into an inertia part and a
  part in that subgroup.**
* `InverseGalois.CFT.canonicalDefect_cutField_eq_zero_iff`: **the obstruction of a prime in the
  subfield cut out by a subgroup of a central subgroup vanishes exactly when the central part of an
  arithmetic Frobenius above it lies in that subgroup together with the central part of the inertia
  group.**
* `InverseGalois.CFT.blockDefect_eq_of_forall_eq_zero_iff`: two fields whose primes carry the same
  obstruction over a block carry the same obstruction of the block.

## Tags

Scholz–Reichardt, Scholz obstruction, inertia subgroup, Frobenius, centre, cut field
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Factoring off the central part -/

section Group

variable {G : Type*} [Group G] {J Z U Y : Subgroup G}

/-- An element of a join with a normal subgroup factors through that subgroup. -/
theorem exists_mul_eq_of_mem_sup [Y.Normal] {x : G} (hx : x ∈ J ⊔ Y) :
    ∃ j ∈ J, ∃ y ∈ Y, x = j * y := by
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
  obtain ⟨j, hj, y, hy, hjy⟩ := hx
  exact ⟨j, hj, y, hy, (show j * y = x from hjy).symm⟩

/-- **Membership in a join with a subgroup of a central subgroup only depends on the central part of
a factorisation.**  Two factorisations of the same element differ by an element of the group joined
in, and that difference is central, so it lies in the central part of that group. -/
theorem mem_sup_iff_mem_inf_sup [U.Normal] (hUZ : U ≤ Z) {x j θ : G} (hj : j ∈ J) (hθ : θ ∈ Z)
    (hx : x = j * θ) : x ∈ J ⊔ U ↔ θ ∈ J ⊓ Z ⊔ U := by
  constructor
  · intro hxJU
    obtain ⟨j', hj', u, hu, hju⟩ := exists_mul_eq_of_mem_sup hxJU
    have heq : j * θ = j' * u := by rw [← hx]; exact hju
    have hθk : θ = j⁻¹ * j' * u := by rw [mul_assoc, ← heq]; group
    have hkJ : j⁻¹ * j' ∈ J := J.mul_mem (J.inv_mem hj) hj'
    have hkZ : j⁻¹ * j' ∈ Z := by
      have hk : j⁻¹ * j' = θ * u⁻¹ := by rw [hθk]; group
      rw [hk]
      exact Z.mul_mem hθ (Z.inv_mem (hUZ hu))
    rw [hθk]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hkJ, hkZ⟩))
      (Subgroup.mem_sup_right hu)
  · intro hθmem
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj)
      (SetLike.le_def.mp (sup_le_sup_right inf_le_left U) hθmem)

end Group

/-! ### The obstruction of a prime in a cut subfield -/

section Field

variable {T : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥T] [IsGalois ℚ ↥T]
  {G : Type*} [Group G] {q : ℕ}

/-- **A prime of residue degree one in the subfield cut out by a subgroup factors an arithmetic
Frobenius above it into an inertia part and a part in that subgroup.** -/
theorem exists_mul_eq_of_isSplitInertiaAt (Ψ : Gal(↥T/ℚ) ≃* G) (Y : Subgroup G) [Y.Normal]
    (hq : q.Prime) (P : Ideal (𝓞 ↥T)) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})]
    {σ : Gal(↥T/ℚ)} (hσ : IsArithFrobAt ℤ σ P)
    (h : IsSplitInertiaAt ↥(cutField ((QuotientGroup.mk' Y).comp Ψ.toMonoidHom)) q) :
    ∃ j ∈ (Ideal.inertia Gal(↥T/ℚ) P).map Ψ.toMonoidHom, ∃ y ∈ Y, Ψ σ = j * y :=
  exists_mul_eq_of_mem_sup ((isSplitInertiaAt_cutField_mk'_iff Ψ Y hq P hσ).mp h)

/-- **The obstruction of a prime in the subfield cut out by a subgroup of a central subgroup
vanishes exactly when the central part of an arithmetic Frobenius above it lies in that subgroup
together with the central part of the inertia group.** -/
theorem canonicalDefect_cutField_eq_zero_iff (Ψ : Gal(↥T/ℚ) ≃* G) {Z U : Subgroup G} [U.Normal]
    (hUZ : U ≤ Z) (hq : q.Prime) (P : Ideal (𝓞 ↥T)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] {σ : Gal(↥T/ℚ)} (hσ : IsArithFrobAt ℤ σ P) {j θ : G}
    (hj : j ∈ (Ideal.inertia Gal(↥T/ℚ) P).map Ψ.toMonoidHom) (hθ : θ ∈ Z) (hx : Ψ σ = j * θ) :
    canonicalDefect ↥(cutField ((QuotientGroup.mk' U).comp Ψ.toMonoidHom)) q = 0
      ↔ θ ∈ (Ideal.inertia Gal(↥T/ℚ) P).map Ψ.toMonoidHom ⊓ Z ⊔ U := by
  rw [canonicalDefect_eq_zero_iff, isSplitInertiaAt_cutField_mk'_iff Ψ U hq P hσ]
  exact mem_sup_iff_mem_inf_sup hUZ hj hθ hx

end Field

/-! ### Comparing obstructions -/

section Compare

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] {q : ℕ}

/-- Two fields in which a prime has residue degree one at the same time give it the same
obstruction. -/
theorem canonicalDefect_congr (h : IsSplitInertiaAt K q ↔ IsSplitInertiaAt K' q) :
    canonicalDefect K q = canonicalDefect K' q := by
  by_cases h1 : IsSplitInertiaAt K q
  · rw [canonicalDefect_eq_zero h1, canonicalDefect_eq_zero (h.mp h1)]
  · rw [canonicalDefect_eq_one h1, canonicalDefect_eq_one fun hc => h1 (h.mpr hc)]

/-- Two fields giving a prime a vanishing obstruction at the same time give it the same
obstruction. -/
theorem canonicalDefect_eq_of_eq_zero_iff
    (h : canonicalDefect K q = 0 ↔ canonicalDefect K' q = 0) :
    canonicalDefect K q = canonicalDefect K' q :=
  canonicalDefect_congr (by
    rw [← canonicalDefect_eq_zero_iff, ← canonicalDefect_eq_zero_iff]
    exact h)

/-- Two fields whose primes carry the same obstruction over a block carry the same obstruction of
the block. -/
theorem blockDefect_eq_of_forall_eq_zero_iff {B : Finset ℕ}
    (h : ∀ p ∈ B, canonicalDefect K p = 0 ↔ canonicalDefect K' p = 0) :
    blockDefect K B = blockDefect K' B :=
  Finset.sum_congr rfl fun p hp => canonicalDefect_eq_of_eq_zero_iff (h p hp)

end Compare

end InverseGalois.CFT
