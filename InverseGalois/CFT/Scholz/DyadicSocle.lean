/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.DyadicRadical
import InverseGalois.CFT.Scholz.ResidueSpan
import InverseGalois.CFT.SqrtFrattini

/-!
# The exponent vectors already radical at the prime two

At the prime two the exponent vectors whose radicand is already a square in the constraint field of
the auxiliary primes are not all zero, and the residue correction is available only for defects
orthogonal to them.  What controls those vectors is the multiquadratic part of the field being
corrected: a square root of a product of distinct primes congruent to one modulo four lying in the
constraint field lies in the solution, because the cyclotomic layer of the constraint field is
ramified only at two; and it lies in the field below the solution, because the automorphisms fixing
that field lie in the Frattini subgroup, which fixes every square root of a rational number.

So the exponent vectors in question are those whose radicand is a square in the field below, and if
those are spanned by the indicator vectors of a family of blocks of ramified primes then a defect
summing to zero over each block is orthogonal to all of them.

## Main definitions

* `InverseGalois.CFT.blockVector`: the indicator vector of a set of primes.
* `InverseGalois.CFT.blockSpan`: the span of the indicator vectors of a family of blocks.

## Main results

* `InverseGalois.CFT.sum_mul_eq_zero_of_mem_blockSpan`: a vector summing to zero over each block is
  orthogonal to the span of the block indicators.
* `InverseGalois.CFT.sum_mul_eq_zero_of_sq_mem_auxConstraintField`: **the orthogonality condition of
  the residue correction at the prime two, for a field whose square roots of products of ramified
  primes are accounted for by a family of blocks.**

## Tags

Scholz–Reichardt, square root, socle, Frattini subgroup, orthogonality
-/

open Finset NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {S : Finset ℕ}

/-! ### Blocks of primes and their span -/

/-- The indicator vector of a set of primes, read on a fixed finite set of primes. -/
def blockVector (S B : Finset ℕ) : {p // p ∈ S} → ZMod 2 := fun p => if (p : ℕ) ∈ B then 1 else 0

/-- The span of the indicator vectors of a family of blocks of primes. -/
def blockSpan (S : Finset ℕ) {ι : Type*} (block : ι → Finset ℕ) :
    Submodule (ZMod 2) ({p // p ∈ S} → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun i => blockVector S (block i))

/-- **A vector summing to zero over each block is orthogonal to the span of the block
indicators.**  Orthogonality to a fixed vector is a linear condition, so it suffices to check it on
the spanning family. -/
theorem sum_mul_eq_zero_of_mem_blockSpan {ι : Type*} {block : ι → Finset ℕ}
    {t : {p // p ∈ S} → ZMod 2}
    (ht : ∀ i, ∑ p : {p // p ∈ S}, t p * blockVector S (block i) p = 0)
    {a : {p // p ∈ S} → ZMod 2} (ha : a ∈ blockSpan S block) :
    ∑ p : {p // p ∈ S}, t p * a p = 0 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ht i
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  | smul c x _ hx =>
    have hterm : ∀ p : {p // p ∈ S}, t p * (c • x) p = c * (t p * x p) := by
      intro p
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun p _ => hterm p, ← Finset.mul_sum, hx, mul_zero]

/-! ### The radicand of an exponent vector at the prime two -/

/-- The radicand of an exponent vector over primes congruent to one modulo four is itself congruent
to one modulo four, being a product of such primes. -/
theorem residueRadicand_mod_four (hS4 : ∀ p ∈ S, p % 4 = 1) (a : {p // p ∈ S} → ZMod 2) :
    residueRadicand S a % 4 = 1 := by
  have key : ∀ i : {p // p ∈ S}, (i : ℕ) ^ (a i).val % 4 = 1 := by
    rintro ⟨p, hp⟩
    rcases eq_zero_or_one_zmod_two (a ⟨p, hp⟩) with h | h <;> rw [h]
    · simp
    · rw [show ((1 : ZMod 2)).val = 1 from rfl, pow_one]
      exact hS4 p hp
  refine Finset.prod_induction _ (fun n => n % 4 = 1) (fun x y hx hy => ?_) rfl fun i _ => key i
  have hx' : x % 4 = 1 := hx
  have hy' : y % 4 = 1 := hy
  show x * y % 4 = 1
  rw [Nat.mul_mod, hx', hy']

/-! ### The orthogonality condition at the prime two -/

/-- **The orthogonality condition of the residue correction at the prime two.**  A square root of
the radicand lies in the constraint field, hence in the solution because the cyclotomic layer is
ramified only at two, hence in the field below because the automorphisms fixing that field lie in
the Frattini subgroup; so the exponent vector is accounted for by the blocks, and a defect summing
to zero over each block is orthogonal to it. -/
theorem sum_mul_eq_zero_of_sq_mem_auxConstraintField {ι : Type*} {block : ι → Finset ℕ}
    {t : {p // p ∈ S} → ZMod 2} (A L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A]
    [IsGalois ℚ ↥A] [NumberField ↥L] [IsGalois ℚ ↥L] (hAL : A ≤ L)
    (hfr : (galRestrictLE hAL).ker ≤ frattini Gal(↥L/ℚ)) (h2L : 2 ∉ ramifiedSet ↥L)
    (hS4 : ∀ p ∈ S, p % 4 = 1)
    (hspan : ∀ b : {p // p ∈ S} → ZMod 2,
      (∃ u ∈ A, u ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) ((residueRadicand S b : ℕ) : ℚ)) →
        b ∈ blockSpan S block)
    (ht : ∀ i, ∑ p : {p // p ∈ S}, t p * blockVector S (block i) p = 0)
    {k : ℕ} [NeZero ((2 : ℕ) ^ k)] {a : {p // p ∈ S} → ZMod 2}
    (ha : ∃ u ∈ auxConstraintField L 2 k,
      u ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) ((residueRadicand S a : ℕ) : ℚ)) :
    ∑ p : {p // p ∈ S}, t p * a p = 0 := by
  obtain ⟨u, huC, hu⟩ := ha
  have hmod : residueRadicand S a % 4 = 1 := residueRadicand_mod_four hS4 a
  have hint : ((residueRadicand S a : ℕ) : ℤ) % 4 = 1 := by omega
  have hcast : u ^ 2 = ((((residueRadicand S a : ℕ) : ℤ)) : AlgebraicClosure ℚ) := by
    rw [hu, map_natCast]
    push_cast
    ring
  have huL : u ∈ L := mem_of_sq_eq_intCast_auxConstraintField L h2L hint huC hcast
  have huA : u ∈ A := mem_of_sq_eq_of_ker_le_frattini hAL hfr huL hu
  exact sum_mul_eq_zero_of_mem_blockSpan ht (hspan a ⟨u, huA, hu⟩)

end InverseGalois.CFT
