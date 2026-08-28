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

Which exponent vectors those are is an invariant of the field that survives the whole
Scholz–Reichardt climb: enlarging the field by a solution of a Frattini embedding problem creates no
new square root of a rational number, so a family of blocks accounting for the square roots of one
field accounts for those of every such enlargement.  At the foot of the climb the condition costs
nothing, the primes involved in a radicand with a square root in the field being ramified there: a
family containing the singleton of every ramified prime accounts for everything.

## Main definitions

* `InverseGalois.CFT.blockVector`: the indicator vector of a set of primes.
* `InverseGalois.CFT.blockSpan`: the span of the indicator vectors of a family of blocks.
* `InverseGalois.CFT.IsBlockSpanned`: a field whose square roots of squarefree products of primes
  are accounted for by a family of blocks.

## Main results

* `InverseGalois.CFT.sum_mul_eq_zero_of_mem_blockSpan`: a vector summing to zero over each block is
  orthogonal to the span of the block indicators.
* `InverseGalois.CFT.sum_mul_eq_zero_of_sq_mem_auxConstraintField`: **the orthogonality condition of
  the residue correction at the prime two, for a field whose square roots of products of ramified
  primes are accounted for by a family of blocks.**
* `InverseGalois.CFT.mem_ramifiedSet_of_sq_eq_residueRadicand`: **a prime involved in the radicand
  of an exponent vector ramifies in every field containing a square root of that radicand.**
* `InverseGalois.CFT.IsBlockSpanned.of_le_of_ker_le_frattini`: **a family of blocks accounting for
  the square roots of a field accounts for those of any Frattini extension of it.**
* `InverseGalois.CFT.isBlockSpanned_of_singleton_mem_of_mem_ramifiedSet`: **a family of blocks
  containing the singleton of every ramified prime accounts for the square roots of the field.**

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

/-! ### The primes involved in a radicand -/

/-- The radicand of an exponent vector at the prime two splits off each prime it involves, the
complementary factor being prime to it. -/
theorem exists_eq_mul_residueRadicand (hSprime : ∀ p ∈ S, p.Prime)
    (b : {q // q ∈ S} → ZMod 2) {p : ℕ} (hpS : p ∈ S) (hbp : b ⟨p, hpS⟩ = 1) :
    ∃ M : ℕ, residueRadicand S b = p * M ∧ ¬ p ∣ M := by
  classical
  set P : {q // q ∈ S} := ⟨p, hpS⟩ with hP
  refine ⟨∏ i ∈ (Finset.univ : Finset {q // q ∈ S}).erase P, (i : ℕ) ^ (b i).val, ?_, ?_⟩
  · rw [residueRadicand, ← Finset.prod_erase_mul _ _ (Finset.mem_univ P), hbp,
      show ((1 : ZMod 2)).val = 1 from rfl, pow_one, mul_comm]
  · intro hdvd
    have hcop : Nat.Coprime p (∏ i ∈ (Finset.univ : Finset {q // q ∈ S}).erase P,
        (i : ℕ) ^ (b i).val) := by
      refine Nat.Coprime.prod_right fun i hi => Nat.Coprime.pow_right _ ?_
      refine (Nat.coprime_primes (hSprime p hpS) (hSprime i.1 i.2)).mpr fun h => ?_
      exact (Finset.mem_erase.mp hi).1 (Subtype.ext h.symm)
    have h1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd dvd_rfl hdvd
    exact (hSprime p hpS).one_lt.ne' (Nat.dvd_one.mp h1)

/-- **A prime involved in the radicand of an exponent vector ramifies in every field containing a
square root of that radicand.**  The prime divides the radicand exactly once, the other primes
involved being distinct from it. -/
theorem mem_ramifiedSet_of_sq_eq_residueRadicand
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A]
    (hSprime : ∀ p ∈ S, p.Prime) {b : {q // q ∈ S} → ZMod 2}
    (hb : ∃ u ∈ A, u ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) ((residueRadicand S b : ℕ) : ℚ))
    {p : ℕ} (hpS : p ∈ S) (hbp : b ⟨p, hpS⟩ = 1) : p ∈ ramifiedSet ↥A := by
  obtain ⟨u, huA, hu⟩ := hb
  obtain ⟨M, hMeq, hMndvd⟩ := exists_eq_mul_residueRadicand hSprime b hpS hbp
  have hcast : u ^ 2 = ((((residueRadicand S b : ℕ) : ℤ)) : AlgebraicClosure ℚ) := by
    rw [hu, map_natCast]
    push_cast
    ring
  have hnat : ¬ (p ^ 2 : ℕ) ∣ residueRadicand S b := by
    rw [hMeq, sq, Nat.mul_dvd_mul_iff_left (hSprime p hpS).pos]
    exact hMndvd
  refine mem_ramifiedSet_of_sq_eq_intCast (sq_eq_intCast_coe A huA hcast) (hSprime p hpS)
    (Int.natCast_dvd_natCast.mpr ⟨M, hMeq⟩) fun hdvd => hnat ?_
  exact_mod_cast hdvd

/-! ### The invariant along the climb -/

/-- A field is **spanned by a family of blocks of primes** when every squarefree product of primes
admitting a square root in it is, up to squares, a product of the blocks of the family. -/
def IsBlockSpanned (A : IntermediateField ℚ (AlgebraicClosure ℚ)) {ι : Type*}
    (block : ι → Finset ℕ) : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∀ b : {q // q ∈ S} → ZMod 2,
    (∃ u ∈ A, u ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) ((residueRadicand S b : ℕ) : ℚ)) →
      b ∈ blockSpan S block

/-- **A family of blocks accounting for the square roots of a field accounts for those of any
Frattini extension of it.**  A square root of a rational number in the larger field is fixed by the
Frattini subgroup, hence by the automorphisms fixing the smaller field, so it lies in the smaller
field already. -/
theorem IsBlockSpanned.of_le_of_ker_le_frattini
    {A L : IntermediateField ℚ (AlgebraicClosure ℚ)} [Normal ℚ ↥A] [FiniteDimensional ℚ ↥L]
    [IsGalois ℚ ↥L] (hAL : A ≤ L) (hfr : (galRestrictLE hAL).ker ≤ frattini Gal(↥L/ℚ))
    {ι : Type*} {block : ι → Finset ℕ} (hA : IsBlockSpanned A block) : IsBlockSpanned L block := by
  rintro S hS b ⟨u, huL, hu⟩
  exact hA S hS b ⟨u, mem_of_sq_eq_of_ker_le_frattini hAL hfr huL hu, hu⟩

/-- **A family of blocks containing the singleton of every ramified prime accounts for the square
roots of the field.**  Every prime involved in a radicand with a square root in the field ramifies
there, so the exponent vector is the sum of the indicator vectors of the singletons of the primes
it involves, all of them blocks of the family. -/
theorem isBlockSpanned_of_singleton_mem_of_mem_ramifiedSet
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] {ι : Type*}
    {block : ι → Finset ℕ} (hcov : ∀ p ∈ ramifiedSet ↥A, ∃ i, block i = {p}) :
    IsBlockSpanned A block := by
  classical
  intro S hS b hb
  rw [← Finset.univ_sum_single b]
  refine Submodule.sum_mem _ fun q _ => ?_
  rcases eq_zero_or_one_zmod_two (b q) with h | h
  · rw [h, Pi.single_zero]
    exact Submodule.zero_mem _
  obtain ⟨i, hi⟩ := hcov q.1 (mem_ramifiedSet_of_sq_eq_residueRadicand A hS hb q.2 h)
  have hsingle : Pi.single q (b q) = blockVector S (block i) := by
    ext r
    rw [h, hi, blockVector]
    by_cases hr : r = q
    · subst hr
      simp
    · rw [Pi.single_eq_of_ne hr,
        if_neg fun hc => hr (Subtype.ext (Finset.mem_singleton.mp hc))]
  rw [hsingle]
  exact Submodule.subset_span ⟨i, rfl⟩

end InverseGalois.CFT
