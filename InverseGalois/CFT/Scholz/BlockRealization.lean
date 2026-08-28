/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CharacterSpan
import InverseGalois.CFT.PrimeProductSquare
import InverseGalois.CFT.SqrtSign
import InverseGalois.CFT.Scholz.DyadicSocle

/-!
# Blocks accounted for by square roots carrying independent sign characters

A family of pairwise disjoint blocks of primes, each block having a square root of the product of
its primes inside the field, accounts for all the square roots of the field as soon as the sign
characters of those square roots are independent and their common kernel lies in the Frattini
subgroup.

Given any square root of a squarefree product of primes in the field, its sign character vanishes on
the common kernel of the block characters, hence is a sum of a subfamily of them, hence agrees with
the sign character of the product of the corresponding square roots.  Two square roots with the same
sign character have a product of radicands which is a square, and a product of two squarefree
products of primes is a square only when the two sets of primes coincide.  So the exponent vector is
the sum of the indicators of the blocks of the subfamily.

## Main definitions

* `InverseGalois.CFT.radicandSupport`: the set of primes occurring in the radicand of an exponent
  vector at the prime two.

## Main results

* `InverseGalois.CFT.residueRadicand_eq_prod_radicandSupport`: the radicand is the product of the
  primes it involves.
* `InverseGalois.CFT.blockVector_biUnion_eq_sum`: the indicator of a union of pairwise disjoint
  blocks is the sum of their indicators.
* `InverseGalois.CFT.isBlockSpanned_of_sqrtSign_surjective`: **a field carrying square roots of the
  products of a pairwise disjoint family of blocks of primes, whose sign characters are jointly
  surjective with kernel inside the Frattini subgroup, is spanned by that family of blocks.**

## Tags

Scholz–Reichardt, block, square root, sign character, Frattini subgroup
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {S : Finset ℕ}

/-! ### The primes involved in a radicand -/

/-- The set of primes occurring in the radicand of an exponent vector at the prime two. -/
def radicandSupport (S : Finset ℕ) (b : {p // p ∈ S} → ZMod 2) : Finset ℕ :=
  (Finset.univ.filter fun q : {p // p ∈ S} => b q = 1).image Subtype.val

theorem mem_radicandSupport_iff {b : {p // p ∈ S} → ZMod 2} (q : {p // p ∈ S}) :
    (q : ℕ) ∈ radicandSupport S b ↔ b q = 1 := by
  classical
  constructor
  · intro hq
    obtain ⟨r, hr, hrq⟩ := Finset.mem_image.mp hq
    have hrq' : r = q := Subtype.ext hrq
    subst hrq'
    exact (Finset.mem_filter.mp hr).2
  · intro hb
    exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

theorem radicandSupport_subset (b : {p // p ∈ S} → ZMod 2) : radicandSupport S b ⊆ S := by
  intro p hp
  obtain ⟨r, -, hrp⟩ := Finset.mem_image.mp hp
  exact hrp ▸ r.2

/-- The exponent vector is the indicator of the set of primes its radicand involves. -/
theorem blockVector_radicandSupport (b : {p // p ∈ S} → ZMod 2) :
    blockVector S (radicandSupport S b) = b := by
  funext q
  show (if (q : ℕ) ∈ radicandSupport S b then (1 : ZMod 2) else 0) = b q
  rcases eq_zero_or_one_zmod_two (b q) with h | h
  · rw [if_neg fun hc => by rw [(mem_radicandSupport_iff q).mp hc] at h; exact absurd h (by decide),
      h]
  · rw [if_pos ((mem_radicandSupport_iff q).mpr h), h]

/-- **The radicand of an exponent vector at the prime two is the product of the primes it
involves.** -/
theorem residueRadicand_eq_prod_radicandSupport (b : {p // p ∈ S} → ZMod 2) :
    residueRadicand S b = ∏ p ∈ radicandSupport S b, p := by
  classical
  have himg : ∏ p ∈ radicandSupport S b, p
      = ∏ q ∈ Finset.univ.filter fun q : {p // p ∈ S} => b q = 1, (q : ℕ) := by
    rw [radicandSupport]
    exact Finset.prod_image fun x _ y _ h => Subtype.ext h
  rw [himg, Finset.prod_filter, residueRadicand]
  refine Finset.prod_congr rfl fun q _ => ?_
  rcases eq_zero_or_one_zmod_two (b q) with h | h <;> rw [h]
  · rw [show ((0 : ZMod 2)).val = 0 from rfl, pow_zero, if_neg (by decide)]
  · rw [show ((1 : ZMod 2)).val = 1 from rfl, pow_one, if_pos rfl]

/-- The radicand of an exponent vector over a set of primes is nonzero. -/
theorem residueRadicand_ne_zero (hSprime : ∀ p ∈ S, p.Prime) (b : {p // p ∈ S} → ZMod 2) :
    residueRadicand S b ≠ 0 := by
  rw [residueRadicand]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hSprime i.1 i.2).ne_zero

/-! ### The indicator of a union of blocks -/

/-- **The indicator of a union of pairwise disjoint blocks is the sum of their indicators.** -/
theorem blockVector_biUnion_eq_sum {ι : Type*} [DecidableEq ι] {block : ι → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j)) (J : Finset ι) :
    blockVector S (J.biUnion block) = ∑ i ∈ J, blockVector S (block i) := by
  classical
  funext q
  simp only [blockVector, Finset.sum_apply]
  by_cases hq : (q : ℕ) ∈ J.biUnion block
  · obtain ⟨i₀, hi₀J, hi₀⟩ := Finset.mem_biUnion.mp hq
    have hsum : ∑ i ∈ J, (if (q : ℕ) ∈ block i then (1 : ZMod 2) else 0)
        = if (q : ℕ) ∈ block i₀ then (1 : ZMod 2) else 0 :=
      Finset.sum_eq_single_of_mem i₀ hi₀J fun j _ hne =>
        if_neg fun hc => Finset.disjoint_left.mp (hdisj j i₀ hne) hc hi₀
    rw [if_pos hq, hsum, if_pos hi₀]
  · rw [if_neg hq]
    exact (Finset.sum_eq_zero fun i hi =>
      if_neg fun hc => hq (Finset.mem_biUnion.mpr ⟨i, hi, hc⟩)).symm

/-! ### Reading a square root inside an intermediate field -/

/-- A square root of a rational number lying in an intermediate field, read inside that field. -/
theorem sq_eq_algebraMap_coe {A : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {u : AlgebraicClosure ℚ} (huA : u ∈ A) {m : ℚ}
    (hu : u ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) m) :
    (⟨u, huA⟩ : ↥A) ^ 2 = algebraMap ℚ ↥A m := by
  apply Subtype.ext
  push_cast
  exact hu

/-! ### Blocks realised by square roots with independent sign characters -/

/-- **A field carrying square roots of the products of a pairwise disjoint family of blocks of
primes, whose sign characters are jointly surjective with kernel inside the Frattini subgroup, is
spanned by that family of blocks.**  The sign character of any square root of a squarefree product
of primes in the field vanishes on the Frattini subgroup, hence on the common kernel of the block
characters, hence is a sum of a subfamily; the corresponding product of block square roots therefore
has the same sign character, so the two radicands have a square product and involve the same
primes. -/
theorem isBlockSpanned_of_sqrtSign_surjective
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {block : ι → Finset ℕ}
    (hprime : ∀ i, ∀ p ∈ block i, p.Prime)
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j)) (v : ι → ↥A)
    (hvsq : ∀ i, v i ^ 2 = algebraMap ℚ ↥A ((∏ p ∈ block i, p : ℕ) : ℚ))
    (hsurj : Function.Surjective fun (σ : Gal(↥A/ℚ)) (i : ι) => sqrtSign (v i) σ)
    (hker : ∀ σ : Gal(↥A/ℚ), (∀ i, sqrtSign (v i) σ = 0) → σ ∈ frattini Gal(↥A/ℚ)) :
    IsBlockSpanned A block := by
  classical
  -- the block square roots are nonzero, their squares being products of primes
  have hv : ∀ i, v i ≠ 0 := by
    intro i hzero
    have h0 : algebraMap ℚ ↥A ((∏ p ∈ block i, p : ℕ) : ℚ) = 0 := by
      rw [← hvsq i, hzero, zero_pow (by norm_num : 2 ≠ 0)]
    have hP : ((∏ p ∈ block i, p : ℕ) : ℚ) = 0 :=
      (map_eq_zero_iff _ (algebraMap ℚ ↥A).injective).mp h0
    exact prod_prime_ne_zero (hprime i) (by exact_mod_cast hP)
  intro S hSprime b hb
  obtain ⟨u, huA, hu⟩ := hb
  set w : ↥A := ⟨u, huA⟩ with hwdef
  have hw : w ^ 2 = algebraMap ℚ ↥A ((residueRadicand S b : ℕ) : ℚ) := sq_eq_algebraMap_coe huA hu
  have hwne : w ≠ 0 := by
    intro hzero
    have h0 : algebraMap ℚ ↥A ((residueRadicand S b : ℕ) : ℚ) = 0 := by
      rw [← hw, hzero, zero_pow (by norm_num : 2 ≠ 0)]
    have hR : ((residueRadicand S b : ℕ) : ℚ) = 0 :=
      (map_eq_zero_iff _ (algebraMap ℚ ↥A).injective).mp h0
    exact residueRadicand_ne_zero hSprime b (by exact_mod_cast hR)
  -- the sign character of the square root is a sum of block characters
  obtain ⟨J, hJ⟩ := exists_finset_forall_eq_sum (fun i => sqrtSign (v i))
    (fun i σ τ => sqrtSign_apply_mul (hv i) (hvsq i) σ τ) hsurj (sqrtSign w)
    (fun σ τ => sqrtSign_apply_mul hwne hw σ τ)
    fun σ h => sqrtSign_eq_zero_of_mem_frattini hw (hker σ h)
  have hsign : ∀ σ : Gal(↥A/ℚ), sqrtSign w σ = sqrtSign (∏ i ∈ J, v i) σ := fun σ => by
    rw [hJ σ, sqrtSign_prod_apply hv hvsq J σ]
  obtain ⟨c, hc⟩ := exists_sq_eq_mul_of_sqrtSign_eq hw (sq_prod_eq_algebraMap hvsq J) hsign
  -- the two radicands involve the same primes
  have hdisjJ : (↑J : Set ι).PairwiseDisjoint block := fun i _ j _ hij => hdisj i j hij
  have hnat : residueRadicand S b * ∏ i ∈ J, ∏ p ∈ block i, p
      = (∏ p ∈ radicandSupport S b, p) * ∏ p ∈ J.biUnion block, p := by
    rw [residueRadicand_eq_prod_radicandSupport b, Finset.prod_biUnion hdisjJ]
  have hc2 : c ^ 2 = (((∏ p ∈ radicandSupport S b, p) * ∏ p ∈ J.biUnion block, p : ℕ) : ℚ) := by
    rw [hc, ← hnat]
    push_cast
    ring
  have hT : radicandSupport S b = J.biUnion block :=
    eq_of_rat_sq_eq_prod_mul_prod (fun p hp => hSprime p (radicandSupport_subset b hp))
      (fun p hp => by
        obtain ⟨i, -, hpi⟩ := Finset.mem_biUnion.mp hp
        exact hprime i p hpi) hc2
  -- so the exponent vector is the sum of the indicators of the blocks involved
  have hbsum : b = ∑ i ∈ J, blockVector S (block i) := by
    rw [← blockVector_radicandSupport b, hT, blockVector_biUnion_eq_sum hdisj]
  rw [hbsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, rfl⟩

end InverseGalois.CFT
