/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.Scholz.FrattiniInertia

/-!
# A prescribed power of two dividing the residue degree at two

The residue degree of a rational prime `p` in the cyclotomic field of conductor `n` prime to `p`
is the multiplicative order of `p` modulo `n`, and residue degrees are multiplicative in a tower,
so that order divides the residue degree at every prime above `p` of every number field containing
a primitive `n`-th root of unity.

For the prime two the conductors to use are the Fermat numbers.  A prime divisor is not needed:
modulo `2 ^ 2 ^ k + 1` the class of two squares to one after `k + 1` doublings and not before,
because `2 ^ 2 ^ k` is congruent to `-1` there and `-1` is not `1`.  So a primitive
`(2 ^ 2 ^ k + 1)`-th root of unity forces `2 ^ (k + 1)` to divide the residue degree at two, and
`k` may be taken as large as one pleases.

## Main results

* `InverseGalois.CFT.orderOf_two_zmod_fermat`: **the class of two modulo a Fermat number has order
  exactly the corresponding power of two.**
* `InverseGalois.CFT.orderOf_dvd_inertiaDeg_of_isPrimitiveRoot`: **the order of a prime modulo `n`
  divides the residue degree of any prime above it in a number field containing a primitive `n`-th
  root of unity.**
* `InverseGalois.CFT.pow_dvd_inertiaDeg_two_of_cycSubfield_le`: **adjoining the cyclotomic field of
  Fermat conductor makes the residue degree at two divisible by a prescribed power of two.**
* `InverseGalois.CFT.not_dvd_fermat_of_le`: **a prime not exceeding a power of two does not divide
  the Fermat number of the previous index**, so a Fermat conductor can be chosen prime to any
  prescribed finite set of primes.

## Tags

residue degree, inertia degree, Frobenius, cyclotomic field, Fermat number, Scholz–Reichardt
-/

open NumberField

namespace InverseGalois.CFT

/-! ### The order of two modulo a Fermat number -/

/-- A Fermat number exceeds two. -/
theorem two_le_two_pow_two_pow (k : ℕ) : 2 ≤ 2 ^ 2 ^ k := by
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow

/-- A Fermat number is odd. -/
theorem not_two_dvd_fermat (k : ℕ) : ¬ (2 : ℕ) ∣ 2 ^ 2 ^ k + 1 := by
  have hk : 2 ^ k ≠ 0 := by positivity
  have h : (2 : ℕ) ∣ 2 ^ 2 ^ k := dvd_pow_self 2 hk
  omega

/-- **The class of two modulo a Fermat number has order exactly the corresponding power of two.**
The class of `2 ^ 2 ^ k` is `-1`, so the order divides `2 ^ (k + 1)` and does not divide `2 ^ k`. -/
theorem orderOf_two_zmod_fermat (k : ℕ) :
    orderOf (((2 : ℕ) : ZMod (2 ^ 2 ^ k + 1))) = 2 ^ (k + 1) := by
  have hle := two_le_two_pow_two_pow k
  have hself : (((2 ^ 2 ^ k + 1 : ℕ) : ZMod (2 ^ 2 ^ k + 1))) = 0 :=
    ZMod.natCast_self (2 ^ 2 ^ k + 1)
  have hneg : (((2 : ℕ) : ZMod (2 ^ 2 ^ k + 1))) ^ 2 ^ k = -1 := by
    push_cast at hself ⊢
    linear_combination hself
  have hpow : (((2 : ℕ) : ZMod (2 ^ 2 ^ k + 1))) ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ, pow_mul, hneg, neg_one_sq]
  obtain ⟨j, hjle, hj⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
  rcases eq_or_lt_of_le hjle with rfl | hlt
  · exact hj
  · exfalso
    have hjk : j ≤ k := by omega
    have h1 : (((2 : ℕ) : ZMod (2 ^ 2 ^ k + 1))) ^ 2 ^ k = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hj]; exact pow_dvd_pow 2 hjk)
    rw [hneg] at h1
    have h2 : (((2 : ℕ) : ZMod (2 ^ 2 ^ k + 1))) = 0 := by
      push_cast
      linear_combination -h1
    have hdvd := (ZMod.natCast_eq_zero_iff 2 (2 ^ 2 ^ k + 1)).mp h2
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

/-! ### The prime divisors of a Fermat number -/

/-- **A prime divisor of a Fermat number is congruent to one modulo the next power of two.**  The
class of two modulo such a prime has the same order `2 ^ (k + 1)` as it has modulo the Fermat
number itself, and that order divides the order of the multiplicative group. -/
theorem two_pow_succ_dvd_sub_one_of_dvd_fermat {k p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ 2 ^ 2 ^ k + 1) : 2 ^ (k + 1) ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact not_two_dvd_fermat k hdvd
  have hne0 : (((2 : ℕ) : ZMod p)) ≠ 0 := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  have hzero : (((2 ^ 2 ^ k + 1 : ℕ) : ZMod p)) = 0 :=
    (ZMod.natCast_eq_zero_iff (2 ^ 2 ^ k + 1) p).mpr hdvd
  have hneg : (((2 : ℕ) : ZMod p)) ^ 2 ^ k = -1 := by
    push_cast at hzero ⊢
    linear_combination hzero
  have hpow : (((2 : ℕ) : ZMod p)) ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ, pow_mul, hneg, neg_one_sq]
  have hord : orderOf (((2 : ℕ) : ZMod p)) = 2 ^ (k + 1) := by
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    rcases eq_or_lt_of_le hjle with rfl | hlt
    · exact hj
    · exfalso
      have hjk : j ≤ k := by omega
      have h1 : (((2 : ℕ) : ZMod p)) ^ 2 ^ k = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (by rw [hj]; exact pow_dvd_pow 2 hjk)
      rw [hneg] at h1
      exact hne0 (by push_cast; linear_combination -h1)
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hne0)

/-- **A prime divisor of a Fermat number exceeds the next power of two.** -/
theorem two_pow_succ_lt_of_dvd_fermat {k p : ℕ} (hp : p.Prime) (hdvd : p ∣ 2 ^ 2 ^ k + 1) :
    2 ^ (k + 1) < p := by
  have h2 := hp.two_le
  have hle := Nat.le_of_dvd (by omega) (two_pow_succ_dvd_sub_one_of_dvd_fermat hp hdvd)
  omega

/-- **A prime not exceeding a power of two does not divide the Fermat number of the previous
index.**  Since a Fermat conductor can be taken as large as one likes, it can be taken prime to any
prescribed finite set of primes. -/
theorem not_dvd_fermat_of_le {k p : ℕ} (hp : p.Prime) (hple : p ≤ 2 ^ (k + 1)) :
    ¬ p ∣ 2 ^ 2 ^ k + 1 := fun hdvd => by
  have := two_pow_succ_lt_of_dvd_fermat hp hdvd
  omega

/-! ### The residue degree in a field containing a root of unity -/

/-- **The order of a prime modulo `n` divides the residue degree of any prime above it in a number
field containing a primitive `n`-th root of unity.**  The field generated by the root of unity is
a cyclotomic field, where that order is the residue degree, and residue degrees multiply in a
tower. -/
theorem orderOf_dvd_inertiaDeg_of_isPrimitiveRoot {L : Type*} [Field L] [NumberField L] {n : ℕ}
    [NeZero n] {ζ : L} (hζ : IsPrimitiveRoot ζ n) {p : ℕ} [Fact p.Prime] (hpn : ¬ p ∣ n)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    orderOf ((p : ZMod n)) ∣ (Ideal.span {(p : ℤ)}).inertiaDeg P := by
  haveI : Algebra.IsIntegral ℚ L := Algebra.IsIntegral.of_finite ℚ L
  haveI : IsCyclotomicExtension {n} ℚ ↥(IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI : NumberField ↥(IntermediateField.adjoin ℚ {ζ}) := ⟨⟩
  haveI := liesOver_under_intermediateField (p := p) (IntermediateField.adjoin ℚ {ζ}) P
  have h := inertiaDeg_under_dvd (Fact.out : p.Prime) (IntermediateField.adjoin ℚ {ζ}) P
  rwa [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p ↥(IntermediateField.adjoin ℚ {ζ})
    (P.under (𝓞 ↥(IntermediateField.adjoin ℚ {ζ}))) hpn] at h

/-- **A primitive root of unity of Fermat conductor makes the residue degree at two divisible by a
prescribed power of two.** -/
theorem pow_dvd_inertiaDeg_two_of_isPrimitiveRoot {L : Type*} [Field L] [NumberField L] (k : ℕ)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ 2 ^ k + 1)) (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver (Ideal.span {((2 : ℕ) : ℤ)})] :
    2 ^ k ∣ (Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero (2 ^ 2 ^ k + 1) := ⟨by positivity⟩
  refine dvd_trans ?_ (orderOf_dvd_inertiaDeg_of_isPrimitiveRoot hζ (not_two_dvd_fermat k) P)
  rw [orderOf_two_zmod_fermat k]
  exact pow_dvd_pow 2 (Nat.le_succ k)

/-! ### The enlargement inside a fixed algebraic closure -/

/-- **Adjoining the cyclotomic field of Fermat conductor makes the residue degree at two divisible
by a prescribed power of two.** -/
theorem pow_dvd_inertiaDeg_two_of_cycSubfield_le (k : ℕ)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
    (hUL : cycSubfield (2 ^ 2 ^ k + 1) ≤ L) (P : Ideal (𝓞 ↥L)) [P.IsPrime]
    [P.LiesOver (Ideal.span {((2 : ℕ) : ℤ)})] :
    2 ^ k ∣ (Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg P := by
  haveI : NeZero (2 ^ 2 ^ k + 1) := ⟨by positivity⟩
  have hmem : cycRoot (2 ^ 2 ^ k + 1) ∈ L :=
    hUL (IntermediateField.subset_adjoin ℚ _ rfl)
  refine pow_dvd_inertiaDeg_two_of_isPrimitiveRoot k
    (ζ := (⟨cycRoot (2 ^ 2 ^ k + 1), hmem⟩ : ↥L)) ?_ P
  refine IsPrimitiveRoot.of_map_of_injective (f := (IntermediateField.val L).toMonoidHom) ?_ ?_
  · exact cycRoot_spec (2 ^ 2 ^ k + 1)
  · exact (IntermediateField.val L).injective

end InverseGalois.CFT
