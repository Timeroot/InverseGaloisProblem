import Mathlib
import InverseGalois.CFT.Local.PadicSquaresTwo

/-!
# The dyadic obstruction to being a sum of three squares

The classical exceptional set of the three-squares theorem consists of the natural numbers of the
shape `4 ^ a * (8 * b + 7)`. This file identifies that set, among the positive naturals, with the
set of `n` such that `-n` is a square in `ℚ_[2]`.

The identification runs through the multiplicative decomposition `n = 2 ^ e * m` with `m` odd.
A nonzero dyadic number is a square exactly when its valuation is even and its unit part is
congruent to `1` modulo `8`; here the valuation of `-n` is `e` and the unit part is `-m`, so `-n`
is a dyadic square exactly when `e` is even and `m ≡ 7 (mod 8)`. Undoing the decomposition, the
even exponent contributes the factor `4 ^ a` and the residue condition the factor `8 * b + 7`.

The dyadic input is taken from `InverseGalois/CFT/Local/PadicSquaresTwo.lean`, which characterises
the squares among the dyadic units through `PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)`.

## Main results

* `InverseGalois.CFT.exists_four_pow_mul_iff`: the elementary reformulation of the exceptional set,
  `(∃ a b, n = 4 ^ a * (8 * b + 7))` if and only if `n = 2 ^ e * m` with `e` even and
  `m % 8 = 7`.
* `InverseGalois.CFT.isSquare_neg_iff_of_two_pow_mul`: for `n = 2 ^ e * m` with `m` odd, the
  negative `-n` is a dyadic square exactly when `e` is even and `m % 8 = 7`.
* `InverseGalois.CFT.isSquare_neg_padic_two_iff`: for `0 < n`, the negative `-n` is a square
  in `ℚ_[2]` exactly when `n = 4 ^ a * (8 * b + 7)` for some `a` and `b`.
* `InverseGalois.CFT.isSquare_neg_natCast_padic_two_iff`: the same statement with the other
  coercion route.
-/

namespace InverseGalois.CFT

open Local

/-- A natural number reduces to `7` in `ZMod 8` exactly when its remainder modulo `8` is `7`. -/
theorem natCast_eq_seven_zmod_iff {m : ℕ} : ((m : ZMod 8) = 7) ↔ m % 8 = 7 := by
  constructor
  · intro h
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_natCast] at h2
    simpa using h2
  · intro h
    rw [← ZMod.natCast_mod, h]
    norm_num

/-- The negative of an odd natural number is a unit of `ℤ_[2]`. -/
theorem isUnit_neg_natCast_two {m : ℕ} (hm : ¬ 2 ∣ m) : IsUnit (-(m : ℤ_[2])) := by
  rw [IsUnit.neg_iff, PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.prime_two).coprime_iff_not_dvd.mpr hm

/-- The dyadic valuation of the negative of a natural number is its `2`-adic valuation. -/
theorem valuation_neg_natCast_two {n : ℕ} :
    ((-(n : ℤ) : ℚ_[2])).valuation = padicValNat 2 n := by
  rw [← Int.cast_neg, Padic.valuation_intCast]
  simp [padicValInt]

/-- The `2`-adic valuation of `2 ^ e * m` with `m` odd is `e`. -/
theorem padicValNat_two_pow_mul {e m : ℕ} (hm : ¬ 2 ∣ m) : padicValNat 2 (2 ^ e * m) = e := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm ⟨0, rfl⟩
  rw [padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero]

/-- A natural number is of the shape `4 ^ a * (8 * b + 7)` exactly when it is `2 ^ e * m` for an
even exponent `e` and a factor `m` congruent to `7` modulo `8`. -/
theorem exists_four_pow_mul_iff {n : ℕ} :
    (∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)) ↔ ∃ e m : ℕ, n = 2 ^ e * m ∧ Even e ∧ m % 8 = 7 := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨2 * a, 8 * b + 7, ?_, ⟨a, two_mul a⟩, by omega⟩
    rw [pow_mul]
    norm_num
  · rintro ⟨e, m, rfl, ⟨k, hk⟩, hmod⟩
    refine ⟨k, m / 8, ?_⟩
    have hmm : 8 * (m / 8) + 7 = m := by omega
    rw [hmm, hk, ← two_mul, pow_mul]
    norm_num

/-- For a decomposition `n = 2 ^ e * m` into a power of two and an odd factor, the negative `-n`
is a square in `ℚ_[2]` exactly when the exponent `e` is even and `m` is congruent to `7`
modulo `8`: the valuation of `-n` is `e`, and its unit part `-m` is a square precisely when it
reduces to `1` in `ZMod 8`. -/
theorem isSquare_neg_iff_of_two_pow_mul {n e m : ℕ} (hnm : n = 2 ^ e * m) (hm : ¬ 2 ∣ m) :
    IsSquare ((-(n : ℤ) : ℚ_[2])) ↔ Even e ∧ m % 8 = 7 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm ⟨0, rfl⟩
  have hn0 : n ≠ 0 := by
    rw [hnm]; exact Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) hm0
  have hu : IsUnit (-(m : ℤ_[2])) := isUnit_neg_natCast_two hm
  have hx : ((-(n : ℤ) : ℚ_[2])) ≠ 0 := by
    simp [hn0]
  have hxeq : ((-(n : ℤ) : ℚ_[2])) = (2 : ℚ_[2]) ^ e * ((-(m : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) := by
    rw [hnm]; push_cast; ring
  have hval : ((-(n : ℤ) : ℚ_[2])).valuation = (e : ℤ) := by
    rw [valuation_neg_natCast_two, hnm, padicValNat_two_pow_mul hm]
  constructor
  · intro hsq
    have hev : Even ((-(n : ℤ) : ℚ_[2])).valuation := even_valuation_of_isSquare hx hsq
    rw [hval] at hev
    have heven : Even e := by exact_mod_cast hev
    refine ⟨heven, ?_⟩
    obtain ⟨k, hk⟩ := heven
    obtain ⟨y, hy⟩ := hsq
    have hpow : ((2 : ℚ_[2]) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
    have husq : IsSquare (((-(m : ℤ_[2]) : ℤ_[2])) : ℚ_[2]) := by
      refine ⟨y / (2 : ℚ_[2]) ^ k, ?_⟩
      rw [div_mul_div_comm, ← hy, hxeq, hk, pow_add]
      field_simp
    rw [isSquare_coe_iff_two hu] at husq
    have h8 : -((m : ℕ) : ZMod 8) = 1 := by
      rw [map_neg, map_natCast] at husq
      exact husq
    rw [neg_eq_iff_eq_neg, show (-1 : ZMod 8) = 7 by decide] at h8
    exact natCast_eq_seven_zmod_iff.mp h8
  · rintro ⟨⟨k, hk⟩, hmod⟩
    rw [hxeq, hk, pow_add]
    refine IsSquare.mul ⟨(2 : ℚ_[2]) ^ k, rfl⟩ ?_
    rw [isSquare_coe_iff_two hu, map_neg, map_natCast]
    have hm8 : ((m : ℕ) : ZMod 8) = 7 := natCast_eq_seven_zmod_iff.mpr hmod
    rw [show ((m : ℕ) : ZMod (2 ^ 3)) = 7 from hm8]
    decide

/-- A positive natural number is `4 ^ a * (8 * b + 7)` for some `a b` exactly when its negative is
a dyadic square. -/
theorem isSquare_neg_padic_two_iff {n : ℕ} (hn : 0 < n) :
    IsSquare ((-(n : ℤ) : ℚ_[2])) ↔ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  rw [exists_four_pow_mul_iff]
  constructor
  · intro h
    obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 2 (by norm_num)
    exact ⟨e, m, hnm, (isSquare_neg_iff_of_two_pow_mul hnm hm).mp h⟩
  · rintro ⟨e, m, hnm, he, hmod⟩
    have hm : ¬ 2 ∣ m := by omega
    exact (isSquare_neg_iff_of_two_pow_mul hnm hm).mpr ⟨he, hmod⟩

/-- The two coercion routes from a natural number to a negative dyadic number agree. -/
theorem neg_intCast_eq_neg_natCast_padic_two (n : ℕ) : ((-(n : ℤ) : ℚ_[2])) = -(n : ℚ_[2]) := by
  push_cast
  ring

/-- A positive natural number is `4 ^ a * (8 * b + 7)` for some `a b` exactly when its negative is
a dyadic square, stated with the direct coercion `ℕ → ℚ_[2]`. -/
theorem isSquare_neg_natCast_padic_two_iff {n : ℕ} (hn : 0 < n) :
    IsSquare (-(n : ℚ_[2])) ↔ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  rw [← neg_intCast_eq_neg_natCast_padic_two]
  exact isSquare_neg_padic_two_iff hn

end InverseGalois.CFT
