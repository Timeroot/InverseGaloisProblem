/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Two primes each a square modulo the other

A prime congruent to one modulo an earlier prime is a square modulo that earlier prime for the
trivial reason that one is a square.  When the earlier prime is congruent to one modulo four the
law of quadratic reciprocity turns that around and makes the earlier prime a square modulo the
later one as well.

So a chain of primes in which each is congruent to one modulo all its predecessors is a chain in
which every prime is a square modulo every other, which is what makes the auxiliary primes of a
residue correction with several independent characters harmless to one another.

## Main results

* `InverseGalois.CFT.isSquare_natCast_of_modEq_left`: the later prime is a square modulo the
  earlier one.
* `InverseGalois.CFT.isSquare_natCast_of_modEq_right`: **the earlier prime is a square modulo the
  later one**, by quadratic reciprocity.
* `InverseGalois.CFT.pow_natCast_eq_one_of_modEq_left` and
  `InverseGalois.CFT.pow_natCast_eq_one_of_modEq_right`: the same statements in the form of Euler's
  criterion.
* `InverseGalois.CFT.isSquare_natCast_swap`: **the quadratic residue relation between two primes is
  symmetric as soon as one of them is congruent to one modulo four**, whatever the source of the
  first half.
* `InverseGalois.CFT.pow_natCast_eq_one_swap`: the same in the form of Euler's criterion.

## Tags

quadratic reciprocity, quadratic residue, auxiliary prime, Euler criterion
-/

namespace InverseGalois.CFT

variable {a b : ℕ}

/-! ### Consequences of the congruence -/

/-- A prime congruent to one modulo four is at least five. -/
theorem five_le_of_mod_four_eq_one (ha : a.Prime) (ha4 : a % 4 = 1) : 5 ≤ a := by
  rcases Nat.lt_or_ge a 5 with h | h
  · interval_cases a <;> revert ha4 ha <;> decide
  · exact h

/-- A prime congruent to one modulo a prime congruent to one modulo four is distinct from it and
odd. -/
theorem ne_two_of_modEq (ha : a.Prime) (ha4 : a % 4 = 1) (hab : b ≡ 1 [MOD a]) : b ≠ 2 := by
  have h5 := five_le_of_mod_four_eq_one ha ha4
  rintro rfl
  rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hab
  omega

/-- A prime congruent to one modulo a prime congruent to one modulo four is different from it. -/
theorem ne_of_modEq (ha : a.Prime) (ha4 : a % 4 = 1) (hab : b ≡ 1 [MOD a]) : a ≠ b := by
  have h5 := five_le_of_mod_four_eq_one ha ha4
  rintro rfl
  rw [Nat.ModEq, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hab
  omega

/-! ### The two squares -/

/-- **The later prime is a square modulo the earlier one**, being congruent to one there. -/
theorem isSquare_natCast_of_modEq_left (hab : b ≡ 1 [MOD a]) : IsSquare ((b : ZMod a)) := by
  have h : ((b : ℕ) : ZMod a) = ((1 : ℕ) : ZMod a) := (ZMod.natCast_eq_natCast_iff b 1 a).mpr hab
  rw [h, Nat.cast_one]
  exact ⟨1, (one_mul 1).symm⟩

/-- **The earlier prime is a square modulo the later one.**  The later prime is a square modulo the
earlier one, and the earlier one being congruent to one modulo four the law of quadratic
reciprocity exchanges the two symbols. -/
theorem isSquare_natCast_of_modEq_right (ha : a.Prime) (hb : b.Prime) (ha4 : a % 4 = 1)
    (hab : b ≡ 1 [MOD a]) : IsSquare ((a : ZMod b)) := by
  haveI : Fact a.Prime := ⟨ha⟩
  haveI : Fact b.Prime := ⟨hb⟩
  have hne : a ≠ b := ne_of_modEq ha ha4 hab
  have hb2 : b ≠ 2 := ne_two_of_modEq ha ha4 hab
  have hb0 : ((b : ℕ) : ZMod a) ≠ 0 := by
    rw [(ZMod.natCast_eq_natCast_iff b 1 a).mpr hab, Nat.cast_one]
    exact one_ne_zero
  have ha0 : ((a : ℕ) : ZMod b) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hb ha).mp h).symm
  have hab1 : legendreSym a b = 1 := (legendreSym.eq_one_iff' a hb0).mpr
    (isSquare_natCast_of_modEq_left hab)
  have hba : legendreSym b a = 1 := by
    rw [legendreSym.quadratic_reciprocity_one_mod_four ha4 hb2]
    exact hab1
  exact (legendreSym.eq_one_iff' b ha0).mp hba

/-! ### Euler's criterion -/

/-- **The later prime is a power residue modulo the earlier one.** -/
theorem pow_natCast_eq_one_of_modEq_left (hab : b ≡ 1 [MOD a]) :
    ((b : ZMod a)) ^ ((a - 1) / 2) = 1 := by
  have h : ((b : ℕ) : ZMod a) = ((1 : ℕ) : ZMod a) := (ZMod.natCast_eq_natCast_iff b 1 a).mpr hab
  rw [h, Nat.cast_one, one_pow]

/-- **The earlier prime is a power residue modulo the later one.** -/
theorem pow_natCast_eq_one_of_modEq_right (ha : a.Prime) (hb : b.Prime) (ha4 : a % 4 = 1)
    (hab : b ≡ 1 [MOD a]) : ((a : ZMod b)) ^ ((b - 1) / 2) = 1 := by
  haveI : Fact a.Prime := ⟨ha⟩
  haveI : Fact b.Prime := ⟨hb⟩
  have hne : a ≠ b := ne_of_modEq ha ha4 hab
  have hb2 : b ≠ 2 := ne_two_of_modEq ha ha4 hab
  have hbodd : b % 2 = 1 := Nat.odd_iff.mp (hb.odd_of_ne_two hb2)
  have ha0 : ((a : ℕ) : ZMod b) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hb ha).mp h).symm
  have h := (ZMod.euler_criterion b ha0).mp (isSquare_natCast_of_modEq_right ha hb ha4 hab)
  have hhalf : (b - 1) / 2 = b / 2 := by omega
  rw [hhalf]
  exact h

/-! ### Turning the relation around -/

/-- **The quadratic residue relation between two primes is symmetric as soon as one of them is
congruent to one modulo four.**  The law of quadratic reciprocity attaches to the two primes the
same symbol, and a nonzero residue is a square exactly when its symbol is one. -/
theorem isSquare_natCast_swap (ha : a.Prime) (hb : b.Prime) (ha4 : a % 4 = 1) (hb2 : b ≠ 2)
    (hne : a ≠ b) (h : IsSquare ((a : ZMod b))) : IsSquare ((b : ZMod a)) := by
  haveI : Fact a.Prime := ⟨ha⟩
  haveI : Fact b.Prime := ⟨hb⟩
  have ha0 : ((a : ℕ) : ZMod b) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => hne ((Nat.prime_dvd_prime_iff_eq hb ha).mp hd).symm
  have hb0 : ((b : ℕ) : ZMod a) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => hne ((Nat.prime_dvd_prime_iff_eq ha hb).mp hd)
  have hba : legendreSym b a = 1 := (legendreSym.eq_one_iff' b ha0).mpr h
  have hab : legendreSym a b = 1 := by
    rw [← legendreSym.quadratic_reciprocity_one_mod_four ha4 hb2]
    exact hba
  exact (legendreSym.eq_one_iff' a hb0).mp hab

/-- **The quadratic residue relation between two primes is symmetric as soon as one of them is
congruent to one modulo four**, in the form of Euler's criterion. -/
theorem pow_natCast_eq_one_swap (ha : a.Prime) (hb : b.Prime) (ha4 : a % 4 = 1) (hb2 : b ≠ 2)
    (hne : a ≠ b) (h : ((a : ZMod b)) ^ ((b - 1) / 2) = 1) :
    ((b : ZMod a)) ^ ((a - 1) / 2) = 1 := by
  haveI : Fact a.Prime := ⟨ha⟩
  haveI : Fact b.Prime := ⟨hb⟩
  have ha5 := five_le_of_mod_four_eq_one ha ha4
  have hbodd : b % 2 = 1 := Nat.odd_iff.mp (hb.odd_of_ne_two hb2)
  have ha0 : ((a : ℕ) : ZMod b) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => hne ((Nat.prime_dvd_prime_iff_eq hb ha).mp hd).symm
  have hb0 : ((b : ℕ) : ZMod a) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => hne ((Nat.prime_dvd_prime_iff_eq ha hb).mp hd)
  have hsq : IsSquare ((a : ZMod b)) := by
    refine (ZMod.euler_criterion b ha0).mpr ?_
    have hhalf : b / 2 = (b - 1) / 2 := by omega
    rw [hhalf]
    exact h
  have hres := (ZMod.euler_criterion a hb0).mp (isSquare_natCast_swap ha hb ha4 hb2 hne hsq)
  have hhalf : (a - 1) / 2 = a / 2 := by omega
  rw [hhalf]
  exact hres

end InverseGalois.CFT
