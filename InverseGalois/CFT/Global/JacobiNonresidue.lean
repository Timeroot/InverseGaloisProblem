/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Nonresidues modulo arbitrarily large primes

A squarefree integer different from `1` is a quadratic nonresidue modulo infinitely many
primes.  The proof combines Dirichlet's theorem on primes in arithmetic progressions with
quadratic reciprocity for the Jacobi symbol.

## Main results

* `InverseGalois.CFT.exists_prime_jacobiSym_eq_neg_one`: for a squarefree integer `m ≠ 1`
  and any bound `N` there is a prime `q > N` with `jacobiSym m q = -1`.
-/

namespace InverseGalois.CFT

/-- A squarefree natural number factors as a power of `2` with exponent at most one times an
odd squarefree natural number. -/
theorem exists_two_pow_mul_odd_of_squarefree {a : ℕ} (ha : Squarefree a) :
    ∃ e u : ℕ, e ≤ 1 ∧ Odd u ∧ Squarefree u ∧ a = 2 ^ e * u := by
  by_cases h2 : 2 ∣ a
  · obtain ⟨u, rfl⟩ := h2
    have hu2 : ¬ (2 ∣ u) := by
      rintro ⟨v, rfl⟩
      have h := ha 2 ⟨v, by ring⟩
      simp at h
    exact ⟨1, u, le_rfl, Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hu2),
      ha.squarefree_of_dvd (dvd_mul_left u 2), by ring⟩
  · exact ⟨0, a, Nat.zero_le 1, Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2), ha,
      (one_mul a).symm⟩

/-- Every odd prime has a natural number that is a quadratic nonresidue modulo it. -/
theorem exists_nat_jacobiSym_prime_eq_neg_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ n : ℕ, jacobiSym n p = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hchar
  refine ⟨a.val, ?_⟩
  have hcast : (((a.val : ℕ) : ℤ) : ZMod p) = a := by
    push_cast
    simp
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  show quadraticChar (ZMod p) (((a.val : ℕ) : ℤ) : ZMod p) = -1
  rw [hcast, ha]

/-- An odd squarefree natural number greater than one has a quadratic nonresidue, that is, a
natural number whose Jacobi symbol against it is `-1`. -/
theorem exists_nat_jacobiSym_eq_neg_one {u : ℕ} (hodd : Odd u) (hsf : Squarefree u)
    (hu : 1 < u) : ∃ n : ℕ, jacobiSym n u = -1 := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hu.ne'
  obtain ⟨u', rfl⟩ := hpd
  obtain ⟨hcop, -, -⟩ := Nat.squarefree_mul_iff.mp hsf
  have hp2 : p ≠ 2 := hodd.ne_two_of_dvd_nat ⟨u', rfl⟩
  obtain ⟨n₀, hn₀⟩ := exists_nat_jacobiSym_prime_eq_neg_one hp hp2
  obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hcop n₀ 1
  have hu'ne : u' ≠ 0 := by rintro rfl; simp at hu
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero u' := ⟨hu'ne⟩
  refine ⟨n, ?_⟩
  have h1 : jacobiSym (n : ℤ) p = -1 := by
    rw [jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr hn1), hn₀]
  have h2 : jacobiSym (n : ℤ) u' = 1 := by
    rw [jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr hn2), Nat.cast_one, jacobiSym.one_left]
  rw [jacobiSym.mul_right (n : ℤ) p u', h1, h2, mul_one]

/-- Dirichlet's theorem in the form used below: given an odd modulus `u` and a residue `n`
coprime to `u`, there are arbitrarily large primes that are `1` modulo `8` and `n` modulo `u`. -/
theorem exists_prime_gt_one_mod_eight_and_modEq {u : ℕ} (hodd : Odd u) {n : ℕ}
    (hcop : Nat.Coprime n u) (N : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ q % 8 = 1 ∧ q ≡ n [MOD u] := by
  have hu : u ≠ 0 := by rintro rfl; simp at hodd
  have h8u : Nat.Coprime 8 u := by
    have h2 : Nat.Coprime 2 u := Nat.coprime_two_left.mpr hodd
    have := h2.pow_left 3
    norm_num at this
    exact this
  obtain ⟨c, hc8, hcu⟩ := Nat.chineseRemainder h8u 1 n
  have hcop8 : Nat.Coprime c 8 := by
    have h := hc8.gcd_eq
    simpa [Nat.Coprime] using h
  have hcopu : Nat.Coprime c u := by
    have h := hcu.gcd_eq
    rw [Nat.Coprime, h]
    exact hcop
  obtain ⟨q, hqN, hqp, hq⟩ := Nat.forall_exists_prime_gt_and_modEq N
    (Nat.mul_ne_zero (by norm_num) hu) (hcop8.mul_right hcopu)
  refine ⟨q, hqp, hqN, ?_, ?_⟩
  · have : q ≡ 1 [MOD 8] := (hq.of_dvd ⟨u, rfl⟩).trans hc8
    simpa [Nat.ModEq] using this
  · exact (hq.of_dvd ⟨8, mul_comm 8 u⟩).trans hcu

/-- There are arbitrarily large primes modulo which `-1` is a nonresidue. -/
theorem exists_prime_jacobiSym_neg_one_eq_neg_one (N : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ jacobiSym (-1) q = -1 := by
  obtain ⟨q, hqN, hqp, hq⟩ := Nat.forall_exists_prime_gt_and_modEq N (a := 3) (q := 8)
    (by norm_num) (by norm_num)
  have hq8 : q % 8 = 3 := by simpa [Nat.ModEq] using hq
  refine ⟨q, hqp, hqN, ?_⟩
  rw [jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
    ZMod.χ₄_nat_three_mod_four (by omega)]

/-- There are arbitrarily large primes modulo which `2` is a nonresidue. -/
theorem exists_prime_jacobiSym_two_eq_neg_one (N : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ jacobiSym 2 q = -1 := by
  obtain ⟨q, hqN, hqp, hq⟩ := Nat.forall_exists_prime_gt_and_modEq N (a := 3) (q := 8)
    (by norm_num) (by norm_num)
  have hq8 : q % 8 = 3 := by simpa [Nat.ModEq] using hq
  refine ⟨q, hqp, hqN, ?_⟩
  rw [jacobiSym.at_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈_nat_eq_if_mod_eight,
    if_neg (by omega), if_neg (by omega)]

/-- There are arbitrarily large primes modulo which `-2` is a nonresidue. -/
theorem exists_prime_jacobiSym_neg_two_eq_neg_one (N : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ jacobiSym (-2) q = -1 := by
  obtain ⟨q, hqN, hqp, hq⟩ := Nat.forall_exists_prime_gt_and_modEq N (a := 5) (q := 8)
    (by norm_num) (by norm_num)
  have hq8 : q % 8 = 5 := by simpa [Nat.ModEq] using hq
  refine ⟨q, hqp, hqN, ?_⟩
  rw [jacobiSym.at_neg_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈'_nat_eq_if_mod_eight,
    if_neg (by omega), if_neg (by omega)]

/-- A squarefree integer other than `1` is a quadratic nonresidue modulo arbitrarily large
primes. -/
theorem exists_prime_jacobiSym_eq_neg_one {m : ℤ} (hm : Squarefree m) (hm1 : m ≠ 1) (N : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ jacobiSym m q = -1 := by
  obtain ⟨e, u, he, huodd, husf, hmu⟩ :=
    exists_two_pow_mul_odd_of_squarefree (Int.squarefree_natAbs.mpr hm)
  have hu0 : u ≠ 0 := by rintro rfl; simp at huodd
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hu0) with hu1 | hu1
  · -- `u = 1`, so `m` is one of `-1`, `2`, `-2`
    have habs : m.natAbs = 2 ^ e := by rw [hmu, ← hu1, mul_one]
    have hm4 : m = 1 ∨ m = -1 ∨ m = 2 ∨ m = -2 := by
      interval_cases e <;> rw [habs] at * <;>
        rcases Int.natAbs_eq m with h | h <;> norm_num at h <;> omega
    rcases hm4 with rfl | rfl | rfl | rfl
    · exact absurd rfl hm1
    · exact exists_prime_jacobiSym_neg_one_eq_neg_one N
    · exact exists_prime_jacobiSym_two_eq_neg_one N
    · exact exists_prime_jacobiSym_neg_two_eq_neg_one N
  · -- `u > 1`
    obtain ⟨n, hn⟩ := exists_nat_jacobiSym_eq_neg_one huodd husf hu1
    haveI : NeZero u := ⟨hu0⟩
    have hcop : Nat.Coprime n u := by
      by_contra hc
      have h := jacobiSym.eq_zero_iff_not_coprime (a := (n : ℤ)) (b := u)
      rw [hn] at h
      simp only [Int.gcd_natCast_natCast, ne_eq] at h
      exact absurd (h.mpr hc) (by norm_num)
    obtain ⟨q, hqp, hqN, hq8, hqn⟩ := exists_prime_gt_one_mod_eight_and_modEq huodd hcop N
    refine ⟨q, hqp, hqN, ?_⟩
    have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
    have hχ₄ : jacobiSym (-1) q = 1 := by
      rw [jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_one_mod_four (by omega)]
    have hχ₈ : jacobiSym 2 q = 1 := by
      rw [jacobiSym.at_two hqodd, ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega),
        if_pos (by omega)]
    have hru : jacobiSym (u : ℤ) q = -1 := by
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' huodd (by omega),
        jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr hqn), hn]
    have hsplit : m = 1 * (2 ^ e * u) ∨ m = -1 * (2 ^ e * u) := by
      rcases Int.natAbs_eq m with h | h
      · left; rw [h, hmu]; push_cast; ring
      · right; rw [h, hmu]; push_cast; ring
    rcases hsplit with h | h <;> rw [h, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.pow_left, hru, hχ₈, one_pow]
    · rw [jacobiSym.one_left]; ring
    · rw [hχ₄]; ring

end InverseGalois.CFT
