/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The valuation of an integer in a valued field

An integer has valuation at most one in any valued ring, because the valuation of a sum is at most
the larger of the two valuations.  If a single prime `p` has valuation less than one, then every
integer prime to `p` has valuation exactly one, and the valuation of an arbitrary nonzero integer
is the valuation of `p` raised to the `p`-adic valuation of that integer.  Applied to a factorial
this turns Legendre's theorem into a bound on the valuation of `n !`, which is what makes the
exponential series converge on a small enough neighbourhood of zero.

## Main results

* `InverseGalois.CFT.valued_natCast_le_one`, `InverseGalois.CFT.valued_intCast_le_one`: an integer
  has valuation at most one.
* `InverseGalois.CFT.valued_natCast_eq_one_of_not_dvd`: an integer prime to `p` has valuation one.
* `InverseGalois.CFT.valued_natCast_eq_pow`: **the valuation of an integer is the valuation of `p`
  raised to its `p`-adic valuation.**
* `InverseGalois.CFT.valued_natCast_eq_exp`: the same, written additively.
* `InverseGalois.CFT.sub_one_mul_valFactorial_le`: **Legendre's bound on the valuation of a
  factorial.**

## Tags

valued field, valuation of an integer, Legendre's theorem, factorial
-/

namespace InverseGalois.CFT

open scoped WithZero

/-! ### Integers have valuation at most one -/

section Ring

variable {A : Type*} [Ring A] [Valued A ℤᵐ⁰]

/-- **A natural number has valuation at most one.**  Adding one increases the valuation by
nothing, because the valuation of a sum is at most the larger of the two valuations. -/
theorem valued_natCast_le_one (n : ℕ) : Valued.v (n : A) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    refine le_trans (Valuation.map_add Valued.v _ _) (max_le ih ?_)
    simp

/-- **An integer has valuation at most one.** -/
theorem valued_intCast_le_one (n : ℤ) : Valued.v (n : A) ≤ 1 := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using valued_natCast_le_one (A := A) m
  · simpa using valued_natCast_le_one (A := A) m

end Ring

/-! ### The valuation of an integer at a distinguished prime -/

section CommRing

variable {A : Type*} [CommRing A] [Valued A ℤᵐ⁰] {p : ℕ}

/-- **An integer prime to `p` has valuation one.**  A Bézout relation expresses one as a
combination of `p` and the integer, and the valuation of that combination is at most the larger of
the two valuations; were the integer to have valuation less than one, both would be less than
one. -/
theorem valued_natCast_eq_one_of_not_dvd (hp : p.Prime) (hpv : Valued.v (p : A) < 1) {n : ℕ}
    (h : ¬ p ∣ n) : Valued.v (n : A) = 1 := by
  refine le_antisymm (valued_natCast_le_one n) (not_lt.mp fun hlt => ?_)
  obtain ⟨a, b, hab⟩ :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
  have hcast : (a : A) * (p : A) + (b : A) * (n : A) = 1 := by
    have := congrArg (fun z : ℤ => (z : A)) hab
    push_cast at this
    exact this
  have hone : (1 : ℤᵐ⁰) ≤ max (Valued.v ((a : A) * (p : A))) (Valued.v ((b : A) * (n : A))) := by
    have h1 : Valued.v ((1 : A)) ≤ _ := hcast ▸ Valuation.map_add Valued.v _ _
    simpa using h1
  have ha : Valued.v ((a : A) * (p : A)) < 1 := by
    rw [Valuation.map_mul]
    calc Valued.v (a : A) * Valued.v (p : A) ≤ 1 * Valued.v (p : A) := by
          gcongr
          exact valued_intCast_le_one a
      _ < 1 := by rwa [one_mul]
  have hb : Valued.v ((b : A) * (n : A)) < 1 := by
    rw [Valuation.map_mul]
    calc Valued.v (b : A) * Valued.v (n : A) ≤ 1 * Valued.v (n : A) := by
          gcongr
          exact valued_intCast_le_one b
      _ < 1 := by rwa [one_mul]
  exact absurd hone (not_le.mpr (max_lt ha hb))

/-- **The valuation of a nonzero integer is the valuation of `p` raised to its `p`-adic
valuation.**  Splitting off the largest power of `p` leaves a cofactor prime to `p`, whose
valuation is one. -/
theorem valued_natCast_eq_pow (hp : p.Prime) (hpv : Valued.v (p : A) < 1) {n : ℕ} (hn : n ≠ 0) :
    Valued.v (n : A) = Valued.v (p : A) ^ padicValNat p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  set k := n.factorization p with hk
  have hsplit : p ^ k * (n / p ^ k) = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hfact : k = padicValNat p n := Nat.factorization_def n hp
  have hcop : ¬ p ∣ n / p ^ k := Nat.not_dvd_ordCompl hp hn
  calc Valued.v (n : A)
      = Valued.v ((p : A) ^ k * ((n / p ^ k : ℕ) : A)) := by
        rw [← Nat.cast_pow, ← Nat.cast_mul, hsplit]
    _ = Valued.v (p : A) ^ padicValNat p n := by
        rw [Valuation.map_mul, map_pow, valued_natCast_eq_one_of_not_dvd hp hpv hcop, mul_one,
          hfact]

variable {e : ℕ}

/-- **The valuation of a nonzero integer, written additively.** -/
theorem valued_natCast_eq_exp (hp : p.Prime) (he : 0 < e)
    (hpe : Valued.v (p : A) = WithZero.exp (-(e : ℤ))) {n : ℕ} (hn : n ≠ 0) :
    Valued.v (n : A) = WithZero.exp (-((e : ℤ) * padicValNat p n)) := by
  have hpv : Valued.v (p : A) < 1 := by
    rw [hpe]
    simpa using WithZero.exp_lt_exp.mpr (by omega : -(e : ℤ) < 0)
  rw [valued_natCast_eq_pow hp hpv hn, hpe, ← WithZero.exp_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  ring

/-- **Legendre's bound on the valuation of a factorial.**  Taking `p - 1` times the `p`-adic
valuation of `n !` gives `n` minus the sum of the base `p` digits of `n`, which is less than
`n`. -/
theorem sub_one_mul_valFactorial_le (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    ((p : ℤ) - 1) * padicValNat p n.factorial ≤ (n : ℤ) - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn
  have hp1 : 1 ≤ p := hp.one_lt.le
  have : ((p - 1 : ℕ) : ℤ) * padicValNat p n.factorial < (n : ℤ) := by exact_mod_cast h
  rw [Nat.cast_sub hp1] at this
  push_cast at this ⊢
  omega

end CommRing

end InverseGalois.CFT
