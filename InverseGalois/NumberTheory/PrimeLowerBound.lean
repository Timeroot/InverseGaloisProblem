/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A Chebyshev-type lower bound for the prime counting function

Mathlib contains Chebyshev's *upper* bounds for `θ`, `ψ` and the prime counting
function `π` (see `Mathlib.NumberTheory.Chebyshev`), but no matching lower bound.
This file supplies the classical *lower* bound: the number of primes up to `x` is
`≳ x / log x`.

We prove the classical central-binomial estimate of Chebyshev:

* `centralBinom_le_pow_primeCounting` : `centralBinom n ≤ (2n)^(π(2n))`,
  because every prime power dividing `centralBinom n` is `≤ 2n` and there are
  exactly `π(2n)` primes `≤ 2n`.
* `four_pow_lt_mul_pow_primeCounting` : combining with the lower bound
  `4^n < n · centralBinom n` gives `4^n < n · (2n)^(π(2n))`. -/

open Nat Finset
open scoped Nat.Prime

namespace HilbertPrimeLower

/-
The number of primes `≤ m` equals the cardinality of the prime filter of
`range (m + 1)`.
-/
lemma primeCounting_eq_card_filter (m : ℕ) :
    Nat.primeCounting m = ((Finset.range (m + 1)).filter Nat.Prime).card := by
  unfold _root_.Nat.primeCounting
  rw [Nat.primeCounting', Nat.count_eq_card_filter_range]

/-
**Chebyshev's central-binomial upper estimate.**
Every prime power `p ^ (centralBinom n).factorization p` dividing the central
binomial coefficient is at most `2n`, and only the (at most `π(2n)`) primes
`p ≤ 2n` occur, so `centralBinom n ≤ (2n)^(π(2n))`.
-/
theorem centralBinom_le_pow_primeCounting (n : ℕ) (hn : 1 ≤ n) :
    Nat.centralBinom n ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  -- Apply the lemma that bounds each term in the product.
  have h_prod_le :
      ∏ p ∈ (Finset.range (2 * n + 1)).filter Nat.Prime,
          p ^ (Nat.centralBinom n).factorization p ≤
        ∏ p ∈ (Finset.range (2 * n + 1)).filter Nat.Prime, 2 * n := by
    gcongr
    exact (Nat.pow_factorization_choose_le (by linarith)).trans (by linarith)
  convert h_prod_le using 1
  · conv_lhs => rw [← Nat.factorization_prod_pow_eq_self (Nat.ne_of_gt (Nat.centralBinom_pos _))]
    rw [Finsupp.prod_of_support_subset]
    · grind only [= subset_iff, = Finsupp.mem_support_iff, = mem_filter,
        factorization_centralBinom_eq_zero_of_two_mul_lt, factorization_eq_zero_iff,
        = mem_range]
    · grind
  · simp [primeCounting_eq_card_filter]

/-
**Chebyshev lower bound (multiplicative form).**
Combining `centralBinom_le_pow_primeCounting` with the lower bound
`4^n < n · centralBinom n` (`Nat.four_pow_lt_mul_centralBinom`) yields
`4^n < n · (2n)^(π(2n))`.
-/
theorem four_pow_lt_mul_pow_primeCounting (n : ℕ) (hn : 4 ≤ n) :
    4 ^ n < n * (2 * n) ^ Nat.primeCounting (2 * n) := by
  apply (Nat.four_pow_lt_mul_centralBinom n hn).trans_le
  exact Nat.mul_le_mul_left _ (centralBinom_le_pow_primeCounting _ (by linarith))

/-
**Chebyshev lower bound (analytic form).**
For `n ≥ 4` the number of primes up to `2n` satisfies `π(2n) ≥ n / (3 · log(2n))`.
This is obtained by taking logarithms in `four_pow_lt_mul_pow_primeCounting` and
using `n·log 4 - log n ≥ n/3`.
-/
theorem primeCounting_two_mul_ge (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) / (3 * Real.log (2 * n)) ≤ Nat.primeCounting (2 * n) := by
  -- By taking logarithms in `four_pow_lt_mul_pow_primeCounting n hn : 4^n < n * (2*n)^k`, we get `n * Real.log 4 < Real.log n + k * Real.log (2*n)`.
  have h_log : (n : ℝ) * Real.log 4 < Real.log n + (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * n) := by
    have h_log : (4 : ℝ) ^ n < n * (2 * n) ^ (Nat.primeCounting (2 * n)) := by
      exact_mod_cast four_pow_lt_mul_pow_primeCounting n hn
    simpa [Real.log_mul, show n ≠ 0 by linarith] using Real.log_lt_log (by positivity) h_log
  -- Now two elementary bounds:
  have h_log_4 : Real.log 4 ≥ 4 / 3 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    have := Real.log_two_gt_d9
    norm_num at *
    linarith
  have h_log_n : Real.log n ≤ n := by
    exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by norm_num)
  have h_n4 : (n : ℝ) ≥ 4 := by norm_cast
  have h_2n1 : (2 * n : ℝ) > 1 := by
    norm_cast
    linarith
  rw [div_le_iff₀] <;> nlinarith [h_n4, Real.log_pos h_2n1]

/-
**Chebyshev lower bound, general form.**
For every `m ≥ 8`, the number of primes up to `m` satisfies
`π(m) ≥ m / (7 · log m)`. Reduces to `primeCounting_two_mul_ge` via
`n = m / 2` and monotonicity of `π`.
-/
theorem primeCounting_ge (m : ℕ) (hm : 8 ≤ m) :
    (m : ℝ) / (7 * Real.log m) ≤ Nat.primeCounting m := by
  -- Set `n := m / 2` (natural division). Since `m ≥ 8`, `n ≥ 4`.
  set n := m / 2 with hn_def
  have hn_ge_4 : 4 ≤ n := by
    omega
  -- By `Nat.monotone_primeCounting` applied to `2*n ≤ m`, we get `(Nat.primeCounting (2*n) : ℝ) ≤ Nat.primeCounting m`.
  have h_monotone : (Nat.primeCounting (2 * n) : ℝ) ≤ Nat.primeCounting m := by
    exact_mod_cast Nat.monotone_primeCounting <| by omega
  -- By `primeCounting_two_mul_ge n (by omega : 4 ≤ n)`, `(n:ℝ)/(3 * Real.log (2*n)) ≤ Nat.primeCounting (2*n)`.
  have h_lower_bound : (n : ℝ) / (3 * Real.log (2 * n)) ≤ Nat.primeCounting (2 * n) :=
    primeCounting_two_mul_ge n hn_ge_4
  refine le_trans ?_ (h_lower_bound.trans h_monotone)
  rw [div_le_div_iff₀]
  · -- Using `Real.log (2*n) ≤ Real.log m` and `Real.log m > 0`, we get `3 * m * Real.log (2*n) ≤ 3 * m * Real.log m`.
    have h_log_ineq : Real.log (2 * n) ≤ Real.log m ∧ 0 < Real.log m := by
      refine ⟨Real.log_le_log (by positivity) ?_, Real.log_pos ?_⟩
      · norm_cast
        linarith [Nat.div_mul_le_self m 2]
      · norm_cast
        linarith
    have h_m_le : (m : ℝ) ≤ 2 * n + 1 := by
      norm_cast
      linarith [Nat.div_add_mod m 2, Nat.mod_lt m two_pos]
    have h_n4 : (n : ℝ) ≥ 4 := by norm_cast
    nlinarith [h_m_le, h_n4]
  · refine mul_pos (by norm_num) (Real.log_pos ?_)
    norm_cast
    linarith
  · refine mul_pos zero_lt_three (Real.log_pos ?_)
    norm_cast
    linarith

end HilbertPrimeLower
