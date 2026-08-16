/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# An entire function of polynomial growth is a polynomial

Liouville's theorem says a bounded entire function is constant.  The same argument, run with
Cauchy's estimate for the higher derivatives instead of the first, says more: if an entire function
grows no faster than `‖z‖ ^ m`, its derivatives of order above `m` all vanish at the origin, because
Cauchy's estimate bounds the `n`-th of them by `n! · A · R ^ (m - n)` on every circle of radius `R`,
and that tends to `0`.  An entire function is the sum of its Taylor series, so the series breaks off
and the function is a polynomial of degree at most `m`.

This is the form of Liouville's theorem needed to recognise a rational function: an analytic
function on the plane with finitely many punctures, meromorphic at each of them and of moderate
growth at infinity, becomes an entire function of polynomial growth once its poles are cleared.

## Main results

* `Rigidity.RET.iteratedDeriv_eq_zero_of_growth` — the derivatives of order above `m` of an entire
  function of growth `‖z‖ ^ m` vanish at the origin.
* `Rigidity.RET.exists_polynomial_of_growth` — such a function is a polynomial of degree at
  most `m`.
* `Rigidity.RET.norm_eval_le_of_one_le` — a polynomial grows no faster than a constant times a
  power of its degree.
-/

open Metric

noncomputable section

namespace Rigidity.RET

/-- A power with base at least one grows with its exponent. -/
theorem pow_le_pow_of_one_le_of_le {r : ℝ} (hr : 1 ≤ r) {j n : ℕ} (h : j ≤ n) : r ^ j ≤ r ^ n := by
  have h1 : (1 : ℝ) ≤ r ^ (n - j) := by simpa using pow_le_pow_left₀ zero_le_one hr (n - j)
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  calc r ^ j = r ^ j * 1 := (mul_one _).symm
    _ ≤ r ^ j * r ^ (n - j) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = r ^ (j + (n - j)) := (pow_add r j (n - j)).symm
    _ = r ^ n := by congr 1; omega

/-- **The high derivatives of an entire function of polynomial growth vanish**: if `f` grows no
faster than `A * ‖z‖ ^ m`, then its `n`-th derivative at the origin is zero for every `n > m`. -/
theorem iteratedDeriv_eq_zero_of_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A R₀ : ℝ}
    {m : ℕ} (hgrowth : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ A * ‖z‖ ^ m) {n : ℕ} (hn : m < n) :
    iteratedDeriv n f 0 = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
  set R : ℝ := max (max R₀ 1) (n.factorial * A / ε) with hR_def
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_right R₀ 1) (le_max_left _ _)
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hR₀ : R₀ ≤ R := le_trans (le_max_left R₀ 1) (le_max_left _ _)
  have hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ A * R ^ m := by
    intro z hz
    have hnz : ‖z‖ = R := by simpa using hz
    rw [← hnz]
    exact hgrowth z (hnz ▸ hR₀)
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := f) (c := 0) n hR0 hf.diffContOnCl hbound
  refine hcauchy.trans ?_
  have hRm : (R : ℝ) ^ m ≠ 0 := by positivity
  have hsplit : (R : ℝ) ^ n = R ^ m * R ^ (n - m) := by
    rw [← pow_add]
    congr 1
    omega
  have hge : R ≤ R ^ (n - m) := by
    simpa using pow_le_pow_of_one_le_of_le hR1 (show 1 ≤ n - m by omega)
  have key : (n.factorial : ℝ) * (A * R ^ m) / R ^ n = n.factorial * A / R ^ (n - m) := by
    rw [hsplit]
    field_simp
  rw [key, div_le_iff₀ (by positivity : (0 : ℝ) < R ^ (n - m))]
  have hRge : (n.factorial : ℝ) * A / ε ≤ R := le_max_right _ _
  rw [div_le_iff₀ hε] at hRge
  calc (n.factorial : ℝ) * A ≤ ε * R := by linarith
    _ ≤ ε * R ^ (n - m) := mul_le_mul_of_nonneg_left hge hε.le

/-- **An entire function of polynomial growth is a polynomial**: if `f` grows no faster than
`A * ‖z‖ ^ m`, it agrees everywhere with a polynomial of degree at most `m`. -/
theorem exists_polynomial_of_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A R₀ : ℝ}
    {m : ℕ} (hgrowth : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ A * ‖z‖ ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z, f z = p.eval z := by
  refine ⟨∑ n ∈ Finset.range (m + 1),
    Polynomial.C ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0) * Polynomial.X ^ n, ?_, fun z => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_X_pow]
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  · have hsum := Complex.taylorSeries_eq_of_entire' (c := 0) (z := z) hf
    rw [← hsum, tsum_eq_sum (s := Finset.range (m + 1)) ?_]
    · simp [Polynomial.eval_finset_sum]
    · intro n hn
      rw [iteratedDeriv_eq_zero_of_growth hf hgrowth
        (by simpa [Nat.lt_succ_iff] using hn : m < n)]
      ring

/-- **A polynomial grows no faster than a power of its degree** times the sum of the norms of its
coefficients, outside the unit disc. -/
theorem norm_eval_le_of_one_le (p : Polynomial ℂ) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖p.eval z‖ ≤ (∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖) * ‖z‖ ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_one_le_of_le hz (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))) (norm_nonneg _)

end Rigidity.RET

end
