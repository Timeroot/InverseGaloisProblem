/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.EntireGrowth

/-!
# A meromorphic function of moderate growth is rational

An analytic function on the plane with finitely many punctures, meromorphic at each of them, is
turned into an entire function by multiplying it by a polynomial with a high enough zero at every
puncture — that is what meromorphy at a point says.  Multiplying by a polynomial costs only a fixed
power of `‖z‖` at infinity, so if the function itself grew no faster than a power of `‖z‖`, neither
does the product; and an entire function of polynomial growth is a polynomial.

So the function is a quotient of two polynomials.  This is the analytic input that turns the
*analytic* coefficients of the equation satisfied by a function on a covering into *rational* ones,
and it is the reason the Riemann Existence Theorem produces an algebraic curve rather than merely a
Riemann surface.

## Main results

* `Rigidity.RET.exists_rational_of_meromorphic_of_growth` — a function analytic off a finite set,
  meromorphic on it, and of polynomial growth at infinity is a quotient of two polynomials.
-/

noncomputable section

namespace Rigidity.RET

open Polynomial

/-- **A function analytic off a finite set, meromorphic on it, and of polynomial growth at infinity
is rational.**

The denominator is a monic polynomial vanishing only on the finite set, and the identity
`q z * c z = p z` holds at *every* point of the plane. -/
theorem exists_rational_of_meromorphic_of_growth (S : Finset ℂ) {c : ℂ → ℂ}
    (hana : ∀ z ∉ S, AnalyticAt ℂ c z) (hmero : ∀ s ∈ S, MeromorphicAt c s)
    {A R₀ : ℝ} {m : ℕ} (hgrowth : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖c z‖ ≤ A * ‖z‖ ^ m) :
    ∃ p q : ℂ[X], q.Monic ∧ (∀ z ∉ S, q.eval z ≠ 0) ∧ ∀ z : ℂ, q.eval z * c z = p.eval z := by
  -- Every point is a point of meromorphy: off `S` the function is analytic.
  have hmero' : ∀ s : ℂ, MeromorphicAt c s := by
    intro s
    by_cases hs : s ∈ S
    · exact hmero s hs
    · exact (hana s hs).meromorphicAt
  choose n hn using hmero'
  -- The polynomial clearing all the poles.
  set q : ℂ[X] := ∏ s ∈ S, (X - C s) ^ n s with hq_def
  have hqmonic : q.Monic := monic_prod_of_monic _ _ fun s _ => (monic_X_sub_C s).pow _
  have hqeval : ∀ z : ℂ, q.eval z = ∏ s ∈ S, (z - s) ^ n s := by
    intro z
    rw [hq_def, eval_prod]
    exact Finset.prod_congr rfl fun s _ => by simp
  have hqne : ∀ z ∉ S, q.eval z ≠ 0 := by
    intro z hz
    rw [hqeval]
    exact Finset.prod_ne_zero_iff.2 fun s hs =>
      pow_ne_zero _ (sub_ne_zero.2 fun h => hz (h ▸ hs))
  -- Clearing the poles makes the function entire.
  have hpolyana : ∀ (r : ℂ[X]) (z : ℂ), AnalyticAt ℂ (fun w => r.eval w) z := fun r z =>
    AnalyticOnNhd.eval_polynomial r z (Set.mem_univ z)
  have hFana : ∀ z : ℂ, AnalyticAt ℂ (fun w => q.eval w * c w) z := by
    intro z
    by_cases hz : z ∈ S
    · have hfac : q = (X - C z) ^ n z * ∏ t ∈ S.erase z, (X - C t) ^ n t :=
        (Finset.mul_prod_erase S _ hz).symm
      have hrw : (fun w => q.eval w * c w)
          = fun w => (∏ t ∈ S.erase z, (X - C t) ^ n t).eval w * ((w - z) ^ n z • c w) := by
        funext w
        rw [hfac]
        simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]
        ring
      rw [hrw]
      exact (hpolyana _ z).mul (hn z)
    · exact (hpolyana q z).mul (hana z hz)
  -- Clearing the poles costs only a fixed power at infinity.
  have hFgrowth : ∀ z : ℂ, max R₀ 1 ≤ ‖z‖ →
      ‖q.eval z * c z‖
        ≤ ((∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖) * A) * ‖z‖ ^ (q.natDegree + m) := by
    intro z hz
    have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (le_max_right R₀ 1) hz
    have hzR : R₀ ≤ ‖z‖ := le_trans (le_max_left R₀ 1) hz
    rw [norm_mul]
    calc ‖q.eval z‖ * ‖c z‖
        ≤ ((∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖) * ‖z‖ ^ q.natDegree) *
            (A * ‖z‖ ^ m) :=
          mul_le_mul (norm_eval_le_of_one_le q hz1) (hgrowth z hzR) (norm_nonneg _)
            (by positivity)
      _ = ((∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖) * A) * ‖z‖ ^ (q.natDegree + m) := by
          rw [pow_add]
          ring
  obtain ⟨p, -, hp⟩ := exists_polynomial_of_growth
    (fun z => (hFana z).differentiableAt) hFgrowth
  exact ⟨p, q, hqmonic, hqne, fun z => hp z⟩

end Rigidity.RET

end
