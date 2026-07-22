/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# General analytic infrastructure for the convergent Laurent / Puiseux tail bound

This file collects *general* (setup-independent) analytic facts used to prove
`DorgeBauer.convergent_laurent_tail_bound` in `InverseGalois/Hilbert/Analytic/PuiseuxTail.lean`:

* `analytic_taylor_remainder_bound` — Taylor expansion with an analytic (hence locally
  bounded) remainder, in the scalar complex case.
* `iteratedDeriv_im_zero_of_real_on_pos` — a Schwarz-reflection style fact: an analytic
  function on a disk centred at `0` that is real on the positive real segment `(0, r)` has
  real Taylor coefficients at `0`.
-/

open scoped BigOperators
open Filter Topology

namespace DorgeBauer

/-
**Taylor expansion with an analytic remainder (scalar complex case).**

If `G` is analytic at `0`, then for every order `n` there is a radius `δ > 0`, a bound
`M ≥ 0`, and a function `R` such that on `ball 0 δ` we have the Taylor identity
`G w = ∑_{m<n} (D^m G 0 / m!) wᵐ + wⁿ · R w` and `‖R w‖ ≤ M`.
-/
theorem analytic_taylor_remainder_bound (G : ℂ → ℂ) (hG : AnalyticAt ℂ G 0) (n : ℕ) :
    ∃ (R : ℂ → ℂ) (δ M : ℝ), 0 < δ ∧ 0 ≤ M ∧
      (∀ w : ℂ, ‖w‖ < δ →
        G w = (∑ m ∈ Finset.range n, (iteratedDeriv m G 0 / (m.factorial : ℂ)) * w ^ m)
          + w ^ n * R w) ∧
      (∀ w : ℂ, ‖w‖ < δ → ‖R w‖ ≤ M) := by
  obtain ⟨F, hF₁, hF₂⟩ := hG.exists_eventuallyEq_sum_add_pow_mul n
  -- Set `R := F`. Since `F` is analytic at `0` it is continuous at `0` (`AnalyticAt.continuousAt`), so it is bounded near `0`: there is `δ₁>0` with `‖F w‖ ≤ ‖F 0‖ + 1` for `‖w‖ < δ₁` (from `Metric.continuousAt_iff` / `ContinuousAt` giving eventually `‖F w - F 0‖ < 1`).
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ w, ‖w‖ < δ₁ → ‖F w‖ ≤ ‖F 0‖ + 1 := by
    have := Metric.continuousAt_iff.mp hF₁.continuousAt 1 zero_lt_one
    refine ⟨this.choose, this.choose_spec.1, fun w hw ↦ ?_⟩
    have := this.choose_spec.2 (show dist w 0 < this.choose by simpa using hw)
    have hmem : F w ∈ Metric.closedBall (F 0) 1 := by simpa [dist_eq_norm] using this.le
    exact norm_le_of_mem_closedBall hmem
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.eventually_nhds_iff.mp hF₂
  refine ⟨F, min δ₁ δ₂, ‖F 0‖ + 1, lt_min hδ₁_pos hδ₂_pos, by positivity, ?_, ?_⟩
  · simp_all [div_eq_inv_mul, mul_assoc, mul_comm]
  · simp_all [div_eq_inv_mul, mul_assoc, mul_comm]

/-
**Real Taylor coefficients from reality on the positive real segment.**

If `G` is analytic on `ball 0 r` and takes real values on the segment `(0, r) ⊆ ℝ`, then all
its Taylor coefficients at `0` are real (their imaginary parts vanish).
-/
theorem iteratedDeriv_im_zero_of_real_on_pos (G : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hG : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) r))
    (hreal : ∀ t : ℝ, 0 < t → t < r → (G (t : ℂ)).im = 0) (m : ℕ) :
    (iteratedDeriv m G 0).im = 0 := by
  -- From `G = G'` on the ball we get, by taking `m`-th iterated derivatives at `0`: `iteratedDeriv m G 0 = iteratedDeriv m G' 0 = conj (iteratedDeriv m G 0)` (conjugation commutes with derivative and the conjugate-point substitution contributes `conj` factors that cancel because we evaluate at `0` which is real, `conj 0 = 0`).
  have h_conj_tendsto : Filter.Tendsto (fun t : ℂ ↦ starRingEnd ℂ t) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε a
    simp_all only [gt_iff_lt, Set.mem_compl_iff, Set.mem_singleton_iff, dist_zero_right,
      map_eq_zero, not_false_eq_true, RCLike.norm_conj, true_and]
    exact ⟨ε, a, fun _ _ hx ↦ hx⟩
  have h_eq : ∀ m, iteratedDeriv m G 0 = starRingEnd ℂ (iteratedDeriv m G 0) := by
    have h_conj_eq : ∀ w ∈ Metric.ball 0 r, starRingEnd ℂ (G (starRingEnd ℂ w)) = G w := by
      -- By the identity theorem for analytic functions, since G and its conjugate agree on the segment (0, r), they must be equal on the entire ball.
      have h_analytic : AnalyticOnNhd ℂ (fun w ↦ (starRingEnd ℂ) (G (starRingEnd ℂ w)))
          (Metric.ball 0 r) := by
        apply DifferentiableOn.analyticOnNhd
        · intro w hw
          have := hG (starRingEnd ℂ w)
          simp_all only [Metric.mem_ball, dist_zero_right, RCLike.norm_conj, forall_const]
          have h_diff : HasDerivAt (fun w ↦ starRingEnd ℂ (G (starRingEnd ℂ w)))
              (starRingEnd ℂ (deriv G (starRingEnd ℂ w))) w := by
            rw [hasDerivAt_iff_tendsto_slope_zero]
            have := this.differentiableAt.hasDerivAt.tendsto_slope_zero
            convert Complex.continuous_conj.continuousAt.tendsto.comp
              (this.comp h_conj_tendsto) using 2
            norm_num
          exact h_diff.differentiableAt.differentiableWithinAt
        · exact Metric.isOpen_ball
      apply h_analytic.eqOn_of_preconnected_of_frequently_eq
      any_goals exact (r / 2 : ℂ)
      · assumption
      · exact (convex_ball _ _).isPreconnected
      · norm_num [abs_of_pos hr, hr]
      · rw [Metric.nhdsWithin_basis_ball.frequently_iff]
        intro ε ε_pos
        use (r / 2 : ℂ) + min ε (r / 2) / 2
        norm_num [Complex.ext_iff, hr.ne']
        erw [Complex.conj_ofReal]
        norm_num
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [abs_of_nonneg (by positivity)]
          linarith [min_le_left ε (r / 2), min_le_right ε (r / 2)]
        · positivity
        · have := hreal (r / 2 + min ε (r / 2) / 2) (by positivity)
            (by linarith [min_le_left ε (r / 2), min_le_right ε (r / 2)])
          norm_num [Complex.ext_iff] at *
          linarith
    -- Apply the fact that the derivative of a composition is the composition of the derivatives.
    have h_deriv_comp : ∀ m, iteratedDeriv m (fun w ↦ starRingEnd ℂ (G (starRingEnd ℂ w))) 0
        = starRingEnd ℂ (iteratedDeriv m G 0) := by
      intro m
      have h_deriv_comp_ball : ∀ w ∈ Metric.ball 0 r,
          iteratedDeriv m (fun w ↦ starRingEnd ℂ (G (starRingEnd ℂ w))) w
            = starRingEnd ℂ (iteratedDeriv m G (starRingEnd ℂ w)) := by
        induction' m with m ih
        · intro w hw
          simp [iteratedDeriv_zero]
        · intro w hw
          rw [iteratedDeriv_succ, iteratedDeriv_succ]
          convert HasDerivAt.deriv (HasDerivAt.congr_of_eventuallyEq _ <|
            Filter.eventuallyEq_of_mem (IsOpen.mem_nhds (Metric.isOpen_ball) hw) ih)
            using 1
          have h_deriv : HasDerivAt (iteratedDeriv m G) (deriv (iteratedDeriv m G) (starRingEnd ℂ w))
              (starRingEnd ℂ w) := by
            have h_analytic_deriv : AnalyticOnNhd ℂ (iteratedDeriv m G) (Metric.ball 0 r) := by
              refine Nat.recOn m ?_ ?_ <;> simp_all [iteratedDeriv_succ]
              exact fun n hn ↦ hn.deriv
            exact (h_analytic_deriv.differentiableOn.differentiableAt
              (Metric.isOpen_ball.mem_nhds <| by simpa [Complex.norm_conj] using hw)).hasDerivAt
          rw [hasDerivAt_iff_tendsto_slope_zero] at *
          convert Complex.continuous_conj.continuousAt.tendsto.comp
            (h_deriv.comp h_conj_tendsto) using 2
          norm_num
      simpa using h_deriv_comp_ball 0 (Metric.mem_ball_self hr)
    intro m
    rw [← h_deriv_comp m, Filter.EventuallyEq.iteratedDeriv_eq]
    filter_upwards [Metric.ball_mem_nhds 0 hr] with w hw
    exact (h_conj_eq w hw).symm
  specialize h_eq m
  norm_num [Complex.ext_iff] at h_eq
  linarith

end DorgeBauer