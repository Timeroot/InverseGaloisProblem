/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The area mean value property of a holomorphic function

A holomorphic function is the average of its values on every circle around a point, and integrating
that statement over the radii turns it into the average of its values on every disc.  Read through
the triangle inequality, the resulting identity bounds the value of the function at the centre by
the integral of its absolute value, or — applying it to the square — of its square, over the disc:
a pointwise bound obtained from an integral one, which is what an `L²` theory needs.

## Main results

* `Rigidity.RET.integral_ball_of_diffContOnCl` — **the area mean value property**.
* `Rigidity.RET.norm_le_integral_ball` — the value at the centre is bounded by the integral of the
  absolute value over the disc.
* `Rigidity.RET.norm_sq_le_integral_ball` — and its square by the integral of the square.
-/

open MeasureTheory Metric Set

noncomputable section

namespace Rigidity.RET

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {F : ℂ → E} {c : ℂ} {r : ℝ}

/-! ### Polar coordinates and the circle map -/

/-- Polar coordinates around a centre are the circle map. -/
theorem add_polarCoord_symm_eq_circleMap (c : ℂ) (p : ℝ × ℝ) :
    c + Complex.polarCoord.symm p = circleMap c p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  push_cast
  ring

/-- The circle map lands at distance the radius from the centre. -/
theorem dist_circleMap_center (c : ℂ) (t θ : ℝ) : dist (circleMap c t θ) c = |t| :=
  circleMap_mem_sphere' c t θ

/-- The circle map is jointly continuous in the radius and the angle. -/
theorem continuous_circleMap_prod (c : ℂ) :
    Continuous fun p : ℝ × ℝ => circleMap c p.1 p.2 := by
  have h : (fun p : ℝ × ℝ => circleMap c p.1 p.2)
      = fun p : ℝ × ℝ => c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := rfl
  rw [h]
  fun_prop

/-! ### The area mean value property -/

/-- **The area mean value property of a holomorphic function**: the integral of a function
holomorphic on a disc and continuous on its closure is the area of the disc times the value at the
centre. -/
theorem integral_ball_of_diffContOnCl (hr : 0 < r) (hF : DiffContOnCl ℂ F (ball c r)) :
    ∫ z in ball c r, F z = (Real.pi * r ^ 2) • F c := by
  classical
  have hFcont : ContinuousOn F (closedBall c r) := hF.continuousOn_ball
  have hTmeas : MeasurableSet (Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hmapmem : ∀ p ∈ Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
      circleMap c p.1 p.2 ∈ ball c r := by
    rintro ⟨t, θ⟩ ⟨ht, _⟩
    rw [mem_ball, dist_circleMap_center, abs_of_pos ht.1]
    exact ht.2
  have hHcont : ContinuousOn (fun p : ℝ × ℝ => p.1 • F (circleMap c p.1 p.2))
      (Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi) := by
    refine continuous_fst.continuousOn.smul ?_
    exact hFcont.comp (continuous_circleMap_prod c).continuousOn fun p hp =>
      ball_subset_closedBall (hmapmem p hp)
  -- Step 1: pass to polar coordinates
  have hT : (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
  have hpolar0 := Complex.integral_comp_polarCoord_symm
    (fun w : ℂ => ((ball c r).indicator F) (c + w))
  have hpolar : (∫ p in polarCoord.target,
        p.1 • ((ball c r).indicator F) (c + Complex.polarCoord.symm p))
      = ∫ w : ℂ, ((ball c r).indicator F) (c + w) := hpolar0
  rw [hT] at hpolar
  have hstep1 : ∫ z in ball c r, F z
      = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • ((ball c r).indicator F) (c + Complex.polarCoord.symm p) := by
    rw [hpolar, integral_add_left_eq_self ((ball c r).indicator F) c,
      integral_indicator measurableSet_ball]
  -- Step 2: identify the integrand with the indicator of the polar region
  have hstep2 : (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • ((ball c r).indicator F) (c + Complex.polarCoord.symm p))
      = ∫ p in Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • F (circleMap c p.1 p.2) := by
    rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      (g := (Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi).indicator
        fun p : ℝ × ℝ => p.1 • F (circleMap c p.1 p.2)) ?_, setIntegral_indicator hTmeas,
      inter_eq_self_of_subset_right (prod_mono Ioo_subset_Ioi_self subset_rfl)]
    rintro ⟨t, θ⟩ ⟨ht, hθ⟩
    simp only [add_polarCoord_symm_eq_circleMap]
    by_cases hlt : t < r
    · have hmem : ((t, θ) : ℝ × ℝ) ∈ Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi := ⟨⟨ht, hlt⟩, hθ⟩
      rw [Set.indicator_of_mem hmem]
      congr 1
      refine Set.indicator_of_mem ?_ F
      rw [mem_ball, dist_circleMap_center, abs_of_pos ht]
      exact hlt
    · have hnmem : ((t, θ) : ℝ × ℝ) ∉ Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi := fun h => hlt h.1.2
      have hnb : circleMap c t θ ∉ ball c r := by
        rw [mem_ball, dist_circleMap_center, abs_of_pos ht]
        exact hlt
      rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnb, smul_zero]
  -- Step 3: Fubini
  have hSfin : (volume : Measure (ℝ × ℝ)) (Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi) < ⊤ :=
    lt_of_le_of_lt (measure_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
      ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)
  obtain ⟨M, hM⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hFcont
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 • F (circleMap c p.1 p.2))
      (Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi) volume := by
    refine ⟨hHcont.aestronglyMeasurable hTmeas,
      HasFiniteIntegral.restrict_of_bounded (C := r * M) hSfin ?_⟩
    filter_upwards [ae_restrict_mem hTmeas] with p hp
    show ‖p.1 • F (circleMap c p.1 p.2)‖ ≤ r * M
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp.1.1]
    exact mul_le_mul hp.1.2.le (hM _ (ball_subset_closedBall (hmapmem p hp))) (norm_nonneg _) hr.le
  have hstep3 : (∫ p in Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • F (circleMap c p.1 p.2))
      = ∫ t in Ioo (0 : ℝ) r, ∫ θ in Ioo (-Real.pi) Real.pi, t • F (circleMap c t θ) := by
    rw [Measure.volume_eq_prod ℝ ℝ] at hint ⊢
    exact setIntegral_prod _ hint
  -- Step 4: the inner integral is the circle average
  have hinner : ∀ t ∈ Ioo (0 : ℝ) r,
      (∫ θ in Ioo (-Real.pi) Real.pi, t • F (circleMap c t θ))
        = (t * (2 * Real.pi)) • F c := by
    intro t ht
    have hper : Function.Periodic (fun θ => F (circleMap c t θ)) (2 * Real.pi) :=
      fun θ => congrArg F (periodic_circleMap c t θ)
    have hball : DiffContOnCl ℂ F (ball c |t|) := by
      rw [abs_of_pos ht.1]
      exact hF.mono (ball_subset_ball ht.2.le)
    have havg : Real.circleAverage F c t = F c := hball.circleAverage
    have h1 : (∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap c t θ))
        = ∫ θ in (-Real.pi)..Real.pi, F (circleMap c t θ) := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have h2 : (∫ θ in (-Real.pi)..Real.pi, F (circleMap c t θ))
        = ∫ θ in (0 : ℝ)..(2 * Real.pi), F (circleMap c t θ) := by
      have h := hper.intervalIntegral_add_eq (-Real.pi) 0
      rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at h
      exact h
    have h3 : (∫ θ in (0 : ℝ)..(2 * Real.pi), F (circleMap c t θ)) = (2 * Real.pi) • F c := by
      rw [← havg, Real.circleAverage_def, smul_inv_smul₀ (by positivity)]
    calc (∫ θ in Ioo (-Real.pi) Real.pi, t • F (circleMap c t θ))
        = t • ∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap c t θ) := integral_smul _ _
      _ = t • ((2 * Real.pi) • F c) := by rw [h1, h2, h3]
      _ = (t * (2 * Real.pi)) • F c := by rw [smul_smul]
  -- Step 5: the outer integral
  rw [hstep1, hstep2, hstep3,
    setIntegral_congr_fun measurableSet_Ioo (g := fun t => (t * (2 * Real.pi)) • F c) hinner,
    integral_smul_const]
  congr 1
  rw [integral_mul_const, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hr.le, integral_id]
  ring

/-! ### The bounds -/

/-- **The value of a holomorphic function at the centre of a disc is bounded by the integral of its
absolute value over the disc.** -/
theorem norm_le_integral_ball (hr : 0 < r) (hF : DiffContOnCl ℂ F (ball c r)) :
    (Real.pi * r ^ 2) * ‖F c‖ ≤ ∫ z in ball c r, ‖F z‖ := by
  have h : ‖∫ z in ball c r, F z‖ ≤ ∫ z in ball c r, ‖F z‖ := norm_integral_le_integral_norm _
  rwa [integral_ball_of_diffContOnCl hr hF, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi * r ^ 2)] at h

/-- **The square of the value of a holomorphic function at the centre of a disc is bounded by the
integral of the square of its absolute value over the disc.** -/
theorem norm_sq_le_integral_ball {F : ℂ → ℂ} (hr : 0 < r) (hF : DiffContOnCl ℂ F (ball c r)) :
    (Real.pi * r ^ 2) * ‖F c‖ ^ 2 ≤ ∫ z in ball c r, ‖F z‖ ^ 2 := by
  have hsq : DiffContOnCl ℂ (fun z => F z * F z) (ball c r) :=
    ⟨hF.differentiableOn.mul hF.differentiableOn, hF.continuousOn.mul hF.continuousOn⟩
  have h := norm_le_integral_ball hr hsq
  rw [norm_mul, ← pow_two] at h
  refine h.trans_eq (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
  show ‖F z * F z‖ = ‖F z‖ ^ 2
  rw [norm_mul, ← pow_two]

end Rigidity.RET

end
