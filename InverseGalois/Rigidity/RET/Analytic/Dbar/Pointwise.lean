/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverChart
import InverseGalois.Rigidity.RET.Analytic.Dbar.AreaMean

/-!
# From an integral bound to a pointwise bound

A solution of the Cauchy–Riemann equation is produced as an element of a weighted `L²` space, and
what is known of it is the size of its integral.  Where the source of the equation vanishes the
solution is holomorphic, and there the mean value property converts the integral bound into a
bound on the value at a point: the value at the centre of a disc is controlled by the integral
over the disc, the integral over the disc is controlled by the weighted integral over the sheet
above it, and that in turn by the norm of the element.  The bound obtained degrades as the disc
shrinks, and it is the size of the available disc that will govern the growth of the solution.

## Main results

* `Rigidity.RET.integral_norm_sq_Lp` — the square norm of an element of `L²` is the integral of
  the square of its absolute value.
* `Rigidity.RET.norm_sq_le_of_holo_ball` — **the pointwise bound**: at the centre of a disc over
  which the solution is holomorphic, its value is bounded by the norm of the element divided by
  the area of the disc.
-/

open MeasureTheory Metric Filter Topology

noncomputable section

namespace Rigidity.RET

/-! ### The square norm of an element of `L²` -/

section L2Norm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **The square norm of an element of `L²` is the integral of the square of its absolute
value.** -/
theorem integral_norm_sq_Lp (U : Lp ℂ 2 μ) : ∫ a, ‖(U : α → ℂ) a‖ ^ 2 ∂μ = ‖U‖ ^ 2 := by
  have h1 : (inner ℂ U U : ℂ) = ∫ a, ((‖(U : α → ℂ) a‖ ^ 2 : ℝ) : ℂ) ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show (inner ℂ ((U : α → ℂ) a) ((U : α → ℂ) a) : ℂ) = ((‖(U : α → ℂ) a‖ ^ 2 : ℝ) : ℂ)
    rw [RCLike.inner_apply, Complex.sq_norm, Complex.mul_conj]
  have hofReal : ∫ a, ((‖(U : α → ℂ) a‖ ^ 2 : ℝ) : ℂ) ∂μ
      = ((∫ a, ‖(U : α → ℂ) a‖ ^ 2 ∂μ : ℝ) : ℂ) := integral_ofReal
  have h2 : (inner ℂ U U : ℂ) = ((‖U‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hofReal, h2] at h1
  exact (Complex.ofReal_inj.mp h1).symm

/-- The square of the absolute value of an element of `L²` is integrable. -/
theorem integrable_norm_sq_Lp (U : Lp ℂ 2 μ) : Integrable (fun a => ‖(U : α → ℂ) a‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable U)).mp (Lp.memLp U)

/-- **The integral of the square of the absolute value of an element of `L²` over a part of the
space** is bounded by its square norm. -/
theorem setIntegral_norm_sq_Lp_le (U : Lp ℂ 2 μ) (s : Set α) :
    ∫ a in s, ‖(U : α → ℂ) a‖ ^ 2 ∂μ ≤ ‖U‖ ^ 2 := by
  rw [← integral_norm_sq_Lp U]
  exact setIntegral_le_integral (integrable_norm_sq_Lp U)
    (Filter.Eventually.of_forall fun a => by positivity)

end L2Norm

/-! ### The pointwise bound -/

section Bound

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {Φ : ℂ → ℂ}
  (hfin : ∀ z, (f ⁻¹' {z}).Finite)
  (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
  (hΦc : Continuous Φ)
  [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **The pointwise bound.**  Over a disc on which the solution is holomorphic, the value at the
centre is bounded by the square norm of the element of `L²` that the solution represents, divided
by the area of the disc and multiplied by a bound for the reciprocal of the weight. -/
theorem norm_sq_le_of_holo_ball
    {U : Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦc)} {u : Y → ℂ}
    {e : OpenPartialHomeomorph Y ℂ} (hfe : f = ⇑e) {c : ℂ} {R r K : ℝ}
    (hr : 0 < r) (hrR : r < R) (hball : ball c R ⊆ e.target)
    (hholo : ∀ z ∈ ball c R, DifferentiableAt ℂ (fun t : ℂ => u (e.symm t)) z)
    (hae : ∀ᵐ z : ℂ, z ∈ ball c R → (U : Y → ℂ) (e.symm z) = u (e.symm z))
    (hK : ∀ z ∈ ball c r, 1 ≤ K * weightOf Φ z) :
    (Real.pi * r ^ 2) * ‖u (e.symm c)‖ ^ 2 ≤ K * ‖U‖ ^ 2 := by
  set G : ℂ → ℂ := fun t : ℂ => u (e.symm t) with hGdef
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hGcont : ContinuousOn G (closedBall c r) := fun z hz =>
    ((hholo z (hsub hz)).continuousAt.continuousWithinAt)
  -- the mean value bound
  have hdcc : DiffContOnCl ℂ G (ball c r) := by
    refine ⟨fun z hz => (hholo z (hsub (ball_subset_closedBall hz))).differentiableWithinAt, ?_⟩
    rw [closure_ball c hr.ne']
    exact hGcont
  have h1 : (Real.pi * r ^ 2) * ‖G c‖ ^ 2 ≤ ∫ z in ball c r, ‖G z‖ ^ 2 :=
    norm_sq_le_integral_ball hr hdcc
  -- the weight is bounded below on the disc
  have hint1 : IntegrableOn (fun z => ‖G z‖ ^ 2) (ball c r) volume :=
    ((hGcont.norm.pow 2).integrableOn_compact (isCompact_closedBall c r)).mono_set
      ball_subset_closedBall
  have hint2 : IntegrableOn (fun z => K * (weightOf Φ z * ‖G z‖ ^ 2)) (ball c r) volume :=
    ((continuousOn_const.mul
      (((continuous_weightOf hΦc).continuousOn).mul (hGcont.norm.pow 2))).integrableOn_compact
        (isCompact_closedBall c r)).mono_set ball_subset_closedBall
  have h2 : ∫ z in ball c r, ‖G z‖ ^ 2 ≤ ∫ z in ball c r, K * (weightOf Φ z * ‖G z‖ ^ 2) := by
    refine setIntegral_mono_on hint1 hint2 measurableSet_ball fun z hz => ?_
    nlinarith [hK z hz, sq_nonneg ‖G z‖]
  -- the weighted integral over the disc is the integral over the sheet
  have hballr : closedBall c r ⊆ e.target := hsub.trans hball
  have hae' : ∀ᵐ z : ℂ, z ∈ ball c r → (U : Y → ℂ) (e.symm z) = G z := by
    filter_upwards [hae] with z hz hzr
    exact hz (ball_subset_ball hrR.le hzr)
  have hmeas : AEStronglyMeasurable (fun z => ‖(U : Y → ℂ) (e.symm z)‖ ^ 2)
      (volume.restrict (ball c r)) := by
    refine AEStronglyMeasurable.congr
      ((hGcont.mono ball_subset_closedBall).norm.pow 2 |>.aestronglyMeasurable
        measurableSet_ball) ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
    filter_upwards [hae'] with z hz hzr
    rw [hz hzr]
  have h3 : ∫ y in sheet f e c r, ‖(U : Y → ℂ) y‖ ^ 2 ∂(coverL2Measure f Φ hfin hcov hf hΦc)
      = ∫ z in ball c r, weightOf Φ z • ‖(U : Y → ℂ) (e.symm z)‖ ^ 2 :=
    integral_weightMeasure_sheet hfin hcov hf (continuous_weightOf hΦc)
      (fun z => (weightOf_pos Φ z).le) hfe hballr hmeas
  have h4 : ∫ z in ball c r, weightOf Φ z • ‖(U : Y → ℂ) (e.symm z)‖ ^ 2
      = ∫ z in ball c r, weightOf Φ z * ‖G z‖ ^ 2 := by
    refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [hae'] with z hz hzr
    rw [hz hzr, smul_eq_mul]
  have hKpos : 0 < K := by
    nlinarith [hK c (mem_ball_self hr), weightOf_pos Φ c]
  have h5 : ∫ z in ball c r, weightOf Φ z * ‖G z‖ ^ 2 ≤ ‖U‖ ^ 2 := by
    rw [← h4, ← h3]
    exact setIntegral_norm_sq_Lp_le U _
  calc (Real.pi * r ^ 2) * ‖G c‖ ^ 2 ≤ ∫ z in ball c r, ‖G z‖ ^ 2 := h1
    _ ≤ ∫ z in ball c r, K * (weightOf Φ z * ‖G z‖ ^ 2) := h2
    _ = K * ∫ z in ball c r, weightOf Φ z * ‖G z‖ ^ 2 := integral_const_mul _ _
    _ ≤ K * ‖U‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left h5 hKpos.le

end Bound

end Rigidity.RET

end
