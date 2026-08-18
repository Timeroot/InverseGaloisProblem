/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Basic

/-!
# Excising a point

To read the value of a weak solution of the Cauchy–Riemann equation at a point one wants to test it
against the Cauchy kernel `1/(w - z)`, which is not smooth there.  The remedy is to multiply the
kernel by a smooth cutoff which vanishes on a small disc about the point and is one outside a
slightly larger disc.  The resulting test function is genuinely smooth, and when the Cauchy–Riemann
operator is applied to it the singular factor cancels: the derivative of the annular cutoff is a
multiple of `w - z`, so dividing by `w - z` leaves a bounded density concentrated on the annulus.
Shrinking the annulus, that density is an approximate identity of total mass `π`.

## Main definitions

* `Rigidity.RET.sqDist` — the squared distance to a point.
* `Rigidity.RET.punctureCutoff` — the annular cutoff.
* `Rigidity.RET.punctureKernel` — the density produced by differentiating it.
* `Rigidity.RET.punctureTest` — the cut-off Cauchy kernel.

## Main results

* `Rigidity.RET.dbar_punctureCutoff` — differentiating the annular cutoff.
* `Rigidity.RET.dbar_punctureTest` — differentiating the cut-off Cauchy kernel.
-/

open MeasureTheory Metric ComplexConjugate

open scoped ContDiff

noncomputable section

namespace Rigidity.RET

/-! ### Elementary rules for the operator -/

variable {u : ℂ → ℂ} {z w : ℂ}

/-- The operator kills the constants. -/
theorem dbar_const (c : ℂ) (z : ℂ) : dbar (fun _ => c) z = 0 :=
  dbar_eq_zero (differentiableAt_const c)

/-- The operator is homogeneous. -/
theorem dbar_const_mul (c : ℂ) (hu : DifferentiableAt ℝ u z) :
    dbar (fun t => c * u t) z = c * dbar u z := by
  rw [dbar_mul (differentiableAt_const c) hu, dbar_const]
  ring

/-- The operator does not see an additive constant. -/
theorem dbar_add_const (c : ℂ) (hu : DifferentiableAt ℝ u z) :
    dbar (fun t => u t + c) z = dbar u z := by
  rw [dbar_add hu (differentiableAt_const c), dbar_const]
  ring

/-- **The chain rule through a real function.** -/
theorem dbar_comp_real {s : ℂ → ℝ} {ψ : ℝ → ℝ} {c : ℝ} (hs : DifferentiableAt ℝ s w)
    (hψ : HasDerivAt ψ c (s w)) :
    dbar (fun t => ((ψ (s t) : ℝ) : ℂ)) w = (c : ℂ) * dbar (fun t => ((s t : ℝ) : ℂ)) w := by
  have hS : HasFDerivAt (fun t : ℂ => ((s t : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ s w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w hs.hasFDerivAt
  have hcomp : HasFDerivAt (fun t : ℂ => ψ (s t)) (c • fderiv ℝ s w) w :=
    hψ.comp_hasFDerivAt w hs.hasFDerivAt
  have hP : HasFDerivAt (fun t : ℂ => ((ψ (s t) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (c • fderiv ℝ s w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w hcomp
  rw [dbar, dbar, hS.fderiv, hP.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

/-! ### The squared distance -/

/-- **The squared distance to a point.** -/
def sqDist (z w : ℂ) : ℝ := ‖w - z‖ ^ 2

theorem sqDist_nonneg (z w : ℂ) : 0 ≤ sqDist z w := by
  rw [sqDist]
  positivity

theorem sqDist_self (z : ℂ) : sqDist z z = 0 := by simp [sqDist]

/-- The squared distance is the product of a difference and its conjugate. -/
theorem ofReal_sqDist (z w : ℂ) : ((sqDist z w : ℝ) : ℂ) = (w - z) * conj (w - z) := by
  rw [sqDist, Complex.sq_norm, Complex.mul_conj]

theorem contDiff_sqDist (z : ℂ) : ContDiff ℝ ∞ (sqDist z) := by
  have h : sqDist z = fun w : ℂ => (w - z).re ^ 2 + (w - z).im ^ 2 := by
    funext w
    rw [sqDist, Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [h]
  exact ((Complex.reCLM.contDiff.comp (contDiff_id.sub contDiff_const)).pow 2).add
    ((Complex.imCLM.contDiff.comp (contDiff_id.sub contDiff_const)).pow 2)

theorem differentiable_sqDist (z : ℂ) : Differentiable ℝ (sqDist z) :=
  (contDiff_sqDist z).differentiable (by simp)

theorem differentiable_ofReal_sqDist (z : ℂ) :
    Differentiable ℝ fun t : ℂ => ((sqDist z t : ℝ) : ℂ) := fun t =>
  Complex.ofRealCLM.differentiableAt.comp t ((differentiable_sqDist z) t)

theorem differentiable_sub_const (z : ℂ) : Differentiable ℝ fun t : ℂ => t - z :=
  (differentiable_id (𝕜 := ℝ)).sub_const z

theorem differentiable_conj_sub (z : ℂ) : Differentiable ℝ fun t : ℂ => conj (t - z) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiable.comp (differentiable_sub_const z)

/-- The operator sends a difference of conjugates to one. -/
theorem dbar_conj_sub (z w : ℂ) : dbar (fun t => conj (t - z)) w = 1 := by
  have h1 : HasFDerivAt (fun t : ℂ => t - z) (ContinuousLinearMap.id ℝ ℂ) w := by
    simpa using (hasFDerivAt_id w).sub_const z
  have h2 := (Complex.conjCLE.hasFDerivAt (x := w - z)).comp w h1
  rw [ContinuousLinearMap.comp_id] at h2
  have hd : HasFDerivAt (fun t : ℂ => conj (t - z)) (Complex.conjCLE : ℂ →L[ℝ] ℂ) w := h2
  rw [dbar, hd.fderiv]
  simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I]
  rw [mul_neg, Complex.I_mul_I]
  ring

/-- **The operator applied to the squared distance.** -/
theorem dbar_ofReal_sqDist (z w : ℂ) : dbar (fun t => ((sqDist z t : ℝ) : ℂ)) w = w - z := by
  have hfun : (fun t : ℂ => ((sqDist z t : ℝ) : ℂ)) = fun t : ℂ => (t - z) * conj (t - z) :=
    funext (ofReal_sqDist z)
  have hu : DifferentiableAt ℝ (fun t : ℂ => t - z) w := differentiable_sub_const z w
  have hv : DifferentiableAt ℝ (fun t : ℂ => conj (t - z)) w := differentiable_conj_sub z w
  have hhol : dbar (fun t : ℂ => t - z) w = 0 := by
    refine dbar_eq_zero ?_
    fun_prop
  rw [hfun, dbar_mul hu hv, dbar_conj_sub, hhol]
  ring

/-! ### The transition profile -/

theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)

theorem hasDerivAt_smoothTransition (t : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
  ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) t).hasDerivAt

theorem deriv_smoothTransition_eq_zero_of_neg {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact Real.smoothTransition.zero_of_nonpos hx.le
  rw [h.deriv_eq, deriv_const]

theorem deriv_smoothTransition_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[nhds t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact Real.smoothTransition.one_of_one_le hx.le
  rw [h.deriv_eq, deriv_const]

/-- The derivative of the transition profile is bounded. -/
theorem exists_bound_deriv_smoothTransition :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_deriv_smoothTransition.continuousOn
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨M₀ + 1, by linarith, fun t => ?_⟩
  rcases lt_or_ge t 0 with h | h
  · rw [deriv_smoothTransition_eq_zero_of_neg h]
    simpa using by linarith
  rcases le_or_gt t 1 with h1 | h1
  · exact le_trans (hM₀ t ⟨h, h1⟩) (by linarith)
  · rw [deriv_smoothTransition_eq_zero_of_one_lt h1]
    simpa using by linarith

/-! ### The annular cutoff -/

variable {ε : ℝ}

/-- **The annular cutoff**: a smooth function which vanishes on the disc of radius `ε` about a
point and is one outside the disc of radius `2ε`. -/
def punctureCutoff (z : ℂ) (ε : ℝ) (w : ℂ) : ℝ :=
  Real.smoothTransition ((sqDist z w - ε ^ 2) / (3 * ε ^ 2))

/-- **The density produced by differentiating the annular cutoff.** -/
def punctureKernel (z : ℂ) (ε : ℝ) (w : ℂ) : ℝ :=
  deriv Real.smoothTransition ((sqDist z w - ε ^ 2) / (3 * ε ^ 2)) / (3 * ε ^ 2)

theorem punctureCutoff_nonneg (z : ℂ) (ε : ℝ) (w : ℂ) : 0 ≤ punctureCutoff z ε w :=
  Real.smoothTransition.nonneg _

theorem punctureCutoff_le_one (z : ℂ) (ε : ℝ) (w : ℂ) : punctureCutoff z ε w ≤ 1 :=
  Real.smoothTransition.le_one _

theorem norm_ofReal_punctureCutoff_le (z : ℂ) (ε : ℝ) (w : ℂ) :
    ‖((punctureCutoff z ε w : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (punctureCutoff_nonneg z ε w)]
  exact punctureCutoff_le_one z ε w

/-- The annular cutoff vanishes near the point. -/
theorem punctureCutoff_eq_zero (hε : 0 < ε) (hw : ‖w - z‖ ≤ ε) : punctureCutoff z ε w = 0 := by
  have h2 : (0 : ℝ) < 3 * ε ^ 2 := by positivity
  refine Real.smoothTransition.zero_of_nonpos ?_
  rw [div_le_iff₀ h2, zero_mul, sub_nonpos, sqDist]
  nlinarith [norm_nonneg (w - z)]

/-- The annular cutoff is one away from the point. -/
theorem punctureCutoff_eq_one (hε : 0 < ε) (hw : 2 * ε ≤ ‖w - z‖) : punctureCutoff z ε w = 1 := by
  have h2 : (0 : ℝ) < 3 * ε ^ 2 := by positivity
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ h2, sqDist]
  nlinarith [norm_nonneg (w - z)]

theorem contDiff_punctureCutoff (z : ℂ) (ε : ℝ) : ContDiff ℝ ∞ (punctureCutoff z ε) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    (((contDiff_sqDist z).sub contDiff_const).div_const _)

theorem continuous_punctureCutoff (z : ℂ) (ε : ℝ) : Continuous (punctureCutoff z ε) :=
  (contDiff_punctureCutoff z ε).continuous

theorem contDiff_ofReal_punctureCutoff (z : ℂ) (ε : ℝ) :
    ContDiff ℝ ∞ fun w : ℂ => ((punctureCutoff z ε w : ℝ) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_punctureCutoff z ε)

theorem differentiable_ofReal_punctureCutoff (z : ℂ) (ε : ℝ) :
    Differentiable ℝ fun w : ℂ => ((punctureCutoff z ε w : ℝ) : ℂ) :=
  (contDiff_ofReal_punctureCutoff z ε).differentiable (by simp)

/-! ### The density -/

theorem continuous_punctureKernel (z : ℂ) (ε : ℝ) : Continuous (punctureKernel z ε) :=
  (continuous_deriv_smoothTransition.comp
    (((contDiff_sqDist z).continuous.sub continuous_const).div_const _)).div_const _

/-- The density vanishes inside the annulus. -/
theorem punctureKernel_eq_zero_of_lt (hε : 0 < ε) (hw : ‖w - z‖ < ε) :
    punctureKernel z ε w = 0 := by
  have h2 : (0 : ℝ) < 3 * ε ^ 2 := by positivity
  have harg : (sqDist z w - ε ^ 2) / (3 * ε ^ 2) < 0 := by
    rw [div_lt_iff₀ h2, zero_mul, sub_neg, sqDist]
    nlinarith [norm_nonneg (w - z)]
  rw [punctureKernel, deriv_smoothTransition_eq_zero_of_neg harg, zero_div]

/-- The density vanishes outside the annulus. -/
theorem punctureKernel_eq_zero_of_gt (hε : 0 < ε) (hw : 2 * ε < ‖w - z‖) :
    punctureKernel z ε w = 0 := by
  have h2 : (0 : ℝ) < 3 * ε ^ 2 := by positivity
  have harg : 1 < (sqDist z w - ε ^ 2) / (3 * ε ^ 2) := by
    rw [lt_div_iff₀ h2, sqDist]
    nlinarith [norm_nonneg (w - z)]
  rw [punctureKernel, deriv_smoothTransition_eq_zero_of_one_lt harg, zero_div]

theorem punctureKernel_self (hε : 0 < ε) (z : ℂ) : punctureKernel z ε z = 0 :=
  punctureKernel_eq_zero_of_lt hε (by simpa using hε)

/-- The density is supported in the closed disc of radius `2ε`. -/
theorem support_punctureKernel_subset (hε : 0 < ε) (z : ℂ) :
    Function.support (punctureKernel z ε) ⊆ closedBall z (2 * ε) := by
  intro w hw
  by_contra hmem
  simp only [mem_closedBall, not_le] at hmem
  exact hw (punctureKernel_eq_zero_of_gt hε (by rwa [← Complex.dist_eq]))

/-- The density is bounded by the reciprocal of the area of the annulus. -/
theorem abs_punctureKernel_le (hε : 0 < ε) {M : ℝ} (hM : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M)
    (z : ℂ) (w : ℂ) : |punctureKernel z ε w| ≤ M / (3 * ε ^ 2) := by
  have h2 : (0 : ℝ) < 3 * ε ^ 2 := by positivity
  rw [punctureKernel, abs_div, abs_of_pos h2]
  exact div_le_div_of_nonneg_right (hM _) h2.le

/-- **The operator applied to the annular cutoff.** -/
theorem dbar_punctureCutoff (z : ℂ) (hε : 0 < ε) (w : ℂ) :
    dbar (fun t => ((punctureCutoff z ε t : ℝ) : ℂ)) w = (punctureKernel z ε w : ℂ) * (w - z) := by
  have h2 : (3 * ε ^ 2 : ℝ) ≠ 0 := by positivity
  have hsub : DifferentiableAt ℝ (fun t : ℂ => sqDist z t - ε ^ 2) w :=
    ((differentiable_sqDist z) w).sub_const (ε ^ 2)
  have hs : DifferentiableAt ℝ (fun t : ℂ => (sqDist z t - ε ^ 2) / (3 * ε ^ 2)) w := by
    simpa only [← div_eq_mul_inv] using hsub.mul_const (3 * ε ^ 2)⁻¹
  have hchain := dbar_comp_real (s := fun t : ℂ => (sqDist z t - ε ^ 2) / (3 * ε ^ 2))
    (ψ := Real.smoothTransition) hs (hasDerivAt_smoothTransition _)
  have hSfun : (fun t : ℂ => (((sqDist z t - ε ^ 2) / (3 * ε ^ 2) : ℝ) : ℂ))
      = fun t : ℂ => ((3 * ε ^ 2 : ℝ) : ℂ)⁻¹ * ((sqDist z t : ℝ) : ℂ)
          + (-(((ε : ℝ) : ℂ) ^ 2) * ((3 * ε ^ 2 : ℝ) : ℂ)⁻¹) := by
    funext t
    push_cast
    field_simp
    ring
  have hd1 : DifferentiableAt ℝ (fun t : ℂ => ((sqDist z t : ℝ) : ℂ)) w :=
    (differentiable_ofReal_sqDist z) w
  have hd2 : DifferentiableAt ℝ
      (fun t : ℂ => ((3 * ε ^ 2 : ℝ) : ℂ)⁻¹ * ((sqDist z t : ℝ) : ℂ)) w :=
    (differentiableAt_const _).mul hd1
  have hbase : dbar (fun t : ℂ => (((sqDist z t - ε ^ 2) / (3 * ε ^ 2) : ℝ) : ℂ)) w
      = ((3 * ε ^ 2 : ℝ) : ℂ)⁻¹ * (w - z) := by
    rw [hSfun, dbar_add_const _ hd2, dbar_const_mul _ hd1, dbar_ofReal_sqDist]
  simp only [punctureCutoff]
  rw [hchain, hbase, punctureKernel]
  push_cast
  ring

/-! ### The cut-off Cauchy kernel -/

variable {χ : ℂ → ℂ}

/-- **The cut-off Cauchy kernel**: the Cauchy kernel at a point, excised near that point by the
annular cutoff and localized by an ambient cutoff. -/
def punctureTest (χ : ℂ → ℂ) (z : ℂ) (ε : ℝ) (w : ℂ) : ℂ :=
  χ w * ((punctureCutoff z ε w : ℝ) : ℂ) * (w - z)⁻¹

/-- The cut-off Cauchy kernel vanishes near the excised point. -/
theorem punctureTest_eventuallyEq_zero (hε : 0 < ε) (χ : ℂ → ℂ) (z : ℂ) :
    punctureTest χ z ε =ᶠ[nhds z] fun _ => (0 : ℂ) := by
  filter_upwards [ball_mem_nhds z hε] with t ht
  have : ‖t - z‖ ≤ ε := by
    rw [← Complex.dist_eq]
    exact (mem_ball.mp ht).le
  simp [punctureTest, punctureCutoff_eq_zero hε this]

theorem contDiff_punctureTest (hχ : ContDiff ℝ ∞ χ) (z : ℂ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (punctureTest χ z ε) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = z
  · subst hw
    exact contDiffAt_const.congr_of_eventuallyEq (punctureTest_eventuallyEq_zero hε χ w)
  · have hinv : ContDiffAt ℝ ∞ (fun t : ℂ => (t - z)⁻¹) w :=
      (contDiff_id.sub contDiff_const).contDiffAt.inv (sub_ne_zero.mpr hw)
    exact (hχ.contDiffAt.mul (contDiff_ofReal_punctureCutoff z ε).contDiffAt).mul hinv

theorem hasCompactSupport_punctureTest (hχ : HasCompactSupport χ) (z : ℂ) (ε : ℝ) :
    HasCompactSupport (punctureTest χ z ε) :=
  (hχ.mul_right).mul_right

theorem tsupport_punctureTest_subset (χ : ℂ → ℂ) (z : ℂ) (ε : ℝ) :
    tsupport (punctureTest χ z ε) ⊆ tsupport χ :=
  closure_mono ((Function.support_mul_subset_left _ _).trans (Function.support_mul_subset_left _ _))

/-- **The operator applied to the cut-off Cauchy kernel.** -/
theorem dbar_punctureTest (hχ : ContDiff ℝ ∞ χ) (z : ℂ) (hε : 0 < ε) (w : ℂ) :
    dbar (punctureTest χ z ε) w
      = dbar χ w * ((punctureCutoff z ε w : ℝ) : ℂ) * (w - z)⁻¹
        + χ w * (punctureKernel z ε w : ℂ) := by
  by_cases hw : w = z
  · subst hw
    rw [dbar_congr (punctureTest_eventuallyEq_zero hε χ w), dbar_const,
      punctureCutoff_eq_zero hε (by simpa using hε.le), punctureKernel_self hε]
    simp
  · have hne : w - z ≠ 0 := sub_ne_zero.mpr hw
    have hdχ : DifferentiableAt ℝ χ w := (hχ.differentiable (by simp)) w
    have hdP : DifferentiableAt ℝ (fun t : ℂ => ((punctureCutoff z ε t : ℝ) : ℂ)) w :=
      (differentiable_ofReal_punctureCutoff z ε) w
    have hdK : DifferentiableAt ℂ (fun t : ℂ => (t - z)⁻¹) w :=
      (differentiableAt_id.sub_const z).inv hne
    have hdKR : DifferentiableAt ℝ (fun t : ℂ => (t - z)⁻¹) w := hdK.restrictScalars ℝ
    have hstep : dbar (fun t : ℂ => χ t * ((punctureCutoff z ε t : ℝ) : ℂ)) w
        = χ w * ((punctureKernel z ε w : ℂ) * (w - z))
          + ((punctureCutoff z ε w : ℝ) : ℂ) * dbar χ w := by
      rw [dbar_mul hdχ hdP, dbar_punctureCutoff z hε]
    have hprod : punctureTest χ z ε
        = fun t : ℂ => (χ t * ((punctureCutoff z ε t : ℝ) : ℂ)) * (t - z)⁻¹ := rfl
    rw [hprod, dbar_mul (u := fun t : ℂ => χ t * ((punctureCutoff z ε t : ℝ) : ℂ))
      (v := fun t : ℂ => (t - z)⁻¹) (hdχ.mul hdP) hdKR, dbar_eq_zero hdK, hstep]
    field_simp
    ring

end Rigidity.RET

end
