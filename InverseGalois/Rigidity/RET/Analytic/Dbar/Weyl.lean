/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Basic
import InverseGalois.Rigidity.RET.Analytic.Dbar.Kernel
import InverseGalois.Rigidity.RET.Analytic.Dbar.Parts
import InverseGalois.Rigidity.RET.Analytic.Dbar.Pompeiu
import InverseGalois.Rigidity.RET.Analytic.Dbar.Solve
import InverseGalois.Rigidity.RET.Analytic.Dbar.CauchyType
import InverseGalois.Rigidity.RET.Analytic.Dbar.Puncture
import InverseGalois.Rigidity.RET.Analytic.Dbar.LebesguePoint

/-!
# Regularity for the Cauchy–Riemann operator

A merely integrable function which satisfies the Cauchy–Riemann equation `∂u/∂z̄ = g` in the sense
of distributions agrees almost everywhere with a genuine solution.  The proof tests the equation
against the Cauchy kernel with its pole excised by an annular cut-off: the cut-off contributes an
approximate identity concentrated on a thin annulus, which reads off the value of the function at
every Lebesgue point, while the remaining terms converge to Cauchy-type integrals.  The resulting
formula exhibits the function as the sum of a holomorphic term and the Cauchy transform of the
right-hand side, and the Cauchy transform solves the equation classically.

## Main results

* `Rigidity.RET.cauchyTransform_eq_cauchyType` — the Cauchy transform is a Cauchy-type integral.
* `Rigidity.RET.integral_punctureKernel` — the annular density has total mass `π`.
* `Rigidity.RET.eq_cauchyType_of_weak` — the representation formula at a Lebesgue point.
* `Rigidity.RET.exists_dbar_of_weak` — a weak solution agrees almost everywhere with a
  classical one on a smaller disc.
-/

open MeasureTheory Metric Filter Topology Real

open scoped ContDiff

noncomputable section

namespace Rigidity.RET

variable {u g χ : ℂ → ℂ} {z : ℂ} {ρ ε : ℝ}

private theorem one_le_infty : (1 : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

/-! ### The Cauchy transform as a Cauchy-type integral -/

/-- **The Cauchy transform is a Cauchy-type integral**, up to the normalising factor. -/
theorem cauchyTransform_eq_cauchyType (φ : ℂ → ℂ) (w : ℂ) :
    cauchyTransform φ w = -((π : ℂ))⁻¹ * cauchyType φ w := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℂ))
    (fun s : ℂ => φ (w + s) / s) w
  rw [cauchyTransform, cauchyType]
  congr 1
  rw [← h]
  refine integral_congr_ae (.of_forall fun x => ?_)
  show φ (w + (x - w)) / (x - w) = φ x / (x - w)
  rw [show w + (x - w) = x from by ring]

/-! ### Integrability against the Cauchy kernel -/

/-- A continuous function of compact support is integrable against the Cauchy kernel. -/
theorem integrable_div_sub_of_hasCompactSupport {φ : ℂ → ℂ} (hφ : Continuous φ)
    (hs : HasCompactSupport φ) (z : ℂ) :
    Integrable (fun w : ℂ => φ w / (w - z)) volume := by
  obtain ⟨B, hB⟩ := hφ.bounded_above_of_compact_support hs
  obtain ⟨M, hM⟩ := hs.isCompact.isBounded.subset_closedBall z
  have hzero : ∀ v : ℂ, v ∉ closedBall (0 : ℂ) M → φ (v + z) / v = 0 := by
    intro v hv
    have hout : φ (v + z) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hmem => hv ?_
      have := hM hmem
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_right] at this ⊢
      simpa using this
    simp [hout]
  have hIO : IntegrableOn (fun v : ℂ => φ (v + z) / v) (closedBall (0 : ℂ) M) volume := by
    simp only [div_eq_mul_inv]
    refine (integrableOn_inv_closedBall M).bdd_mul ?_ (.of_forall fun v => hB _)
    exact ((hφ.comp (continuous_id.add continuous_const)).aestronglyMeasurable).restrict
  have hbase : Integrable (fun v : ℂ => φ (v + z) / v) volume :=
    hIO.integrable_of_forall_notMem_eq_zero hzero
  have hmp : MeasurePreserving (fun w : ℂ => w - z) volume volume :=
    measurePreserving_sub_right (volume : Measure ℂ) z
  have h := hmp.integrable_comp_of_integrable hbase
  simpa [Function.comp_def] using h

/-! ### The cut-off is constant near the point -/

/-- Where the cut-off is identically one, the operator annihilates it. -/
theorem dbar_eq_zero_of_eq_one (hone : ∀ w : ℂ, ‖w - z‖ ≤ ρ → χ w = 1) {w : ℂ}
    (hw : ‖w - z‖ < ρ) : dbar χ w = 0 := by
  have hlt : (0 : ℝ) < ρ - ‖w - z‖ := by linarith
  have heq : χ =ᶠ[nhds w] fun _ => (1 : ℂ) := by
    filter_upwards [ball_mem_nhds w hlt] with t ht
    refine hone t ?_
    have hd : ‖t - w‖ < ρ - ‖w - z‖ := by
      simpa [Complex.dist_eq] using ht
    have hle : ‖t - z‖ ≤ ‖t - w‖ + ‖w - z‖ := by
      have hsum : t - z = (t - w) + (w - z) := by ring
      rw [hsum]
      exact norm_add_le _ _
    linarith
  rw [dbar_congr heq, dbar_const]

/-- The operator applied to the cut-off, divided by the Cauchy kernel, is bounded. -/
theorem exists_bound_dbar_inv (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hρ : 0 < ρ)
    (hone : ∀ w : ℂ, ‖w - z‖ ≤ ρ → χ w = 1) :
    ∃ D : ℝ, ∀ w : ℂ, ‖dbar χ w * (w - z)⁻¹‖ ≤ D := by
  obtain ⟨B, hB⟩ := (continuous_dbar (hχ.of_le one_le_infty)).bounded_above_of_compact_support
    (hasCompactSupport_dbar hχs)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB z)
  refine ⟨B * ρ⁻¹, fun w => ?_⟩
  rcases lt_or_ge ‖w - z‖ ρ with h | h
  · rw [dbar_eq_zero_of_eq_one hone h, zero_mul, norm_zero]
    exact mul_nonneg hB0 (by positivity)
  · rw [norm_mul, norm_inv]
    have h1 : ‖w - z‖⁻¹ ≤ ρ⁻¹ := by gcongr
    exact mul_le_mul (hB w) h1 (by positivity) hB0

/-- The product of the cut-off's derivative, the Cauchy kernel and an integrable function is
integrable. -/
theorem integrable_dbar_inv_mul (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hρ : 0 < ρ)
    (hone : ∀ w : ℂ, ‖w - z‖ ≤ ρ → χ w = 1) (hu : Integrable u) :
    Integrable (fun w : ℂ => dbar χ w * (w - z)⁻¹ * u w) volume := by
  obtain ⟨D, hD⟩ := exists_bound_dbar_inv hχ hχs hρ hone
  refine hu.bdd_mul ?_ (.of_forall hD)
  exact (continuous_dbar (hχ.of_le one_le_infty)).aestronglyMeasurable.mul
    ((measurable_id.sub measurable_const).inv).aestronglyMeasurable

/-- The annular density is integrable. -/
theorem integrable_ofReal_punctureKernel (hε : 0 < ε) (z : ℂ) :
    Integrable (fun w : ℂ => ((punctureKernel z ε w : ℝ) : ℂ)) volume := by
  refine (Complex.continuous_ofReal.comp (continuous_punctureKernel z ε)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall z (2 * ε)) fun w hw => ?_
  have : 2 * ε < ‖w - z‖ := by
    simp only [mem_closedBall, Complex.dist_eq, not_le] at hw
    exact hw
  simp [punctureKernel_eq_zero_of_gt hε this]

/-- The annular density times an integrable function is integrable. -/
theorem integrable_punctureKernel_mul (hε : 0 < ε) (hu : Integrable u) (z : ℂ) :
    Integrable (fun w : ℂ => ((punctureKernel z ε w : ℝ) : ℂ) * u w) volume := by
  obtain ⟨M, _, hM⟩ := exists_bound_deriv_smoothTransition
  refine hu.bdd_mul (c := M / (3 * ε ^ 2))
    ((Complex.continuous_ofReal.comp (continuous_punctureKernel z ε)).aestronglyMeasurable)
    (.of_forall fun w => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_punctureKernel_le hε hM z w

/-! ### The derivative of the excised kernel -/

/-- **The operator applied to the excised Cauchy kernel**, in the region where the cut-off is
constant near the pole. -/
theorem dbar_punctureTest_eq (hχ : ContDiff ℝ ∞ χ) (hone : ∀ w : ℂ, ‖w - z‖ ≤ ρ → χ w = 1)
    (hε : 0 < ε) (hερ : 2 * ε < ρ) (w : ℂ) :
    dbar (punctureTest χ z ε) w
      = dbar χ w * (w - z)⁻¹ + ((punctureKernel z ε w : ℝ) : ℂ) := by
  rw [dbar_punctureTest hχ z hε w]
  congr 1
  · rcases lt_or_ge ‖w - z‖ ρ with h | h
    · rw [dbar_eq_zero_of_eq_one hone h]
      ring
    · rw [punctureCutoff_eq_one hε (by linarith)]
      push_cast
      ring
  · by_cases hk : punctureKernel z ε w = 0
    · rw [hk]
      simp
    · have hle : ‖w - z‖ ≤ 2 * ε := by
        by_contra hc
        exact hk (punctureKernel_eq_zero_of_gt hε (lt_of_not_ge hc))
      rw [hone w (by linarith)]
      ring

/-! ### The mass of the annular density -/

/-- **The annular density has total mass `π`.** -/
theorem integral_punctureKernel (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hone : ∀ w : ℂ, ‖w - z‖ ≤ ρ → χ w = 1) (hε : 0 < ε) (hερ : 2 * ε < ρ) :
    ∫ w : ℂ, ((punctureKernel z ε w : ℝ) : ℂ) = (π : ℂ) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le one_le_infty
  have hzero : ∫ w : ℂ, dbar (punctureTest χ z ε) w = 0 :=
    integral_dbar_eq_zero ((contDiff_punctureTest hχ z hε).of_le one_le_infty)
      (hasCompactSupport_punctureTest hχs z ε)
  have hA : Integrable (fun w : ℂ => dbar χ w * (w - z)⁻¹) volume := by
    have := integrable_div_sub_of_hasCompactSupport (continuous_dbar hχ1)
      (hasCompactSupport_dbar hχs) z
    simpa only [div_eq_mul_inv] using this
  have hB : Integrable (fun w : ℂ => ((punctureKernel z ε w : ℝ) : ℂ)) volume :=
    integrable_ofReal_punctureKernel hε z
  simp_rw [dbar_punctureTest_eq hχ hone hε hερ] at hzero
  rw [integral_add hA hB] at hzero
  have hct : ∫ w : ℂ, dbar χ w * (w - z)⁻¹ = -(π : ℂ) := by
    have h1 : cauchyTransform (dbar χ) z = χ z := cauchyTransform_dbar hχ1 hχs z
    have h2 : cauchyTransform (dbar χ) z = -((π : ℂ))⁻¹ * cauchyType (dbar χ) z :=
      cauchyTransform_eq_cauchyType _ _
    have h3 : χ z = 1 := hone z (by simp only [sub_self, norm_zero]; linarith)
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h5 : (1 : ℂ) = -((π : ℂ))⁻¹ * cauchyType (dbar χ) z := by rw [← h3, ← h1, h2]
    have hkey : -(π : ℂ) * (1 : ℂ)
        = -(π : ℂ) * (-((π : ℂ))⁻¹ * cauchyType (dbar χ) z) :=
      congrArg (fun t : ℂ => -(π : ℂ) * t) h5
    have hsimp : -(π : ℂ) * (-((π : ℂ))⁻¹ * cauchyType (dbar χ) z) = cauchyType (dbar χ) z := by
      field_simp
    rw [hsimp, mul_one] at hkey
    have h4 : cauchyType (dbar χ) z = -(π : ℂ) := hkey.symm
    simpa only [cauchyType, div_eq_mul_inv] using h4
  rw [hct] at hzero
  linear_combination hzero

/-! ### The two limits -/

/-- **The annular density is an approximate identity**: tested against an integrable function it
reads off `π` times the value at a Lebesgue point. -/
theorem tendsto_integral_punctureKernel_mul (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hρ : 0 < ρ) (hone : ∀ w : ℂ, ‖w - z‖ ≤ ρ → χ w = 1) (hu : Integrable u)
    (hleb : IsLebesguePoint u z) :
    Tendsto (fun ε : ℝ => ∫ w : ℂ, ((punctureKernel z ε w : ℝ) : ℂ) * u w) (𝓝[>] 0)
      (𝓝 ((π : ℂ) * u z)) := by
  obtain ⟨M, hMpos, hM⟩ := exists_bound_deriv_smoothTransition
  have hsmall : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), 2 * e < ρ := by
    have hmem : {t : ℝ | t < ρ / 2} ∈ 𝓝 (0 : ℝ) := gt_mem_nhds (by linarith)
    filter_upwards [nhdsWithin_le_nhds hmem] with e he
    have : e < ρ / 2 := he
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero'
    (g := fun e : ℝ => M / 3 * ((e ^ 2)⁻¹ * ∫ w in closedBall z (2 * e), ‖u w - u z‖))
    (.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, hsmall] with e he heρ
    have hepos : 0 < e := he
    have he2 : (0 : ℝ) < 3 * e ^ 2 := by positivity
    have hmass : ∫ w : ℂ, ((punctureKernel z e w : ℝ) : ℂ) = (π : ℂ) :=
      integral_punctureKernel hχ hχs hone hepos heρ
    have hKu : Integrable (fun w : ℂ => ((punctureKernel z e w : ℝ) : ℂ) * u w) volume :=
      integrable_punctureKernel_mul hepos hu z
    have hKc : Integrable (fun w : ℂ => ((punctureKernel z e w : ℝ) : ℂ) * u z) volume :=
      (integrable_ofReal_punctureKernel hepos z).mul_const _
    have hF : Integrable
        (fun w : ℂ => ((punctureKernel z e w : ℝ) : ℂ) * (u w - u z)) volume := by
      simpa only [mul_sub] using hKu.sub hKc
    have hsplit : (∫ w : ℂ, ((punctureKernel z e w : ℝ) : ℂ) * u w) - (π : ℂ) * u z
        = ∫ w : ℂ, ((punctureKernel z e w : ℝ) : ℂ) * (u w - u z) := by
      have hconst : (π : ℂ) * u z = ∫ w : ℂ, ((punctureKernel z e w : ℝ) : ℂ) * u z := by
        rw [integral_mul_const, hmass]
      rw [hconst, ← integral_sub hKu hKc]
      refine integral_congr_ae (.of_forall fun w => ?_)
      show ((punctureKernel z e w : ℝ) : ℂ) * u w - ((punctureKernel z e w : ℝ) : ℂ) * u z
        = ((punctureKernel z e w : ℝ) : ℂ) * (u w - u z)
      ring
    rw [hsplit]
    have hvanish : ∀ w : ℂ, w ∉ closedBall z (2 * e) →
        ‖((punctureKernel z e w : ℝ) : ℂ) * (u w - u z)‖ = 0 := by
      intro w hw
      have h2 : 2 * e < ‖w - z‖ := by
        simp only [mem_closedBall, Complex.dist_eq, not_le] at hw
        exact hw
      simp [punctureKernel_eq_zero_of_gt hepos h2]
    have hstep1 : ‖∫ w : ℂ, ((punctureKernel z e w : ℝ) : ℂ) * (u w - u z)‖
        ≤ ∫ w : ℂ, ‖((punctureKernel z e w : ℝ) : ℂ) * (u w - u z)‖ :=
      norm_integral_le_integral_norm _
    have hrestrict : (∫ w : ℂ, ‖((punctureKernel z e w : ℝ) : ℂ) * (u w - u z)‖)
        = ∫ w in closedBall z (2 * e), ‖((punctureKernel z e w : ℝ) : ℂ) * (u w - u z)‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hvanish).symm
    have hsub : IntegrableOn (fun w : ℂ => u w - u z) (closedBall z (2 * e)) volume :=
      hu.integrableOn.sub (integrableOn_const measure_closedBall_lt_top.ne)
    have hmono : (∫ w in closedBall z (2 * e), ‖((punctureKernel z e w : ℝ) : ℂ) * (u w - u z)‖)
        ≤ ∫ w in closedBall z (2 * e), (M / (3 * e ^ 2)) * ‖u w - u z‖ := by
      refine setIntegral_mono_on hF.norm.integrableOn (hsub.norm.const_mul _)
        measurableSet_closedBall fun w _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_punctureKernel_le hepos hM z w) (norm_nonneg _)
    refine hstep1.trans ?_
    rw [hrestrict]
    refine hmono.trans ?_
    rw [integral_const_mul]
    have hrw : M / (3 * e ^ 2) * (∫ w in closedBall z (2 * e), ‖u w - u z‖)
        = M / 3 * ((e ^ 2)⁻¹ * ∫ w in closedBall z (2 * e), ‖u w - u z‖) := by
      field_simp
    rw [hrw]
  · have := (tendsto_const_nhds (x := M / 3) (f := 𝓝[>] (0 : ℝ))).mul hleb.tendsto_two
    simpa using this

/-- The excised Cauchy kernel converges to the Cauchy kernel when tested against a continuous
function of compact support. -/
theorem tendsto_integral_punctureTest_mul (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hg : Continuous g) (z : ℂ) :
    Tendsto (fun ε : ℝ => ∫ w : ℂ, punctureTest χ z ε w * g w) (𝓝[>] 0)
      (𝓝 (cauchyType (fun w => χ w * g w) z)) := by
  have hbound : Integrable (fun w : ℂ => χ w * g w / (w - z)) volume :=
    integrable_div_sub_of_hasCompactSupport (hχ.continuous.mul hg) hχs.mul_right z
  rw [cauchyType]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun w : ℂ => ‖χ w * g w / (w - z)‖) ?_ ?_ hbound.norm ?_
  · filter_upwards [self_mem_nhdsWithin] with e he
    exact (((contDiff_punctureTest hχ z he).continuous).mul hg).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with e _
    refine .of_forall fun w => ?_
    have heq : punctureTest χ z e w * g w
        = ((punctureCutoff z e w : ℝ) : ℂ) * (χ w * g w / (w - z)) := by
      rw [punctureTest, div_eq_mul_inv]
      ring
    rw [heq, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_ofReal_punctureCutoff_le z e w)
  · refine .of_forall fun w => ?_
    by_cases hne : w = z
    · subst hne
      have h0 : ∀ e : ℝ, punctureTest χ w e w * g w = 0 := by
        intro e
        simp [punctureTest]
      simp only [h0, sub_self, div_zero]
      exact tendsto_const_nhds
    · have hpos : (0 : ℝ) < ‖w - z‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        exact hne
      have hev : (fun _ : ℝ => χ w * g w / (w - z)) =ᶠ[𝓝[>] (0 : ℝ)]
          fun e : ℝ => punctureTest χ z e w * g w := by
        have hmem : {t : ℝ | t < ‖w - z‖ / 2} ∈ 𝓝 (0 : ℝ) := gt_mem_nhds (by positivity)
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with e he hlt
        have hepos : 0 < e := he
        have h2 : 2 * e ≤ ‖w - z‖ := by
          have : e < ‖w - z‖ / 2 := hlt
          linarith
        rw [punctureTest, punctureCutoff_eq_one hepos h2, Complex.ofReal_one, div_eq_mul_inv]
        ring
      exact Tendsto.congr' hev tendsto_const_nhds

/-! ### The representation formula -/

/-- **The representation formula at a Lebesgue point**: a weak solution of the Cauchy–Riemann
equation is the sum of a Cauchy-type integral carried by the derivative of the cut-off and the
Cauchy transform of the right-hand side. -/
theorem eq_cauchyType_of_weak (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hρ : 0 < ρ)
    (hone : ∀ w : ℂ, ‖w - z‖ ≤ ρ → χ w = 1) (hu : Integrable u) (hleb : IsLebesguePoint u z)
    (hg : Continuous g)
    (hweak : ∀ ζ : ℂ → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ → tsupport ζ ⊆ tsupport χ →
      (∫ w : ℂ, dbar ζ w * u w) = -∫ w : ℂ, ζ w * g w) :
    u z = -((π : ℂ))⁻¹ * (cauchyType (fun w => dbar χ w * u w) z
      + cauchyType (fun w => χ w * g w) z) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA : Integrable (fun w : ℂ => dbar χ w * (w - z)⁻¹ * u w) volume :=
    integrable_dbar_inv_mul hχ hχs hρ hone hu
  have hAeq : (∫ w : ℂ, dbar χ w * (w - z)⁻¹ * u w)
      = cauchyType (fun w => dbar χ w * u w) z := by
    rw [cauchyType]
    refine integral_congr_ae (.of_forall fun w => ?_)
    show dbar χ w * (w - z)⁻¹ * u w = dbar χ w * u w / (w - z)
    ring
  have hsmall : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), 2 * e < ρ := by
    have hmem : {t : ℝ | t < ρ / 2} ∈ 𝓝 (0 : ℝ) := gt_mem_nhds (by linarith)
    filter_upwards [nhdsWithin_le_nhds hmem] with e he
    have : e < ρ / 2 := he
    linarith
  have heq : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ),
      (∫ w : ℂ, ((punctureKernel z e w : ℝ) : ℂ) * u w)
        = -(∫ w : ℂ, punctureTest χ z e w * g w)
          - cauchyType (fun w => dbar χ w * u w) z := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with e he heρ
    have hepos : 0 < e := he
    have hw := hweak (punctureTest χ z e) (contDiff_punctureTest hχ z hepos)
      (hasCompactSupport_punctureTest hχs z e) (tsupport_punctureTest_subset χ z e)
    have hKu : Integrable (fun w : ℂ => ((punctureKernel z e w : ℝ) : ℂ) * u w) volume :=
      integrable_punctureKernel_mul hepos hu z
    have hexpand : (∫ w : ℂ, dbar (punctureTest χ z e) w * u w)
        = (∫ w : ℂ, dbar χ w * (w - z)⁻¹ * u w)
          + ∫ w : ℂ, ((punctureKernel z e w : ℝ) : ℂ) * u w := by
      rw [← integral_add hA hKu]
      refine integral_congr_ae (.of_forall fun w => ?_)
      show dbar (punctureTest χ z e) w * u w
        = dbar χ w * (w - z)⁻¹ * u w + ((punctureKernel z e w : ℝ) : ℂ) * u w
      rw [dbar_punctureTest_eq hχ hone hepos heρ w]
      ring
    rw [hexpand, hAeq] at hw
    linear_combination hw
  have hlimL : Tendsto (fun e : ℝ => ∫ w : ℂ, ((punctureKernel z e w : ℝ) : ℂ) * u w) (𝓝[>] 0)
      (𝓝 ((π : ℂ) * u z)) :=
    tendsto_integral_punctureKernel_mul hχ hχs hρ hone hu hleb
  have hlimR : Tendsto (fun e : ℝ => -(∫ w : ℂ, punctureTest χ z e w * g w)
      - cauchyType (fun w => dbar χ w * u w) z) (𝓝[>] 0)
      (𝓝 (-cauchyType (fun w => χ w * g w) z
        - cauchyType (fun w => dbar χ w * u w) z)) :=
    ((tendsto_integral_punctureTest_mul hχ hχs hg z).neg).sub tendsto_const_nhds
  have hkey := tendsto_nhds_unique (hlimL.congr' heq) hlimR
  field_simp
  linear_combination hkey

/-! ### Weyl's lemma -/

/-- **Weyl's lemma for the Cauchy–Riemann operator.**  An integrable function which satisfies
`∂u/∂z̄ = g` against every smooth test function supported in a disc agrees, almost everywhere on a
smaller disc, with a function that satisfies the equation classically. -/
theorem exists_dbar_of_weak {z₀ : ℂ} {R : ℝ} (hR : 0 < R) (hu : Integrable u)
    (hg : ContDiff ℝ 1 g)
    (hweak : ∀ ζ : ℂ → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ closedBall z₀ R → (∫ w : ℂ, dbar ζ w * u w) = -∫ w : ℂ, ζ w * g w) :
    ∃ v : ℂ → ℂ, (∀ w ∈ ball z₀ (R / 4), DifferentiableAt ℝ v w) ∧
      (∀ w ∈ ball z₀ (R / 4), dbar v w = g w) ∧
      ∀ᵐ w : ℂ, w ∈ ball z₀ (R / 4) → u w = v w := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  -- the cut-off
  let f : ContDiffBump z₀ := ⟨R / 2, R, by linarith, by linarith⟩
  set χ : ℂ → ℂ := fun w => ((f w : ℝ) : ℂ) with hχdef
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le one_le_infty
  have hχs : HasCompactSupport χ :=
    f.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hsupp_eq : Function.support χ = Function.support (f : ℂ → ℝ) := by
    ext w
    simp [hχdef, Function.mem_support]
  have htsupp : tsupport χ = closedBall z₀ R := by
    rw [tsupport, hsupp_eq, ← tsupport, f.tsupport_eq]
  have honeHalf : ∀ w : ℂ, ‖w - z₀‖ ≤ R / 2 → χ w = 1 := by
    intro w hw
    have : w ∈ closedBall z₀ f.rIn := by
      simp only [mem_closedBall, Complex.dist_eq]
      exact hw
    simp [hχdef, f.one_of_mem_closedBall this]
  have hweak' : ∀ ζ : ℂ → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ → tsupport ζ ⊆ tsupport χ →
      (∫ w : ℂ, dbar ζ w * u w) = -∫ w : ℂ, ζ w * g w := by
    intro ζ h1 h2 h3
    exact hweak ζ h1 h2 (htsupp ▸ h3)
  -- the two pieces of the solution
  have hdbarInt : Integrable (fun w : ℂ => dbar χ w * u w) volume := by
    obtain ⟨B, hB⟩ := (continuous_dbar hχ1).bounded_above_of_compact_support
      (hasCompactSupport_dbar hχs)
    exact hu.bdd_mul (continuous_dbar hχ1).aestronglyMeasurable (.of_forall hB)
  have hχg : ContDiff ℝ 1 (fun w : ℂ => χ w * g w) := hχ1.mul hg
  have hχgs : HasCompactSupport (fun w : ℂ => χ w * g w) := hχs.mul_right
  refine ⟨fun w => -((π : ℂ))⁻¹ * cauchyType (fun t => dbar χ t * u t) w
    + cauchyTransform (fun t => χ t * g t) w, ?_, ?_, ?_⟩
  · intro w hw
    have hwn : ‖w - z₀‖ < R / 4 := by
      simpa [Complex.dist_eq] using hw
    have hd : (0 : ℝ) < R / 2 - ‖w - z₀‖ := by linarith
    have hvanish : ∀ t : ℂ, ‖t - w‖ < R / 2 - ‖w - z₀‖ → dbar χ t * u t = 0 := by
      intro t ht
      have hle : ‖t - z₀‖ ≤ ‖t - w‖ + ‖w - z₀‖ := by
        have hsum : t - z₀ = (t - w) + (w - z₀) := by ring
        rw [hsum]
        exact norm_add_le _ _
      have : ‖t - z₀‖ < R / 2 := by linarith
      rw [dbar_eq_zero_of_eq_one honeHalf this, zero_mul]
    have h1 : DifferentiableAt ℝ (cauchyType (fun t => dbar χ t * u t)) w :=
      (differentiableAt_cauchyType hdbarInt hd hvanish).restrictScalars ℝ
    have h2 : DifferentiableAt ℝ (cauchyTransform (fun t => χ t * g t)) w :=
      ((contDiff_cauchyTransform hχg hχgs).differentiable one_ne_zero) w
    exact (h1.const_mul _).add h2
  · intro w hw
    have hwn : ‖w - z₀‖ < R / 4 := by
      simpa [Complex.dist_eq] using hw
    have hd : (0 : ℝ) < R / 2 - ‖w - z₀‖ := by linarith
    have hvanish : ∀ t : ℂ, ‖t - w‖ < R / 2 - ‖w - z₀‖ → dbar χ t * u t = 0 := by
      intro t ht
      have hle : ‖t - z₀‖ ≤ ‖t - w‖ + ‖w - z₀‖ := by
        have hsum : t - z₀ = (t - w) + (w - z₀) := by ring
        rw [hsum]
        exact norm_add_le _ _
      have : ‖t - z₀‖ < R / 2 := by linarith
      rw [dbar_eq_zero_of_eq_one honeHalf this, zero_mul]
    have h1 : DifferentiableAt ℝ (cauchyType (fun t => dbar χ t * u t)) w :=
      (differentiableAt_cauchyType hdbarInt hd hvanish).restrictScalars ℝ
    have h2 : DifferentiableAt ℝ (cauchyTransform (fun t => χ t * g t)) w :=
      ((contDiff_cauchyTransform hχg hχgs).differentiable one_ne_zero) w
    rw [dbar_add (h1.const_mul _) h2, dbar_const_mul _ h1,
      dbar_cauchyType hdbarInt hd hvanish, dbar_cauchyTransform hχg hχgs w]
    have hχw : χ w = 1 := honeHalf w (by linarith)
    rw [hχw]
    ring
  · filter_upwards [ae_isLebesguePoint hu.locallyIntegrable] with w hleb hw
    have hwn : ‖w - z₀‖ < R / 4 := by
      simpa [Complex.dist_eq] using hw
    have honeQ : ∀ t : ℂ, ‖t - w‖ ≤ R / 4 → χ t = 1 := by
      intro t ht
      refine honeHalf t ?_
      have hle : ‖t - z₀‖ ≤ ‖t - w‖ + ‖w - z₀‖ := by
        have hsum : t - z₀ = (t - w) + (w - z₀) := by ring
        rw [hsum]
        exact norm_add_le _ _
      linarith
    have hrep := eq_cauchyType_of_weak hχ hχs (ρ := R / 4) (by linarith) honeQ hu hleb
      hg.continuous hweak'
    rw [hrep, mul_add, cauchyTransform_eq_cauchyType]

end Rigidity.RET

end
