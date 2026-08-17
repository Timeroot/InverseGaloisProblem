/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Basic

/-!
# The Cauchy transform inverts `∂/∂z̄`

Convolution with the fundamental solution `-1/(π z)` of the Cauchy–Riemann operator is the
**Cauchy transform**.  On a continuously differentiable function of compact support it undoes the
operator: the transform of `∂f/∂z̄` is `f` again.

The proof is the one that passes to polar coordinates around the point at which the value is read.
In those coordinates the anti-holomorphic derivative is half the sum of the radial derivative and
`i` times the angular derivative divided by the radius (`Rigidity.RET.polar_dbar`), the Jacobian
`r` of the substitution cancels the pole of the kernel exactly, and the two derivatives integrate
by the fundamental theorem of calculus: the radial one along each ray contributes the value at the
centre, and the angular one contributes nothing, the circle having no boundary.

## Main definitions

* `Rigidity.RET.cauchyTransform` — convolution with `-1/(π z)`.

## Main results

* `Rigidity.RET.cauchyTransform_dbar` — the transform of `∂f/∂z̄` is `f`.
-/

open MeasureTheory Set

open scoped Real

noncomputable section

namespace Rigidity.RET

variable {g : ℂ → ℂ} {w : ℂ}

/-- The **Cauchy transform** of a function of a complex variable: convolution with the fundamental
solution `-1/(π z)` of the Cauchy–Riemann operator. -/
def cauchyTransform (g : ℂ → ℂ) (w : ℂ) : ℂ := -((π : ℂ))⁻¹ * ∫ u : ℂ, g (w + u) / u

/-! ### The two halves of the polar integrand -/

/-- The radial half of the integrand of the Cauchy transform in polar coordinates. -/
def polarRad (g : ℂ → ℂ) (w : ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ g (w + (p.1 : ℂ) * circPt p.2) (circPt p.2)

/-- The angular half of the integrand of the Cauchy transform in polar coordinates. -/
def polarAng (g : ℂ → ℂ) (w : ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.I * fderiv ℝ g (w + (p.1 : ℂ) * circPt p.2) (Complex.I * circPt p.2)

theorem continuous_circPt : Continuous circPt := by
  have h : circPt = fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) := funext circPt_eq_exp
  rw [h]
  fun_prop

theorem continuous_polarBase (w : ℂ) :
    Continuous fun p : ℝ × ℝ => w + (p.1 : ℂ) * circPt p.2 :=
  continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
    (continuous_circPt.comp continuous_snd))

theorem continuous_polarRad (hg : ContDiff ℝ 1 g) (w : ℂ) : Continuous (polarRad g w) :=
  ((hg.continuous_fderiv one_ne_zero).comp (continuous_polarBase w)).clm_apply
    (continuous_circPt.comp continuous_snd)

theorem continuous_polarAng (hg : ContDiff ℝ 1 g) (w : ℂ) : Continuous (polarAng g w) :=
  continuous_const.mul
    (((hg.continuous_fderiv one_ne_zero).comp (continuous_polarBase w)).clm_apply
      (continuous_const.mul (continuous_circPt.comp continuous_snd)))

/-! ### A radius outside which the function and its derivative vanish -/

/-- Outside a disc around the point at which the transform is read, a compactly supported function
and its derivative both vanish, and the derivative is bounded everywhere. -/
theorem exists_radius_bound (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g) (w : ℂ) :
    ∃ R C : ℝ, 0 < R ∧ (∀ z : ℂ, ‖fderiv ℝ g z‖ ≤ C) ∧
      ∀ u : ℂ, R ≤ ‖u‖ → g (w + u) = 0 ∧ fderiv ℝ g (w + u) = 0 := by
  obtain ⟨C, hC⟩ := (hg.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hsupp.fderiv ℝ)
  obtain ⟨M, hM⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨|M| + ‖w‖ + 1, C, by positivity, hC, fun u hu => ?_⟩
  have hnot : w + u ∉ tsupport g := by
    intro hmem
    have h1 : ‖w + u‖ ≤ M := by simpa using hM hmem
    have h2 : ‖u‖ ≤ ‖w + u‖ + ‖w‖ := by
      calc ‖u‖ = ‖(w + u) - w‖ := by ring_nf
        _ ≤ ‖w + u‖ + ‖w‖ := norm_sub_le _ _
    have h3 : M ≤ |M| := le_abs_self M
    linarith
  exact ⟨image_eq_zero_of_notMem_tsupport hnot, fderiv_of_notMem_tsupport ℝ hnot⟩

/-! ### Integrability of the two halves -/

/-- A continuous bounded function which vanishes off a set of finite measure is integrable on any
measurable set containing that set. -/
theorem integrableOn_of_bounded_off {F : ℝ × ℝ → ℂ} (hF : Continuous F) {C : ℝ}
    (hbd : ∀ p, ‖F p‖ ≤ C) {s u : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hu : MeasurableSet u)
    (husub : u ⊆ s) (hufin : volume u ≠ ⊤) (hvan : ∀ p ∈ s, p ∉ u → F p = 0) :
    IntegrableOn F s volume := by
  have h1 : IntegrableOn F u volume :=
    Measure.integrableOn_of_bounded hufin hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => hbd a)
  have hz : IntegrableOn (fun _ : ℝ × ℝ => (0 : ℂ)) (s \ u) volume := integrableOn_zero
  have h2 : IntegrableOn F (s \ u) volume :=
    hz.congr_fun (fun x hx => (hvan x hx.1 hx.2).symm) (hs.diff hu)
  have hsu : s = u ∪ (s \ u) := (Set.union_diff_cancel husub).symm
  rw [hsu, integrableOn_union]
  exact ⟨h1, h2⟩

theorem volume_box_ne_top {R : ℝ} :
    volume (Ioo (0 : ℝ) R ×ˢ Ioo (-π) π) ≠ ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem volume_box_swap_ne_top {R : ℝ} :
    volume (Ioo (-π) π ×ˢ Ioo (0 : ℝ) R) ≠ ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-! ### The radial integral -/

/-- Along the ray of angle `θ`, the radial half of the integrand is the derivative of the function
read along that ray. -/
theorem hasDerivAt_along_ray (hg : ContDiff ℝ 1 g) (w : ℂ) (θ : ℝ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => g (w + (r : ℂ) * circPt θ)) (polarRad g w (r, θ)) r := by
  have h1 : HasDerivAt (fun r : ℝ => w + (r : ℂ) * circPt θ) (circPt θ) r := by
    have h0 : HasDerivAt (fun r : ℝ => (r : ℂ) * circPt θ) (circPt θ) r := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (circPt θ)
    simpa using h0.const_add w
  exact ((hg.differentiable one_ne_zero) (w + (r : ℂ) * circPt θ)).hasFDerivAt.comp_hasDerivAt r h1

/-- Along the circle of radius `r`, the angular derivative of the function. -/
theorem hasDerivAt_along_circle (hg : ContDiff ℝ 1 g) (w : ℂ) (r : ℝ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => g (w + (r : ℂ) * circPt θ))
      (fderiv ℝ g (w + (r : ℂ) * circPt θ) ((r : ℂ) * (Complex.I * circPt θ))) θ := by
  have hexp : HasDerivAt (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) θ := by
    have h0 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
    exact h0.cexp
  have h1 : HasDerivAt (fun θ : ℝ => w + (r : ℂ) * circPt θ)
      ((r : ℂ) * (Complex.I * circPt θ)) θ := by
    have h2 : HasDerivAt (fun θ : ℝ => (r : ℂ) * circPt θ)
        ((r : ℂ) * (Complex.I * circPt θ)) θ := by
      have h3 : (fun θ : ℝ => (r : ℂ) * circPt θ)
          = fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
        funext θ; rw [circPt_eq_exp]
      have h4 := hexp.const_mul ((r : ℂ))
      rw [h3, circPt_eq_exp]
      convert h4 using 1
      ring
    simpa using h2.const_add w
  exact ((hg.differentiable one_ne_zero) (w + (r : ℂ) * circPt θ)).hasFDerivAt.comp_hasDerivAt θ h1

theorem integral_polarRad_ray (hg : ContDiff ℝ 1 g) (w : ℂ) {R : ℝ} (hR : 0 < R)
    (hvan : ∀ u : ℂ, R ≤ ‖u‖ → g (w + u) = 0 ∧ fderiv ℝ g (w + u) = 0) (θ : ℝ) :
    ∫ r in Ioi (0 : ℝ), polarRad g w (r, θ) = - g w := by
  have hzero : ∀ r : ℝ, R ≤ r → polarRad g w (r, θ) = 0 := by
    intro r hr
    have hn : R ≤ ‖(r : ℂ) * circPt θ‖ := by
      rw [norm_mul, norm_circPt, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_trans hR.le hr)]
      exact hr
    show fderiv ℝ g (w + (r : ℂ) * circPt θ) (circPt θ) = 0
    rw [(hvan _ hn).2, ContinuousLinearMap.zero_apply]
  have hcont : Continuous fun r : ℝ => polarRad g w (r, θ) :=
    (continuous_polarRad hg w).comp (continuous_id.prodMk continuous_const)
  have hsub : Ioc (0 : ℝ) R ⊆ Ioi (0 : ℝ) := fun x hx => hx.1
  have hrestrict : ∫ r in Ioi (0 : ℝ), polarRad g w (r, θ)
      = ∫ r in Ioc (0 : ℝ) R, polarRad g w (r, θ) := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi hsub ?_
    intro x hx
    have hgt : R < x := by
      rcases hx with ⟨hx1, hx2⟩
      by_contra hle
      exact hx2 ⟨hx1, le_of_not_gt hle⟩
    exact hzero x hgt.le
  rw [hrestrict, ← intervalIntegral.integral_of_le hR.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_along_ray hg w θ x) (hcont.intervalIntegrable _ _)]
  have hRz : g (w + (R : ℂ) * circPt θ) = 0 := by
    refine (hvan _ ?_).1
    rw [norm_mul, norm_circPt, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hR.le]
  have h0 : ((0 : ℝ) : ℂ) * circPt θ = 0 := by simp
  show g (w + (R : ℂ) * circPt θ) - g (w + ((0 : ℝ) : ℂ) * circPt θ) = - g w
  rw [hRz, h0, add_zero, zero_sub]

/-! ### The angular integral -/

theorem circPt_pi : circPt π = -1 := by simp [circPt]

theorem circPt_neg_pi : circPt (-π) = -1 := by simp [circPt]

theorem integral_polarAng_circle (hg : ContDiff ℝ 1 g) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ θ in Ioo (-π) π, polarAng g w (r, θ) = 0 := by
  set D : ℝ → ℂ := fun θ => fderiv ℝ g (w + (r : ℂ) * circPt θ) ((r : ℂ) * (Complex.I * circPt θ))
    with hD
  have hrne : (r : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hr.ne'
  have hsplit : ∀ θ : ℝ, polarAng g w (r, θ) = (Complex.I * (r : ℂ)⁻¹) * D θ := by
    intro θ
    have hlin : D θ = (r : ℂ) * fderiv ℝ g (w + (r : ℂ) * circPt θ) (Complex.I * circPt θ) := by
      show fderiv ℝ g (w + (r : ℂ) * circPt θ) ((r : ℂ) * (Complex.I * circPt θ)) = _
      rw [show ((r : ℂ) * (Complex.I * circPt θ)) = r • (Complex.I * circPt θ) by
        simp [Complex.real_smul], map_smul]
      simp [Complex.real_smul]
    show Complex.I * fderiv ℝ g (w + (r : ℂ) * circPt θ) (Complex.I * circPt θ) = _
    rw [hlin]
    field_simp
  have hcontD : Continuous D := by
    refine (((hg.continuous_fderiv one_ne_zero).comp
      ((continuous_polarBase w).comp (continuous_const.prodMk continuous_id))).clm_apply ?_)
    exact continuous_const.mul (continuous_const.mul continuous_circPt)
  have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  calc ∫ θ in Ioo (-π) π, polarAng g w (r, θ)
      = ∫ θ in Ioo (-π) π, (Complex.I * (r : ℂ)⁻¹) * D θ :=
        setIntegral_congr_fun measurableSet_Ioo fun θ _ => hsplit θ
    _ = (Complex.I * (r : ℂ)⁻¹) * ∫ θ in Ioo (-π) π, D θ := integral_const_mul _ _
    _ = 0 := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun x _ => hasDerivAt_along_circle hg w r x) (hcontD.intervalIntegrable _ _)]
        rw [circPt_pi, circPt_neg_pi]
        ring

/-! ### The inversion formula -/

/-- **The Cauchy transform inverts the Cauchy–Riemann operator.**  For a continuously
differentiable function of compact support, the transform of its anti-holomorphic derivative is the
function itself. -/
theorem cauchyTransform_dbar (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g) (w : ℂ) :
    cauchyTransform (dbar g) w = g w := by
  obtain ⟨R, C, hR, hbd, hvan⟩ := exists_radius_bound hg hsupp w
  -- the change to polar coordinates
  have hpolar : (∫ u : ℂ, dbar g (w + u) / u)
      = ∫ p in Complex.polarCoord.target,
          p.1 • (dbar g (w + Complex.polarCoord.symm p) / Complex.polarCoord.symm p) :=
    (Complex.integral_comp_polarCoord_symm (fun u : ℂ => dbar g (w + u) / u)).symm
  -- on the target the integrand is half the sum of the two halves
  have hint : ∀ p ∈ Complex.polarCoord.target,
      p.1 • (dbar g (w + Complex.polarCoord.symm p) / Complex.polarCoord.symm p)
        = (2 : ℂ)⁻¹ * (polarRad g w p + polarAng g w p) := by
    intro p hp
    rw [Complex.polarCoord_target] at hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    have hsymm : Complex.polarCoord.symm p = (p.1 : ℂ) * circPt p.2 := by
      rw [Complex.polarCoord_symm_apply]
      rfl
    have hp1z : (p.1 : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact hp1.ne'
    have hc : circPt p.2 ≠ 0 := circPt_ne_zero p.2
    have hinv : (circPt p.2)⁻¹ = Complex.exp (-(p.2 : ℂ) * Complex.I) :=
      inv_eq_of_mul_eq_one_left (circPt_mul_conj p.2)
    have hstep : p.1 • (dbar g (w + Complex.polarCoord.symm p) / Complex.polarCoord.symm p)
        = Complex.exp (-(p.2 : ℂ) * Complex.I) * dbar g (w + (p.1 : ℂ) * circPt p.2) := by
      rw [hsymm, Complex.real_smul, ← hinv]
      field_simp
    rw [hstep, polar_dbar g _ p.2]
    rfl
  rw [cauchyTransform, hpolar, setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
    hint, Complex.polarCoord_target]
  -- vanishing and bounds for the two halves
  have hvanRad : ∀ p : ℝ × ℝ, R ≤ p.1 → polarRad g w p = 0 := by
    intro p hp
    have hn : R ≤ ‖(p.1 : ℂ) * circPt p.2‖ := by
      rw [norm_mul, norm_circPt, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_trans hR.le hp)]
      exact hp
    show fderiv ℝ g (w + (p.1 : ℂ) * circPt p.2) (circPt p.2) = 0
    rw [(hvan _ hn).2, ContinuousLinearMap.zero_apply]
  have hvanAng : ∀ p : ℝ × ℝ, R ≤ p.1 → polarAng g w p = 0 := by
    intro p hp
    have hn : R ≤ ‖(p.1 : ℂ) * circPt p.2‖ := by
      rw [norm_mul, norm_circPt, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_trans hR.le hp)]
      exact hp
    show Complex.I * fderiv ℝ g (w + (p.1 : ℂ) * circPt p.2) (Complex.I * circPt p.2) = 0
    rw [(hvan _ hn).2, ContinuousLinearMap.zero_apply, mul_zero]
  have hbdRad : ∀ p : ℝ × ℝ, ‖polarRad g w p‖ ≤ C := by
    intro p
    have h1 := (fderiv ℝ g (w + (p.1 : ℂ) * circPt p.2)).le_opNorm (circPt p.2)
    rw [norm_circPt, mul_one] at h1
    exact le_trans h1 (hbd _)
  have hbdAng : ∀ p : ℝ × ℝ, ‖polarAng g w p‖ ≤ C := by
    intro p
    have h1 := (fderiv ℝ g (w + (p.1 : ℂ) * circPt p.2)).le_opNorm (Complex.I * circPt p.2)
    have hnorm : ‖Complex.I * circPt p.2‖ = 1 := by rw [norm_mul, Complex.norm_I, norm_circPt]; ring
    rw [hnorm, mul_one] at h1
    have h2 : ‖polarAng g w p‖
        = ‖fderiv ℝ g (w + (p.1 : ℂ) * circPt p.2) (Complex.I * circPt p.2)‖ := by
      show ‖Complex.I * fderiv ℝ g (w + (p.1 : ℂ) * circPt p.2) (Complex.I * circPt p.2)‖ = _
      rw [norm_mul, Complex.norm_I, one_mul]
    rw [h2]
    exact le_trans h1 (hbd _)
  have hmemsub : Ioo (0 : ℝ) R ×ˢ Ioo (-π) π ⊆ Ioi (0 : ℝ) ×ˢ Ioo (-π) π :=
    Set.prod_mono (fun x hx => hx.1) (subset_refl _)
  have hIntRad : IntegrableOn (polarRad g w) (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) volume := by
    refine integrableOn_of_bounded_off (continuous_polarRad hg w) hbdRad
      (measurableSet_Ioi.prod measurableSet_Ioo) (measurableSet_Ioo.prod measurableSet_Ioo)
      hmemsub volume_box_ne_top ?_
    intro p hp hpn
    refine hvanRad p ?_
    by_contra hlt
    exact hpn ⟨⟨hp.1, lt_of_not_ge hlt⟩, hp.2⟩
  have hIntAng : IntegrableOn (polarAng g w) (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) volume := by
    refine integrableOn_of_bounded_off (continuous_polarAng hg w) hbdAng
      (measurableSet_Ioi.prod measurableSet_Ioo) (measurableSet_Ioo.prod measurableSet_Ioo)
      hmemsub volume_box_ne_top ?_
    intro p hp hpn
    refine hvanAng p ?_
    by_contra hlt
    exact hpn ⟨⟨hp.1, lt_of_not_ge hlt⟩, hp.2⟩
  rw [integral_const_mul, integral_add hIntRad hIntAng]
  -- the angular half integrates to zero
  have hAng : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, polarAng g w p = 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod _ (by rwa [← Measure.volume_eq_prod])]
    refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
    exact integral_polarAng_circle hg w hr
  -- the radial half integrates to `-2π g w`
  have hRad : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, polarRad g w p
      = ((2 * π : ℝ) : ℂ) * (- g w) := by
    have hswap : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, polarRad g w p
        = ∫ z in Ioo (-π) π ×ˢ Ioi (0 : ℝ), polarRad g w z.swap := by
      rw [Measure.volume_eq_prod]
      exact (setIntegral_prod_swap (Ioi (0 : ℝ)) (Ioo (-π) π) (polarRad g w)).symm
    have hIntSwap : IntegrableOn (fun z : ℝ × ℝ => polarRad g w z.swap)
        (Ioo (-π) π ×ˢ Ioi (0 : ℝ)) volume := by
      refine integrableOn_of_bounded_off (u := Ioo (-π) π ×ˢ Ioo (0 : ℝ) R)
        ((continuous_polarRad hg w).comp continuous_swap) (fun p => hbdRad p.swap)
        (measurableSet_Ioo.prod measurableSet_Ioi) (measurableSet_Ioo.prod measurableSet_Ioo)
        (Set.prod_mono (subset_refl _) fun x hx => hx.1) volume_box_swap_ne_top ?_
      intro p hp hpn
      refine hvanRad p.swap ?_
      by_contra hlt
      exact hpn ⟨hp.1, ⟨hp.2, lt_of_not_ge hlt⟩⟩
    rw [hswap, Measure.volume_eq_prod,
      setIntegral_prod _ (by rwa [← Measure.volume_eq_prod])]
    have hinner : ∀ θ ∈ Ioo (-π) π,
        (∫ r in Ioi (0 : ℝ), polarRad g w ((θ, r) : ℝ × ℝ).swap) = - g w := by
      intro θ _
      exact integral_polarRad_ray hg w hR hvan θ
    rw [setIntegral_congr_fun measurableSet_Ioo hinner, setIntegral_const,
      Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos] : (-π : ℝ) ≤ π)]
    rw [show π - -π = 2 * π by ring, Complex.real_smul]
  rw [hRad, hAng, add_zero]
  have hpi : (π : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.pi_ne_zero
  push_cast
  field_simp

end Rigidity.RET
