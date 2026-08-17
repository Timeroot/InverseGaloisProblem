/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Basic

/-!
# Integration by parts for the Cauchy–Riemann operator

The plane integral of `∂F/∂z̄` vanishes whenever `F` is continuously differentiable with compact
support: reading the plane as a product of two lines, each of the two coordinate derivatives
integrates to zero along its own line by the fundamental theorem of calculus, and Fubini's theorem
turns that into the vanishing of the plane integral.  Applying this to a product gives the rule
that moves the operator from one factor to the other, which is the first ingredient of every
`L²` estimate for the operator.

## Main results

* `Rigidity.RET.integral_complex_eq_iterated` — the plane integral as an iterated integral.
* `Rigidity.RET.integral_dbar_eq_zero` — the plane integral of `∂F/∂z̄` vanishes on compactly
  supported functions.
* `Rigidity.RET.integral_dbar_mul` — the operator moves from one factor of a product to the other.
-/

open MeasureTheory Set

noncomputable section

namespace Rigidity.RET

/-! ### The plane integral as an iterated integral -/

/-- Reading the plane as a product of two lines. -/
theorem integral_complex_eq_prod (F : ℂ → ℂ) :
    ∫ p : ℝ × ℝ, F ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) = ∫ z : ℂ, F z := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd).integral_comp' F
  simpa [Complex.mk_eq_add_mul_I] using h

/-- Integrability transports to the product of two lines. -/
theorem integrable_prod_of_integrable {F : ℂ → ℂ} (hF : Integrable F) :
    Integrable (fun p : ℝ × ℝ => F ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd).integrable_comp_emb
      (Complex.measurableEquivRealProd.symm.measurableEmbedding) (g := F)
  have h' := h.2 hF
  simpa [Function.comp_def, Complex.mk_eq_add_mul_I] using h'

/-- **The plane integral is the iterated integral**, the real part on the outside. -/
theorem integral_complex_eq_iterated (F : ℂ → ℂ) (hF : Integrable F) :
    ∫ x : ℝ, ∫ y : ℝ, F ((x : ℂ) + (y : ℂ) * Complex.I) = ∫ z : ℂ, F z := by
  have hint : Integrable
      (Function.uncurry fun x y : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I))
      ((volume : Measure ℝ).prod volume) :=
    integrable_prod_of_integrable hF
  have h := MeasureTheory.integral_integral hint
  rw [h, ← MeasureTheory.Measure.volume_eq_prod, integral_complex_eq_prod]

/-- **The plane integral is the iterated integral**, the imaginary part on the outside. -/
theorem integral_complex_eq_iterated' (F : ℂ → ℂ) (hF : Integrable F) :
    ∫ y : ℝ, ∫ x : ℝ, F ((x : ℂ) + (y : ℂ) * Complex.I) = ∫ z : ℂ, F z := by
  have hint : Integrable
      (Function.uncurry fun x y : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I))
      ((volume : Measure ℝ).prod volume) :=
    integrable_prod_of_integrable hF
  rw [← MeasureTheory.integral_integral_swap hint]
  exact integral_complex_eq_iterated F hF

/-! ### Compact support along the coordinate lines -/

/-- A compactly supported function vanishes outside a disc. -/
theorem exists_bound_of_hasCompactSupport {F : ℂ → ℂ} (hs : HasCompactSupport F) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : ℂ, R < ‖z‖ → F z = 0 := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max R 0, le_max_right _ _, fun z hz => ?_⟩
  by_contra hne
  have hmem : z ∈ tsupport F := subset_closure hne
  have := hR hmem
  simp only [Metric.mem_closedBall, dist_zero_right] at this
  exact absurd (this.trans (le_max_left R 0)) (not_le.2 hz)

/-- The restriction to a horizontal line of a compactly supported function is compactly
supported. -/
theorem hasCompactSupport_line_re {F : ℂ → ℂ} (hs : HasCompactSupport F) (y : ℝ) :
    HasCompactSupport (fun t : ℝ => F ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_of_hasCompactSupport hs
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun t ht => ?_
  refine hR _ ?_
  have habs : R < |t| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · calc R < -t := by linarith
        _ ≤ |t| := neg_le_abs t
    · exact h.trans_le (le_abs_self t)
  have hre : (((t : ℂ) + (y : ℂ) * Complex.I)).re = t := by simp
  calc R < |t| := habs
    _ = |(((t : ℂ) + (y : ℂ) * Complex.I)).re| := by rw [hre]
    _ ≤ ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ := Complex.abs_re_le_norm _

/-- The restriction to a vertical line of a compactly supported function is compactly
supported. -/
theorem hasCompactSupport_line_im {F : ℂ → ℂ} (hs : HasCompactSupport F) (x : ℝ) :
    HasCompactSupport (fun t : ℝ => F ((x : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_of_hasCompactSupport hs
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun t ht => ?_
  refine hR _ ?_
  have habs : R < |t| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · calc R < -t := by linarith
        _ ≤ |t| := neg_le_abs t
    · exact h.trans_le (le_abs_self t)
  have him : (((x : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
  calc R < |t| := habs
    _ = |(((x : ℂ) + (t : ℂ) * Complex.I)).im| := by rw [him]
    _ ≤ ‖((x : ℂ) + (t : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _

/-! ### The line integral of a derivative -/

/-- The integral over the whole line of the derivative of a compactly supported function
vanishes. -/
theorem integral_deriv_eq_zero {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) :
    ∫ x : ℝ, deriv g x = 0 := by
  have hint : Integrable (deriv g) :=
    (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hs.deriv
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hint.integrableOn hint.integrableOn,
    HasCompactSupport.integral_Iic_deriv_eq hg hs 0,
    HasCompactSupport.integral_Ioi_deriv_eq hg hs 0, add_neg_cancel]

/-! ### The two coordinate derivatives -/

/-- The plane integral of the derivative in the real direction vanishes. -/
theorem integral_fderiv_one {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) :
    ∫ z : ℂ, fderiv ℝ F z 1 = 0 := by
  set Φ : ℂ → ℂ := fun z => fderiv ℝ F z 1 with hΦ
  have hcont : Continuous Φ := (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsupp : HasCompactSupport Φ :=
    HasCompactSupport.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L 1) (hs.fderiv (𝕜 := ℝ)) (by simp)
  have hint : Integrable Φ := hcont.integrable_of_hasCompactSupport hsupp
  rw [← integral_complex_eq_iterated' Φ hint]
  have hzero : ∀ y : ℝ, (∫ x : ℝ, Φ ((x : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    intro y
    have haff : ContDiff ℝ 1 (fun t : ℝ => ((t : ℂ) + (y : ℂ) * Complex.I)) := by
      have := (Complex.ofRealCLM.contDiff (n := 1)).add
        (contDiff_const (c := ((y : ℂ) * Complex.I)))
      simpa using this
    have hline : ContDiff ℝ 1 (fun t : ℝ => F ((t : ℂ) + (y : ℂ) * Complex.I)) := hF.comp haff
    have hderiv : ∀ x : ℝ,
        deriv (fun t : ℝ => F ((t : ℂ) + (y : ℂ) * Complex.I)) x = Φ ((x : ℂ) + (y : ℂ) * Complex.I) := by
      intro x
      have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ) + (y : ℂ) * Complex.I)) 1 x := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
      have h2 : HasFDerivAt F (fderiv ℝ F ((x : ℂ) + (y : ℂ) * Complex.I))
          ((x : ℂ) + (y : ℂ) * Complex.I) := (hF.differentiable one_ne_zero _).hasFDerivAt
      exact (h2.comp_hasDerivAt x h1).deriv
    calc (∫ x : ℝ, Φ ((x : ℂ) + (y : ℂ) * Complex.I))
        = ∫ x : ℝ, deriv (fun t : ℝ => F ((t : ℂ) + (y : ℂ) * Complex.I)) x := by
          simp_rw [hderiv]
      _ = 0 := integral_deriv_eq_zero hline (hasCompactSupport_line_re hs y)
  simp_rw [hzero]
  simp

/-- The plane integral of the derivative in the imaginary direction vanishes. -/
theorem integral_fderiv_I {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) :
    ∫ z : ℂ, fderiv ℝ F z Complex.I = 0 := by
  set Φ : ℂ → ℂ := fun z => fderiv ℝ F z Complex.I with hΦ
  have hcont : Continuous Φ := (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsupp : HasCompactSupport Φ :=
    HasCompactSupport.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L Complex.I) (hs.fderiv (𝕜 := ℝ)) (by simp)
  have hint : Integrable Φ := hcont.integrable_of_hasCompactSupport hsupp
  rw [← integral_complex_eq_iterated Φ hint]
  have hzero : ∀ x : ℝ, (∫ y : ℝ, Φ ((x : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    intro x
    have haff : ContDiff ℝ 1 (fun t : ℝ => ((x : ℂ) + (t : ℂ) * Complex.I)) := by
      have := (contDiff_const (c := (x : ℂ))).add
        ((Complex.ofRealCLM.contDiff (n := 1)).mul (contDiff_const (c := Complex.I)))
      simpa using this
    have hline : ContDiff ℝ 1 (fun t : ℝ => F ((x : ℂ) + (t : ℂ) * Complex.I)) := hF.comp haff
    have hderiv : ∀ t : ℝ,
        deriv (fun s : ℝ => F ((x : ℂ) + (s : ℂ) * Complex.I)) t = Φ ((x : ℂ) + (t : ℂ) * Complex.I) := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => ((x : ℂ) + (s : ℂ) * Complex.I)) Complex.I t := by
        simpa using
          ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add ((x : ℂ))
      have h2 : HasFDerivAt F (fderiv ℝ F ((x : ℂ) + (t : ℂ) * Complex.I))
          ((x : ℂ) + (t : ℂ) * Complex.I) := (hF.differentiable one_ne_zero _).hasFDerivAt
      exact (h2.comp_hasDerivAt t h1).deriv
    calc (∫ y : ℝ, Φ ((x : ℂ) + (y : ℂ) * Complex.I))
        = ∫ y : ℝ, deriv (fun s : ℝ => F ((x : ℂ) + (s : ℂ) * Complex.I)) y := by
          simp_rw [hderiv]
      _ = 0 := integral_deriv_eq_zero hline (hasCompactSupport_line_im hs x)
  simp_rw [hzero]
  simp

/-! ### The operator on compactly supported functions -/

/-- The operator preserves compact support. -/
theorem hasCompactSupport_dbar {F : ℂ → ℂ} (hs : HasCompactSupport F) :
    HasCompactSupport (dbar F) :=
  HasCompactSupport.comp_left
    (g := fun L : ℂ →L[ℝ] ℂ => (2 : ℂ)⁻¹ * (L 1 + Complex.I * L Complex.I)) (hs.fderiv (𝕜 := ℝ)) (by simp)

/-- The operator preserves continuity. -/
theorem continuous_dbar {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) : Continuous (dbar F) := by
  have h := hF.continuous_fderiv one_ne_zero
  exact continuous_const.mul
    ((h.clm_apply continuous_const).add (continuous_const.mul (h.clm_apply continuous_const)))

/-- The operator sends a compactly supported function to an integrable one. -/
theorem integrable_dbar {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) :
    Integrable (dbar F) :=
  (continuous_dbar hF).integrable_of_hasCompactSupport (hasCompactSupport_dbar hs)

/-- **The plane integral of `∂F/∂z̄` vanishes** on continuously differentiable functions of
compact support. -/
theorem integral_dbar_eq_zero {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) :
    ∫ z : ℂ, dbar F z = 0 := by
  have hcont := hF.continuous_fderiv one_ne_zero
  have h1 : Integrable (fun z : ℂ => fderiv ℝ F z 1) :=
    (hcont.clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L 1) (hs.fderiv (𝕜 := ℝ)) (by simp))
  have h2 : Integrable (fun z : ℂ => Complex.I * fderiv ℝ F z Complex.I) :=
    ((continuous_const.mul (hcont.clm_apply continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_left
        (g := fun L : ℂ →L[ℝ] ℂ => Complex.I * L Complex.I) (hs.fderiv (𝕜 := ℝ)) (by simp))
  simp only [dbar]
  rw [integral_const_mul, integral_add h1 h2, integral_const_mul,
    integral_fderiv_one hF hs, integral_fderiv_I hF hs]
  simp

/-! ### Moving the operator across a product -/

/-- **Integration by parts**: the operator moves from one factor of a product to the other. -/
theorem integral_dbar_mul {f g : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) :
    (∫ z : ℂ, dbar f z * g z) = -∫ z : ℂ, f z * dbar g z := by
  have hprod : ContDiff ℝ 1 (fun z : ℂ => f z * g z) := hf.mul hg
  have hprods : HasCompactSupport (fun z : ℂ => f z * g z) := hs.mul_left
  have hrule : ∀ z : ℂ, dbar (fun w => f w * g w) z = f z * dbar g z + g z * dbar f z := fun z =>
    dbar_mul (hf.differentiable one_ne_zero z) (hg.differentiable one_ne_zero z)
  have hi1 : Integrable (fun z : ℂ => f z * dbar g z) :=
    (hf.continuous.mul (continuous_dbar hg)).integrable_of_hasCompactSupport
      (hasCompactSupport_dbar hs).mul_left
  have hi2 : Integrable (fun z : ℂ => g z * dbar f z) :=
    (hg.continuous.mul (continuous_dbar hf)).integrable_of_hasCompactSupport hs.mul_right
  have hzero := integral_dbar_eq_zero hprod hprods
  simp_rw [hrule] at hzero
  rw [integral_add hi1 hi2] at hzero
  have : (∫ z : ℂ, g z * dbar f z) = ∫ z : ℂ, dbar f z * g z := by simp_rw [mul_comm]
  rw [this] at hzero
  linear_combination hzero

end Rigidity.RET

end
