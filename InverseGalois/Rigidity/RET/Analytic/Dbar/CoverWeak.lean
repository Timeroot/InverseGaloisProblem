/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverL2

/-!
# A weak solution of the Cauchy–Riemann equation on a covering

The a priori estimate bounds the weighted inner product of a test function with the source by the
weighted norm of the weighted adjoint of the test function, once both sides are damped by the
square root of the curvature of the weight.  A linear functional on the image of the adjoint is
therefore bounded, and the Hahn–Banach theorem extends it to the whole weighted `L²` space, where
the Fréchet–Riesz representation turns it into a vector.  That vector solves the Cauchy–Riemann
equation in the weak sense, with a norm controlled by the damped source.

## Main definitions

* `Rigidity.RET.curv`, `Rigidity.RET.sqrtCurv` — the curvature of a weight and its square root.
* `Rigidity.RET.testFn` — the test functions on the total space.
* `Rigidity.RET.dampSrc`, `Rigidity.RET.dampTest` — the damping by the square root of the curvature.

## Main results

* `Rigidity.RET.exists_weak_solution` — **a weak solution of the Cauchy–Riemann equation** on the
  total space of a covering, with an `L²` bound.
-/

open MeasureTheory Topology ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f u v g : Y → ℂ} {y : Y} {z : ℂ} {Φ : ℂ → ℂ}

/-! ### The curvature of a weight -/

/-- **The curvature of a weight.** -/
def curv (Φ : ℂ → ℂ) (z : ℂ) : ℝ := (dbar (dz Φ) z).re

/-- The curvature of a smooth weight is continuous. -/
theorem continuous_curv (hΦ : ContDiff ℝ 2 Φ) : Continuous (curv Φ) :=
  Complex.continuous_re.comp (continuous_dbar (contDiff_one_dz hΦ))

/-- The square root of the curvature. -/
def sqrtCurv (Φ : ℂ → ℂ) (z : ℂ) : ℝ := Real.sqrt (curv Φ z)

/-- The square root of the curvature of a smooth weight is continuous. -/
theorem continuous_sqrtCurv (hΦ : ContDiff ℝ 2 Φ) : Continuous (sqrtCurv Φ) :=
  Real.continuous_sqrt.comp (continuous_curv hΦ)

/-- The square root of a positive curvature is positive. -/
theorem sqrtCurv_pos (h : 0 < curv Φ z) : 0 < sqrtCurv Φ z := Real.sqrt_pos.mpr h

/-- The square root of a nonnegative curvature squares back to it. -/
theorem sq_sqrtCurv (h : 0 ≤ curv Φ z) : sqrtCurv Φ z ^ 2 = curv Φ z := Real.sq_sqrt h

/-! ### The test functions -/

/-- **The test functions on the total space of a covering**: the twice continuously differentiable
functions of compact support. -/
def testFn (hlh : IsLocalHomeomorph f) : Submodule ℂ (Y → ℂ) where
  carrier := {w | (∀ y, IsC2At f w y) ∧ HasCompactSupport w}
  add_mem' ha hb := ⟨fun y => (ha.1 y).add (hb.1 y), ha.2.add hb.2⟩
  zero_mem' := ⟨fun y => isC2At_const hlh 0 y, HasCompactSupport.zero⟩
  smul_mem' c _w hw :=
    ⟨fun y => (hw.1 y).const_mul c, hw.2.comp_left (g := fun t => c * t) (mul_zero c)⟩

section TestFunctions

variable {hlh : IsLocalHomeomorph f}

/-- A test function is twice continuously differentiable. -/
theorem testFn.isC2At {w : Y → ℂ} (hw : w ∈ testFn hlh) (y : Y) : IsC2At f w y := hw.1 y

/-- A test function has compact support. -/
theorem testFn.hasCompactSupport {w : Y → ℂ} (hw : w ∈ testFn hlh) : HasCompactSupport w := hw.2

/-- A test function is continuous. -/
theorem testFn.continuous (hlh : IsLocalHomeomorph f) {w : Y → ℂ} (hw : w ∈ testFn hlh) :
    Continuous w := continuous_of_isC1At hlh fun y => (hw.1 y).isC1At

end TestFunctions

/-- The weighted adjoint of a twice continuously differentiable function is continuous. -/
theorem continuous_deltaOpY_of_isC2At (hlh : IsLocalHomeomorph f) (hΦ : ContDiff ℝ 2 Φ)
    (hu : ∀ y, IsC2At f u y) : Continuous (deltaOpY hlh Φ u) :=
  continuous_of_isC1At hlh fun y => isC1At_deltaOpY hlh hΦ hu y

/-! ### Damping by the curvature -/

variable (f Φ) in
/-- The source of the equation, damped by the square root of the curvature. -/
def dampSrc (g : Y → ℂ) : Y → ℂ := fun y => g y * (((sqrtCurv Φ (f y))⁻¹ : ℝ) : ℂ)

variable (f Φ) in
/-- A test function, amplified by the square root of the curvature. -/
def dampTest (w : Y → ℂ) : Y → ℂ := fun y => ((sqrtCurv Φ (f y) : ℝ) : ℂ) * w y

/-- The damped source is continuous. -/
theorem continuous_dampSrc (hf : Continuous f) (hlh : IsLocalHomeomorph f)
    (hΦ : ContDiff ℝ 2 Φ) (hpos : ∀ t, 0 < curv Φ t) (hg1 : ∀ y, IsC1At f g y) :
    Continuous (dampSrc f Φ g) := by
  have hs : Continuous fun y => sqrtCurv Φ (f y) := (continuous_sqrtCurv hΦ).comp hf
  have hi : Continuous fun y => (sqrtCurv Φ (f y))⁻¹ :=
    hs.inv₀ fun y => (sqrtCurv_pos (hpos (f y))).ne'
  exact (continuous_of_isC1At hlh hg1).mul (Complex.continuous_ofReal.comp hi)

/-- The damped source has compact support. -/
theorem hasCompactSupport_dampSrc (hgs : HasCompactSupport g) :
    HasCompactSupport (dampSrc f Φ g) := hgs.mul_right

/-- The amplified test function is continuous. -/
theorem continuous_dampTest (hf : Continuous f) (hΦ : ContDiff ℝ 2 Φ) {w : Y → ℂ}
    (hwc : Continuous w) : Continuous (dampTest f Φ w) := by
  have hs : Continuous fun y => sqrtCurv Φ (f y) := (continuous_sqrtCurv hΦ).comp hf
  exact (Complex.continuous_ofReal.comp hs).mul hwc

/-- The amplified test function has compact support. -/
theorem hasCompactSupport_dampTest {w : Y → ℂ} (hws : HasCompactSupport w) :
    HasCompactSupport (dampTest f Φ w) := hws.mul_left

omit [TopologicalSpace Y] in
/-- **Damping cancels**: the damped source and the amplified test function pair as the original
ones do. -/
theorem dampTest_mul_conj_dampSrc (hpos : ∀ t, 0 < curv Φ t) (w : Y → ℂ) (y : Y) :
    dampTest f Φ w y * conj (dampSrc f Φ g y) = w y * conj (g y) := by
  have h : ((sqrtCurv Φ (f y) : ℝ) : ℂ) * (((sqrtCurv Φ (f y))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (sqrtCurv_pos (hpos (f y))).ne', Complex.ofReal_one]
  calc dampTest f Φ w y * conj (dampSrc f Φ g y)
      = (((sqrtCurv Φ (f y) : ℝ) : ℂ) * (((sqrtCurv Φ (f y))⁻¹ : ℝ) : ℂ))
          * (w y * conj (g y)) := by
        simp only [dampTest, dampSrc, map_mul, Complex.conj_ofReal]
        ring
    _ = w y * conj (g y) := by rw [h, one_mul]

/-! ### The weighted inner product after damping -/

omit [TopologicalSpace Y] in
/-- The weighted inner product only sees the product of the two functions. -/
theorem wipY_congr {u' v' : Y → ℂ} (h : ∀ y, u y * conj (v y) = u' y * conj (v' y)) :
    wipY f Φ u v = wipY f Φ u' v' := by
  have h2 : (fun y => u y * conj (v y) * Complex.exp (-(Φ (f y))))
      = fun y => u' y * conj (v' y) * Complex.exp (-(Φ (f y))) := by
    funext y
    rw [h y]
  simp only [wipY, h2]

omit [TopologicalSpace Y] in
/-- The weighted square norm of an amplified test function is the curvature integral. -/
theorem wnorm2Y_dampTest (hpos : ∀ t, 0 < curv Φ t) (w : Y → ℂ) :
    wnorm2Y f Φ (dampTest f Φ w)
      = ∫ z : ℂ, fibreSum f (fun y => curv Φ (f y) * ‖w y‖ ^ 2
          * Real.exp (-(Φ (f y)).re)) z := by
  have h : (fun y => ‖dampTest f Φ w y‖ ^ 2 * Real.exp (-(Φ (f y)).re))
      = fun y => curv Φ (f y) * ‖w y‖ ^ 2 * Real.exp (-(Φ (f y)).re) := by
    funext y
    have hn : ‖dampTest f Φ w y‖ = sqrtCurv Φ (f y) * ‖w y‖ := by
      simp [dampTest, sqrtCurv, abs_of_nonneg (Real.sqrt_nonneg (curv Φ (f y)))]
    rw [hn, mul_pow, sq_sqrtCurv (hpos (f y)).le]
  simp only [wnorm2Y, h]

/-! ### The weak solution -/

section Weak

variable (hfin : ∀ z, (f ⁻¹' {z}).Finite)
  (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
  (hlh : IsLocalHomeomorph f) (hΦ : ContDiff ℝ 2 Φ) (hreal : ∀ t, conj (Φ t) = Φ t)
  (hpos : ∀ t, 0 < curv Φ t) (hg1 : ∀ y, IsC1At f g y) (hgs : HasCompactSupport g)
  [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Pairing an element of the weighted `L²` space with a continuous function of compact
support. -/
theorem inner_toL2_right (hΦc : Continuous Φ)
    (U : Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦc)) {F : Y → ℂ} (hFc : Continuous F)
    (hFs : HasCompactSupport F) :
    inner ℂ U (toL2 hfin hcov hf hΦc hFc hFs)
      = ∫ y, F y * conj (U y) ∂(coverL2Measure f Φ hfin hcov hf hΦc) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 hfin hcov hf hΦc hFc hFs] with y hy
  simp only [hy, RCLike.inner_apply]

/-- A test function, as an element of the weighted `L²` space. -/
def testL2 : testFn hlh →ₗ[ℂ] Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦ.continuous) where
  toFun w := toL2 hfin hcov hf hΦ.continuous (testFn.continuous hlh w.2)
    (testFn.hasCompactSupport w.2)
  map_add' w₁ w₂ := by
    exact toL2_add hfin hcov hf hΦ.continuous
      (testFn.continuous hlh w₁.2) (testFn.hasCompactSupport w₁.2)
      (testFn.continuous hlh w₂.2) (testFn.hasCompactSupport w₂.2)
      (testFn.continuous hlh (w₁ + w₂).2) (testFn.hasCompactSupport (w₁ + w₂).2)
  map_smul' c w := by
    exact toL2_const_smul hfin hcov hf hΦ.continuous c
      (testFn.continuous hlh w.2) (testFn.hasCompactSupport w.2)
      (testFn.continuous hlh (c • w).2) (testFn.hasCompactSupport (c • w).2)

@[simp]
theorem testL2_apply (w : testFn hlh) :
    testL2 hfin hcov hf hlh hΦ w = toL2 hfin hcov hf hΦ.continuous
      (testFn.continuous hlh w.2) (testFn.hasCompactSupport w.2) := rfl

/-- The weighted adjoint of a test function, as an element of the weighted `L²` space. -/
def deltaL2 : testFn hlh →ₗ[ℂ] Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦ.continuous) where
  toFun w := toL2 hfin hcov hf hΦ.continuous
    (continuous_deltaOpY_of_isC2At hlh hΦ w.2.1) (hasCompactSupport_deltaOpY hlh w.2.2)
  map_add' w₁ w₂ := by
    have h1 : Continuous fun y => deltaOpY hlh Φ (↑w₁ : Y → ℂ) y
        + deltaOpY hlh Φ (↑w₂ : Y → ℂ) y :=
      (continuous_deltaOpY_of_isC2At hlh hΦ w₁.2.1).add
        (continuous_deltaOpY_of_isC2At hlh hΦ w₂.2.1)
    have h2 : HasCompactSupport fun y => deltaOpY hlh Φ (↑w₁ : Y → ℂ) y
        + deltaOpY hlh Φ (↑w₂ : Y → ℂ) y :=
      (hasCompactSupport_deltaOpY hlh w₁.2.2).add (hasCompactSupport_deltaOpY hlh w₂.2.2)
    have hfun : deltaOpY hlh Φ (↑(w₁ + w₂) : Y → ℂ)
        = fun y => deltaOpY hlh Φ (↑w₁ : Y → ℂ) y + deltaOpY hlh Φ (↑w₂ : Y → ℂ) y := by
      funext y
      exact deltaOpY_add (w₁.2.1 y).isDiffAt (w₂.2.1 y).isDiffAt
    calc toL2 hfin hcov hf hΦ.continuous
          (continuous_deltaOpY_of_isC2At hlh hΦ (w₁ + w₂).2.1)
          (hasCompactSupport_deltaOpY hlh (w₁ + w₂).2.2)
        = toL2 hfin hcov hf hΦ.continuous h1 h2 :=
          toL2_congr hfin hcov hf hΦ.continuous _ _ h1 h2 hfun
      _ = _ := toL2_add hfin hcov hf hΦ.continuous _ _ _ _ h1 h2
  map_smul' c w := by
    have h1 : Continuous fun y => c * deltaOpY hlh Φ (↑w : Y → ℂ) y :=
      continuous_const.mul (continuous_deltaOpY_of_isC2At hlh hΦ w.2.1)
    have h2 : HasCompactSupport fun y => c * deltaOpY hlh Φ (↑w : Y → ℂ) y :=
      (hasCompactSupport_deltaOpY hlh w.2.2).comp_left (g := fun t => c * t) (mul_zero c)
    have hfun : deltaOpY hlh Φ (↑(c • w) : Y → ℂ)
        = fun y => c * deltaOpY hlh Φ (↑w : Y → ℂ) y := by
      funext y
      exact deltaOpY_const_mul c (w.2.1 y).isDiffAt
    calc toL2 hfin hcov hf hΦ.continuous
          (continuous_deltaOpY_of_isC2At hlh hΦ (c • w).2.1)
          (hasCompactSupport_deltaOpY hlh (c • w).2.2)
        = toL2 hfin hcov hf hΦ.continuous h1 h2 :=
          toL2_congr hfin hcov hf hΦ.continuous _ _ h1 h2 hfun
      _ = _ := toL2_const_smul hfin hcov hf hΦ.continuous c _ _ h1 h2

@[simp]
theorem deltaL2_apply (w : testFn hlh) :
    deltaL2 hfin hcov hf hlh hΦ w = toL2 hfin hcov hf hΦ.continuous
      (continuous_deltaOpY_of_isC2At hlh hΦ w.2.1) (hasCompactSupport_deltaOpY hlh w.2.2) := rfl

/-- **The functional whose representing vector is the weak solution.** -/
def srcFunctional : testFn hlh →ₗ[ℂ] ℂ :=
  (innerSL ℂ (toL2 hfin hcov hf hΦ.continuous (continuous_of_isC1At hlh hg1) hgs)).toLinearMap ∘ₗ
    testL2 hfin hcov hf hlh hΦ

include hreal in
theorem srcFunctional_apply (w : testFn hlh) :
    srcFunctional hfin hcov hf hlh hΦ hg1 hgs w = wipY f Φ (↑w : Y → ℂ) g := by
  have h := inner_toL2 hfin hcov hf hΦ.continuous hreal
    (continuous_of_isC1At hlh hg1) hgs (testFn.continuous hlh w.2)
    (testFn.hasCompactSupport w.2)
  simpa only [srcFunctional, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, testL2_apply] using h

include hreal hpos in
/-- **The a priori bound on the functional**, from the curvature estimate. -/
theorem srcFunctional_norm_le (w : testFn hlh) :
    ‖srcFunctional hfin hcov hf hlh hΦ hg1 hgs w‖
      ≤ ‖toL2 hfin hcov hf hΦ.continuous (continuous_dampSrc hf hlh hΦ hpos hg1)
          (hasCompactSupport_dampSrc hgs)‖ * ‖deltaL2 hfin hcov hf hlh hΦ w‖ := by
  have hac := continuous_dampSrc (g := g) hf hlh hΦ hpos hg1
  have has := hasCompactSupport_dampSrc (f := f) (Φ := Φ) hgs
  have hbc := continuous_dampTest (w := (↑w : Y → ℂ)) hf hΦ (testFn.continuous hlh w.2)
  have hbs := hasCompactSupport_dampTest (f := f) (Φ := Φ) (testFn.hasCompactSupport w.2)
  -- the functional is the inner product of the damped source with the amplified test function
  have hval : srcFunctional hfin hcov hf hlh hΦ hg1 hgs w
      = inner ℂ (toL2 hfin hcov hf hΦ.continuous hac has)
        (toL2 hfin hcov hf hΦ.continuous hbc hbs) := by
    rw [srcFunctional_apply hfin hcov hf hlh hΦ hreal hg1 hgs w,
      inner_toL2 hfin hcov hf hΦ.continuous hreal hac has hbc hbs]
    exact (wipY_congr fun y => dampTest_mul_conj_dampSrc hpos (↑w : Y → ℂ) y).symm
  -- the amplified test function is dominated by the adjoint
  have hsq : ‖toL2 hfin hcov hf hΦ.continuous hbc hbs‖ ^ 2
      ≤ ‖deltaL2 hfin hcov hf hlh hΦ w‖ ^ 2 := by
    rw [norm_toL2_sq hfin hcov hf hΦ.continuous hreal hbc hbs, deltaL2_apply,
      norm_toL2_sq hfin hcov hf hΦ.continuous hreal _ _,
      wnorm2Y_dampTest hpos (↑w : Y → ℂ)]
    exact curvature_estimateY hfin hcov hlh hΦ hreal w.2.1 w.2.2
  have hle : ‖toL2 hfin hcov hf hΦ.continuous hbc hbs‖
      ≤ ‖deltaL2 hfin hcov hf hlh hΦ w‖ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  calc ‖srcFunctional hfin hcov hf hlh hΦ hg1 hgs w‖
      = ‖inner ℂ (toL2 hfin hcov hf hΦ.continuous hac has)
          (toL2 hfin hcov hf hΦ.continuous hbc hbs)‖ := by rw [hval]
    _ ≤ ‖toL2 hfin hcov hf hΦ.continuous hac has‖
          * ‖toL2 hfin hcov hf hΦ.continuous hbc hbs‖ := norm_inner_le_norm _ _
    _ ≤ ‖toL2 hfin hcov hf hΦ.continuous hac has‖ * ‖deltaL2 hfin hcov hf hlh hΦ w‖ :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)

include hreal hpos hg1 hgs in
/-- **A weak solution of the Cauchy–Riemann equation on the total space of a covering.** -/
theorem exists_weak_solution :
    ∃ U : Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦ.continuous),
      ‖U‖ ^ 2 ≤ wnorm2Y f Φ (dampSrc f Φ g) ∧
      ∀ w : Y → ℂ, (∀ y, IsC2At f w y) → HasCompactSupport w →
        (∫ y, deltaOpY hlh Φ w y * conj (U y)
            ∂(coverL2Measure f Φ hfin hcov hf hΦ.continuous)) = wipY f Φ w g := by
  have hac := continuous_dampSrc (g := g) hf hlh hΦ hpos hg1
  have has := hasCompactSupport_dampSrc (f := f) (Φ := Φ) hgs
  have hbd := srcFunctional_norm_le hfin hcov hf hlh hΦ hreal hpos hg1 hgs
  have hex : ∃ C : ℝ, ∀ w : testFn hlh,
      ‖srcFunctional hfin hcov hf hlh hΦ hg1 hgs w‖
        ≤ C * ‖deltaL2 hfin hcov hf hlh hΦ w‖ :=
    ⟨‖toL2 hfin hcov hf hΦ.continuous hac has‖, hbd⟩
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : LinearMap.range (deltaL2 hfin hcov hf hlh hΦ) →L[ℂ] ℂ,
      ∀ (p : LinearMap.range (deltaL2 hfin hcov hf hlh hΦ)) (w : testFn hlh),
        deltaL2 hfin hcov hf hlh hΦ w = (p : Lp ℂ 2 _) →
          L₁ p = srcFunctional hfin hcov hf hlh hΦ hg1 hgs w := by
    refine ⟨(srcFunctional hfin hcov hf hlh hΦ hg1 hgs).compLeftInverse
      (deltaL2 hfin hcov hf hlh hΦ), ?_⟩
    rintro ⟨x, hx⟩ w hw
    subst hw
    exact LinearMap.compLeftInverse_apply_of_bdd _ _ hex w _ rfl
  have hL₁norm : ‖L₁‖ ≤ ‖toL2 hfin hcov hf hΦ.continuous hac has‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun p => ?_
    obtain ⟨w, hw⟩ := p.2
    calc ‖L₁ p‖ = ‖srcFunctional hfin hcov hf hlh hΦ hg1 hgs w‖ := by rw [hL₁ p w hw]
      _ ≤ ‖toL2 hfin hcov hf hΦ.continuous hac has‖ * ‖deltaL2 hfin hcov hf hlh hΦ w‖ := hbd w
      _ = ‖toL2 hfin hcov hf hΦ.continuous hac has‖ * ‖p‖ := by
          congr 1
          exact congrArg norm hw
  obtain ⟨L₂, hL₂ext, hL₂norm⟩ :=
    exists_extension_norm_eq (LinearMap.range (deltaL2 hfin hcov hf hlh hΦ)) L₁
  obtain ⟨U, hU⟩ : ∃ U : Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦ.continuous),
      U = (InnerProductSpace.toDual ℂ (Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦ.continuous))).symm
        L₂ := ⟨_, rfl⟩
  have hUnorm : ‖U‖ ≤ ‖toL2 hfin hcov hf hΦ.continuous hac has‖ := by
    rw [hU, LinearIsometryEquiv.norm_map, hL₂norm]
    exact hL₁norm
  have hUinner : ∀ x : Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦ.continuous),
      inner ℂ U x = L₂ x := by
    intro x
    rw [hU]
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨U, ?_, ?_⟩
  · calc ‖U‖ ^ 2 ≤ ‖toL2 hfin hcov hf hΦ.continuous hac has‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hUnorm 2
      _ = wnorm2Y f Φ (dampSrc f Φ g) := norm_toL2_sq hfin hcov hf hΦ.continuous hreal hac has
  · intro w hw1 hw2
    have hW : w ∈ testFn hlh := ⟨hw1, hw2⟩
    have hmem : deltaL2 hfin hcov hf hlh hΦ ⟨w, hW⟩
        ∈ LinearMap.range (deltaL2 hfin hcov hf hlh hΦ) := ⟨⟨w, hW⟩, rfl⟩
    calc (∫ y, deltaOpY hlh Φ w y * conj (U y)
            ∂(coverL2Measure f Φ hfin hcov hf hΦ.continuous))
        = inner ℂ U (deltaL2 hfin hcov hf hlh hΦ ⟨w, hW⟩) :=
          (inner_toL2_right hfin hcov hf hΦ.continuous U
            (continuous_deltaOpY_of_isC2At hlh hΦ hw1)
            (hasCompactSupport_deltaOpY hlh hw2)).symm
      _ = L₂ (deltaL2 hfin hcov hf hlh hΦ ⟨w, hW⟩) := hUinner _
      _ = L₁ ⟨deltaL2 hfin hcov hf hlh hΦ ⟨w, hW⟩, hmem⟩ :=
          hL₂ext ⟨deltaL2 hfin hcov hf hlh hΦ ⟨w, hW⟩, hmem⟩
      _ = srcFunctional hfin hcov hf hlh hΦ hg1 hgs ⟨w, hW⟩ := hL₁ _ ⟨w, hW⟩ rfl
      _ = wipY f Φ w g := srcFunctional_apply hfin hcov hf hlh hΦ hreal hg1 hgs ⟨w, hW⟩

end Weak

end Rigidity.RET

end
