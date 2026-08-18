/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverChart
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverWeak

/-!
# Test functions on a covering from test functions in a coordinate

A test function of a complex variable supported in a disc contained in the target of a local
coordinate lifts to the total space of a covering: conjugate it, amplify it by the weight, read it
through the coordinate and extend it by zero.  The lift is a test function of the total space, and
its weighted adjoint is again the conjugate of a plane derivative amplified by the weight — the
weight cancelling in the adjoint is what makes the transfer of the weak equation to the plane
possible.

## Main definitions

* `Rigidity.RET.sheetTest` — the test function of the total space attached to a plane one.

## Main results

* `Rigidity.RET.deltaOp_conj_mul_exp` — the weighted adjoint of a conjugated test function
  amplified by the weight.
* `Rigidity.RET.deltaOpY_sheetTest` — the same computation on the total space.
-/

open MeasureTheory Metric Filter Topology ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {e : OpenPartialHomeomorph Y ℂ}
  {Φ ζ : ℂ → ℂ} {c z : ℂ} {R : ℝ}

/-! ### The weighted adjoint of a conjugated test function -/

/-- The holomorphic derivative of an exponential. -/
theorem dz_exp_comp (hΦ : DifferentiableAt ℝ Φ z) :
    dz (fun z' => Complex.exp (Φ z')) z = Complex.exp (Φ z) * dz Φ z := by
  have h := dz_comp_holo (F := Complex.exp) (g := Φ) hΦ (Complex.differentiable_exp _)
  rwa [(Complex.hasDerivAt_exp _).deriv] at h

/-- An exponential is as differentiable as its exponent. -/
theorem differentiableAt_exp_comp (hΦ : DifferentiableAt ℝ Φ z) :
    DifferentiableAt ℝ (fun z' => Complex.exp (Φ z')) z := by
  have hexp : DifferentiableAt ℝ Complex.exp (Φ z) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := 1)).differentiable (by norm_num) (Φ z)
  simpa [Function.comp_def] using hexp.comp z hΦ

/-- An exponential is as smooth as its exponent. -/
theorem contDiff_exp_comp {n : WithTop ℕ∞} (hΦ : ContDiff ℝ n Φ) :
    ContDiff ℝ n fun z' => Complex.exp (Φ z') := by
  have h := (Complex.contDiff_exp (𝕜 := ℝ) (n := n)).comp hΦ
  simpa [Function.comp_def] using h

/-- **The weight cancels in the adjoint**: the weighted adjoint of a conjugated function amplified
by the weight is the conjugate of the plane derivative, amplified by the weight. -/
theorem deltaOp_conj_mul_exp (hΦ : DifferentiableAt ℝ Φ z) (hζ : DifferentiableAt ℝ ζ z) :
    deltaOp Φ (fun z' => conj (ζ z') * Complex.exp (Φ z')) z
      = -(conj (dbar ζ z) * Complex.exp (Φ z)) := by
  rw [deltaOp, dz_mul (differentiableAt_conj hζ) (differentiableAt_exp_comp hΦ),
    dz_exp_comp hΦ, dz_conj hζ]
  ring

/-! ### The test function on the total space -/

/-- **The test function on the total space** attached to a test function of the coordinate: read
the conjugate of the plane function, amplified by the weight, through the coordinate. -/
def sheetTest (f : Y → ℂ) (e : OpenPartialHomeomorph Y ℂ) (Φ ζ : ℂ → ℂ) (y : Y) : ℂ :=
  e.source.indicator (fun y' => conj (ζ (f y')) * Complex.exp (Φ (f y'))) y

theorem sheetTest_of_mem_source {y : Y} (hy : y ∈ e.source) :
    sheetTest f e Φ ζ y = conj (ζ (f y)) * Complex.exp (Φ (f y)) := Set.indicator_of_mem hy _

theorem sheetTest_of_notMem_source {y : Y} (hy : y ∉ e.source) : sheetTest f e Φ ζ y = 0 :=
  Set.indicator_of_notMem hy _

/-- **Read in the coordinate, the test function of the total space is the plane one.** -/
theorem sheetTest_symm (hfe : f = ⇑e) (hz : z ∈ e.target) :
    sheetTest f e Φ ζ (e.symm z) = conj (ζ z) * Complex.exp (Φ z) := by
  rw [sheetTest_of_mem_source (e.map_target hz), apply_symm_of_isChartAt hfe hz]

/-- The test function of the total space lives over the disc. -/
theorem support_sheetTest_subset (hfe : f = ⇑e) (hζs : tsupport ζ ⊆ closedBall c R) :
    Function.support (sheetTest f e Φ ζ) ⊆ e.symm '' closedBall c R := by
  intro y hy
  rw [Function.mem_support] at hy
  by_cases hys : y ∈ e.source
  · rw [sheetTest_of_mem_source hys] at hy
    have hne : ζ (f y) ≠ 0 := by
      intro h
      exact hy (by rw [h, map_zero, zero_mul])
    exact ⟨f y, hζs (subset_tsupport _ hne), by rw [hfe]; exact e.left_inv hys⟩
  · exact absurd (sheetTest_of_notMem_source hys) hy

/-- The test function of the total space vanishes off the sheet over the disc. -/
theorem sheetTest_eq_zero (hfe : f = ⇑e) (hζs : tsupport ζ ⊆ closedBall c R) {y : Y}
    (hy : y ∉ e.symm '' closedBall c R) : sheetTest f e Φ ζ y = 0 :=
  Function.notMem_support.mp fun h => hy (support_sheetTest_subset hfe hζs h)

theorem hasCompactSupport_sheetTest [T2Space Y] (hfe : f = ⇑e)
    (hζs : tsupport ζ ⊆ closedBall c R) (hball : closedBall c R ⊆ e.target) :
    HasCompactSupport (sheetTest f e Φ ζ) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_symm_image hball)
    (support_sheetTest_subset hfe hζs)

theorem continuous_sheetTest [T2Space Y] (hf : Continuous f) (hfe : f = ⇑e)
    (hΦ : Continuous Φ) (hζ : Continuous ζ) (hζs : tsupport ζ ⊆ closedBall c R)
    (hball : closedBall c R ⊆ e.target) : Continuous (sheetTest f e Φ ζ) := by
  have hK : IsCompact (e.symm '' closedBall c R) := isCompact_symm_image hball
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ e.source
  · have hmodel : Continuous fun y' : Y => conj (ζ (f y')) * Complex.exp (Φ (f y')) :=
      ((Complex.continuous_conj.comp hζ).comp hf).mul ((Complex.continuous_exp.comp hΦ).comp hf)
    refine hmodel.continuousAt.congr ?_
    filter_upwards [e.open_source.mem_nhds hy] with y' hy'
    exact (sheetTest_of_mem_source hy').symm
  · have hyK : y ∉ e.symm '' closedBall c R := fun h => hy (symm_image_subset_source hball h)
    have hconst : ContinuousAt (fun _ : Y => (0 : ℂ)) y := continuousAt_const
    refine hconst.congr ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hyK] with y' hy'
    exact (sheetTest_eq_zero hfe hζs hy').symm

/-- **The test function of the total space is twice continuously differentiable.** -/
theorem isC2At_sheetTest [T2Space Y] (hlh : IsLocalHomeomorph f) (hfe : f = ⇑e)
    (hΦ : ContDiff ℝ 2 Φ) (hζ : ContDiff ℝ 2 ζ) (hζs : tsupport ζ ⊆ closedBall c R)
    (hball : closedBall c R ⊆ e.target) (y : Y) : IsC2At f (sheetTest f e Φ ζ) y := by
  by_cases hy : y ∈ e.source
  · have he : IsChartAt f e y := ⟨hy, hfe⟩
    refine ⟨e, he, ?_⟩
    have hmodel : ContDiff ℝ 2 fun z' : ℂ => conj (ζ z') * Complex.exp (Φ z') := by
      have h1 : ContDiff ℝ 2 fun z' : ℂ => conj (ζ z') := by
        have := (contDiff_conj (n := (2 : WithTop ℕ∞))).comp hζ
        simpa [Function.comp_def] using this
      exact h1.mul (contDiff_exp_comp hΦ)
    refine hmodel.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [e.open_target.mem_nhds he.mem_target] with z hz
    exact sheetTest_symm hfe hz
  · have hK : IsCompact (e.symm '' closedBall c R) := isCompact_symm_image hball
    have hyK : y ∉ e.symm '' closedBall c R := fun h => hy (symm_image_subset_source hball h)
    obtain ⟨e', hy', hfe'⟩ := hlh y
    have he' : IsChartAt f e' y := ⟨hy', hfe'⟩
    refine ⟨e', he', ?_⟩
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    have hcont : ContinuousAt e'.symm (f y) := e'.continuousAt_symm he'.mem_target
    have hpre : e'.symm ⁻¹' (e.symm '' closedBall c R)ᶜ ∈ 𝓝 (f y) := by
      refine hcont.preimage_mem_nhds ?_
      rw [he'.symm_apply]
      exact hK.isClosed.isOpen_compl.mem_nhds hyK
    filter_upwards [hpre] with z hz
    exact sheetTest_eq_zero hfe hζs hz

/-- **The weighted adjoint of the test function of the total space**, read in the coordinate. -/
theorem deltaOpY_sheetTest {hlh : IsLocalHomeomorph f} (hfe : f = ⇑e) (hΦ : ContDiff ℝ 2 Φ)
    (hζ : ContDiff ℝ 2 ζ) (hz : z ∈ e.target) :
    deltaOpY hlh Φ (sheetTest f e Φ ζ) (e.symm z)
      = -(conj (dbar ζ z) * Complex.exp (Φ z)) := by
  rw [deltaOpY_symm_apply hfe Φ (sheetTest f e Φ ζ) hz]
  have hev : (fun z' => sheetTest f e Φ ζ (e.symm z'))
      =ᶠ[𝓝 z] fun z' => conj (ζ z') * Complex.exp (Φ z') := by
    filter_upwards [e.open_target.mem_nhds hz] with z' hz'
    exact sheetTest_symm hfe hz'
  have hval : sheetTest f e Φ ζ (e.symm z) = conj (ζ z) * Complex.exp (Φ z) :=
    sheetTest_symm hfe hz
  rw [deltaOp, dz_congr hev, hval, ← deltaOp]
  exact deltaOp_conj_mul_exp (hΦ.differentiable (by norm_num) z)
    (hζ.differentiable (by norm_num) z)

/-- The weighted adjoint of the test function of the total space also lives over the disc. -/
theorem deltaOpY_sheetTest_eq_zero [T2Space Y] {hlh : IsLocalHomeomorph f} (hfe : f = ⇑e)
    (hζs : tsupport ζ ⊆ closedBall c R) (hball : closedBall c R ⊆ e.target) {y : Y}
    (hy : y ∉ e.symm '' closedBall c R) : deltaOpY hlh Φ (sheetTest f e Φ ζ) y = 0 := by
  have hK : IsCompact (e.symm '' closedBall c R) := isCompact_symm_image hball
  have hzero : sheetTest f e Φ ζ y = 0 := sheetTest_eq_zero hfe hζs hy
  have he' := isChartAt_chartOf hlh y
  have hev : (fun z => sheetTest f e Φ ζ ((chartOf hlh y).symm z))
      =ᶠ[𝓝 (f y)] fun _ => (0 : ℂ) := by
    have hcont : ContinuousAt (chartOf hlh y).symm (f y) :=
      (chartOf hlh y).continuousAt_symm he'.mem_target
    have hpre : (chartOf hlh y).symm ⁻¹' (e.symm '' closedBall c R)ᶜ ∈ 𝓝 (f y) := by
      refine hcont.preimage_mem_nhds ?_
      rw [he'.symm_apply]
      exact hK.isClosed.isOpen_compl.mem_nhds hy
    filter_upwards [hpre] with z hz
    exact sheetTest_eq_zero hfe hζs hz
  rw [deltaOpY, dzY, dz_congr hev, dz_const, hzero, mul_zero, neg_zero, add_zero]

end Rigidity.RET

end
