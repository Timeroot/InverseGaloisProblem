/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.WeightMeasure
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverEstimate

/-!
# The weighted `L²` space of a covering

A real exponent on the plane has a positive continuous weight, and weighting the fibre-sum measure
of the total space by it produces a measure whose square-integrable functions are exactly the ones
the a priori estimate speaks about.  A continuous function of compact support on the total space is
square integrable for that measure, and both its inner products and its square norm are the
weighted ones: the Hilbert space in which the Cauchy–Riemann equation is to be solved is therefore
the ordinary `L²` space of an ordinary measure.

## Main definitions

* `Rigidity.RET.weightOf` — the weight attached to an exponent.
* `Rigidity.RET.coverL2Measure` — the measure of the weighted `L²` space of a covering.
* `Rigidity.RET.toL2` — a continuous function of compact support as an element of that space.

## Main results

* `Rigidity.RET.integral_coverL2Measure` — integration against the measure is integration of
  weighted fibre sums over the plane.
* `Rigidity.RET.inner_toL2` — the inner product of two such elements is the weighted inner product.
* `Rigidity.RET.norm_toL2_sq` — the square norm of such an element is the weighted square norm.
-/

open MeasureTheory Topology ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f u v : Y → ℂ} {y : Y} {Φ : ℂ → ℂ}

/-! ### Twice differentiable functions on the total space -/

/-- A constant is twice continuously differentiable. -/
theorem isC2At_const (hlh : IsLocalHomeomorph f) (c : ℂ) (y : Y) : IsC2At f (fun _ => c) y :=
  ⟨chartOf hlh y, isChartAt_chartOf hlh y, contDiffAt_const⟩

/-- A sum of twice continuously differentiable functions is twice continuously differentiable. -/
theorem IsC2At.add (hu : IsC2At f u y) (hv : IsC2At f v y) :
    IsC2At f (fun y' => u y' + v y') y := by
  obtain ⟨e, he, hc⟩ := hu
  exact ⟨e, he, hc.add (hv.of_isChartAt he)⟩

/-- A constant multiple of a twice continuously differentiable function is twice continuously
differentiable. -/
theorem IsC2At.const_mul (c : ℂ) (hu : IsC2At f u y) : IsC2At f (fun y' => c * u y') y := by
  obtain ⟨e, he, hc⟩ := hu
  exact ⟨e, he, contDiffAt_const.mul hc⟩

/-! ### Linearity of the operators -/

/-- The holomorphic derivative of a constant vanishes. -/
theorem dz_const (c z : ℂ) : dz (fun _ => c) z = 0 := by
  have h : fderiv ℝ (fun _ : ℂ => c) z = 0 := (hasFDerivAt_const c z).fderiv
  simp [dz, h]

/-- The holomorphic derivative is homogeneous. -/
theorem dz_const_mul {w : ℂ → ℂ} {z : ℂ} (c : ℂ) (hw : DifferentiableAt ℝ w z) :
    dz (fun t => c * w t) z = c * dz w z := by
  rw [dz_mul (differentiableAt_const c) hw, dz_const]
  ring

variable {hlh : IsLocalHomeomorph f}

/-- A constant is differentiable in every local coordinate. -/
theorem isDiffAt_const (hlh : IsLocalHomeomorph f) (c : ℂ) (y : Y) : IsDiffAt f (fun _ => c) y :=
  isDiffAt_comp (β := fun _ => c) hlh (differentiableAt_const c)

/-- The holomorphic derivative of a constant vanishes. -/
theorem dzY_const (hlh : IsLocalHomeomorph f) (c : ℂ) (y : Y) : dzY hlh (fun _ => c) y = 0 := by
  have h := dzY_comp hlh (fun _ => c) y
  rw [dz_const] at h
  exact h

/-- The holomorphic derivative on the total space is homogeneous. -/
theorem dzY_const_mul (c : ℂ) (hu : IsDiffAt f u y) :
    dzY hlh (fun y' => c * u y') y = c * dzY hlh u y := by
  rw [dzY_mul (isDiffAt_const hlh c y) hu, dzY_const]
  ring

/-- The weighted adjoint is additive. -/
theorem deltaOpY_add (hu : IsDiffAt f u y) (hv : IsDiffAt f v y) :
    deltaOpY hlh Φ (fun y' => u y' + v y') y = deltaOpY hlh Φ u y + deltaOpY hlh Φ v y := by
  simp only [deltaOpY, dzY_add hu hv]
  ring

/-- The weighted adjoint is homogeneous. -/
theorem deltaOpY_const_mul (c : ℂ) (hu : IsDiffAt f u y) :
    deltaOpY hlh Φ (fun y' => c * u y') y = c * deltaOpY hlh Φ u y := by
  simp only [deltaOpY, dzY_const_mul c hu]
  ring

/-! ### The weight of an exponent -/

/-- **The weight of an exponent.** -/
def weightOf (Φ : ℂ → ℂ) (z : ℂ) : ℝ := Real.exp (-(Φ z).re)

/-- The weight is positive. -/
theorem weightOf_pos (Φ : ℂ → ℂ) (z : ℂ) : 0 < weightOf Φ z := Real.exp_pos _

/-- The weight of a continuous exponent is continuous. -/
theorem continuous_weightOf (hΦ : Continuous Φ) : Continuous (weightOf Φ) :=
  Real.continuous_exp.comp (Complex.continuous_re.comp hΦ).neg

/-- For a real exponent the weight is the exponential of its negative. -/
theorem ofReal_weightOf (hreal : ∀ t, conj (Φ t) = Φ t) (z : ℂ) :
    ((weightOf Φ z : ℝ) : ℂ) = Complex.exp (-(Φ z)) := (exp_neg_eq_ofReal hreal z).symm

/-! ### The measure -/

section L2

variable (hfin : ∀ z, (f ⁻¹' {z}).Finite)
  (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
  (hΦc : Continuous Φ)
  [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

variable (f Φ) in
/-- **The measure of the weighted `L²` space of a covering.** -/
def coverL2Measure : Measure Y :=
  weightMeasure f hfin hcov hf (weightOf Φ) (continuous_weightOf hΦc)
    fun z => (weightOf_pos Φ z).le

instance regular_coverL2Measure : (coverL2Measure f Φ hfin hcov hf hΦc).Regular :=
  regular_weightMeasure hfin hcov hf (continuous_weightOf hΦc) fun z => (weightOf_pos Φ z).le

/-- **Integration against the measure is integration of weighted fibre sums over the plane.** -/
theorem integral_coverL2Measure (hreal : ∀ t, conj (Φ t) = Φ t) {F : Y → ℂ}
    (hFc : Continuous F) (hFs : HasCompactSupport F) :
    ∫ y, F y ∂(coverL2Measure f Φ hfin hcov hf hΦc)
      = ∫ z : ℂ, fibreSum f (fun y => F y * Complex.exp (-(Φ (f y)))) z := by
  have h := integral_weightMeasure_complex (w := weightOf Φ) hfin hcov hf
    (continuous_weightOf hΦc) (fun z => (weightOf_pos Φ z).le) hFc hFs
  have he : (fun y => F y * ((weightOf Φ (f y) : ℝ) : ℂ))
      = fun y => F y * Complex.exp (-(Φ (f y))) := by
    funext y
    rw [ofReal_weightOf hreal]
  rw [he] at h
  exact h

/-! ### The Hilbert space -/

/-- **A continuous function of compact support, as an element of the weighted `L²` space.** -/
def toL2 {F : Y → ℂ} (hFc : Continuous F) (hFs : HasCompactSupport F) :
    Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦc) :=
  (hFc.memLp_of_hasCompactSupport hFs).toLp F

/-- An element of the weighted `L²` space built from a function represents that function. -/
theorem coeFn_toL2 {F : Y → ℂ} (hFc : Continuous F) (hFs : HasCompactSupport F) :
    ⇑(toL2 hfin hcov hf hΦc hFc hFs) =ᵐ[coverL2Measure f Φ hfin hcov hf hΦc] F :=
  MemLp.coeFn_toLp _

/-- The element attached to a function does not depend on the proofs that go into it. -/
theorem toL2_congr {F G : Y → ℂ} (hFc : Continuous F) (hFs : HasCompactSupport F)
    (hGc : Continuous G) (hGs : HasCompactSupport G) (h : F = G) :
    toL2 hfin hcov hf hΦc hFc hFs = toL2 hfin hcov hf hΦc hGc hGs := by
  subst h
  rfl

/-- The map to the weighted `L²` space is additive. -/
theorem toL2_add {F G : Y → ℂ} (hFc : Continuous F) (hFs : HasCompactSupport F)
    (hGc : Continuous G) (hGs : HasCompactSupport G)
    (hSc : Continuous fun y => F y + G y) (hSs : HasCompactSupport fun y => F y + G y) :
    toL2 hfin hcov hf hΦc hSc hSs
      = toL2 hfin hcov hf hΦc hFc hFs + toL2 hfin hcov hf hΦc hGc hGs :=
  MemLp.toLp_add _ _

/-- The map to the weighted `L²` space is homogeneous. -/
theorem toL2_const_smul (c : ℂ) {F : Y → ℂ} (hFc : Continuous F) (hFs : HasCompactSupport F)
    (hGc : Continuous fun y => c * F y) (hGs : HasCompactSupport fun y => c * F y) :
    toL2 hfin hcov hf hΦc hGc hGs = c • toL2 hfin hcov hf hΦc hFc hFs :=
  MemLp.toLp_const_smul c _

/-- **The inner product of the weighted `L²` space is the weighted inner product.** -/
theorem inner_toL2 (hreal : ∀ t, conj (Φ t) = Φ t) {F G : Y → ℂ}
    (hFc : Continuous F) (hFs : HasCompactSupport F)
    (hGc : Continuous G) (hGs : HasCompactSupport G) :
    inner ℂ (toL2 hfin hcov hf hΦc hFc hFs) (toL2 hfin hcov hf hΦc hGc hGs) = wipY f Φ G F := by
  rw [L2.inner_def]
  refine (integral_congr_ae (g := fun y => G y * conj (F y)) ?_).trans ?_
  · filter_upwards [coeFn_toL2 hfin hcov hf hΦc hFc hFs,
      coeFn_toL2 hfin hcov hf hΦc hGc hGs] with y hy1 hy2
    simp only [hy1, hy2, RCLike.inner_apply]
  · exact integral_coverL2Measure hfin hcov hf hΦc hreal
      (hGc.mul (Complex.continuous_conj.comp hFc)) hGs.mul_right

/-- **The square norm of the weighted `L²` space is the weighted square norm.** -/
theorem norm_toL2_sq (hreal : ∀ t, conj (Φ t) = Φ t) {F : Y → ℂ}
    (hFc : Continuous F) (hFs : HasCompactSupport F) :
    ‖toL2 hfin hcov hf hΦc hFc hFs‖ ^ 2 = wnorm2Y f Φ F := by
  have h := inner_toL2 hfin hcov hf hΦc hreal hFc hFs hFc hFs
  rw [inner_self_eq_norm_sq_to_K, wipY_self hfin hreal] at h
  have h2 : ((‖toL2 hfin hcov hf hΦc hFc hFs‖ ^ 2 : ℝ) : ℂ) = ((wnorm2Y f Φ F : ℝ) : ℂ) := by
    push_cast
    exact h
  exact Complex.ofReal_inj.mp h2

end L2

end Rigidity.RET

end
