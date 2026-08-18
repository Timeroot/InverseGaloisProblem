/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverTest
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverWeak
import InverseGalois.Rigidity.RET.Analytic.Dbar.Weyl

/-!
# The weak equation of a covering, read in a coordinate

Testing the weak Cauchy–Riemann equation of a covering against the test functions carried by one
sheet turns it into the weak equation of a disc in the plane: the weight cancels against the
amplification of the test function, the fibre sums collapse to a single term, and both sides
become plane integrals of the solution and of the source read in the coordinate.

## Main results

* `Rigidity.RET.integral_dbar_mul_symm` — **the weak equation read in a coordinate.**
-/

open MeasureTheory Metric Filter Topology ComplexConjugate

open scoped ContDiff

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f g : Y → ℂ} {e : OpenPartialHomeomorph Y ℂ}
  {Φ ζ : ℂ → ℂ} {c : ℂ} {R R' : ℝ}

/-! ### Reading a function in a coordinate -/

/-- A measurable function of the total space is measurable when read in a coordinate. -/
theorem aestronglyMeasurable_comp_symm [MeasurableSpace Y] [BorelSpace Y] {E : Type*}
    [NormedAddCommGroup E] (hball : closedBall c R ⊆ e.target) {G : Y → E}
    (hG : StronglyMeasurable G) :
    AEStronglyMeasurable (fun z => G (e.symm z)) (volume.restrict (ball c R)) := by
  have hsub : ball c R ⊆ e.target := ball_subset_closedBall.trans hball
  have hm : AEMeasurable e.symm (volume.restrict (ball c R)) :=
    (e.continuousOn_symm.mono hsub).aemeasurable measurableSet_ball
  have hGm : AEStronglyMeasurable G (Measure.map e.symm (volume.restrict (ball c R))) :=
    hG.aestronglyMeasurable
  simpa [Function.comp_def] using hGm.comp_aemeasurable hm

section Measure

variable [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (hfin : ∀ z, (f ⁻¹' {z}).Finite)
  (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
  (hΦc : Continuous Φ)

/-- **The integral over a sheet above a disc** for the measure of the weighted `L²` space. -/
theorem integral_coverL2Measure_sheet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hfe : f = ⇑e) (hball : closedBall c R ⊆ e.target) {G : Y → E}
    (hG : AEStronglyMeasurable (fun z => G (e.symm z)) (volume.restrict (ball c R))) :
    ∫ y in sheet f e c R, G y ∂(coverL2Measure f Φ hfin hcov hf hΦc)
      = ∫ z in ball c R, weightOf Φ z • G (e.symm z) :=
  integral_weightMeasure_sheet hfin hcov hf (continuous_weightOf hΦc)
    (fun z => (weightOf_pos Φ z).le) hfe hball hG

/-- **A function integrable over a sheet above a disc is integrable over the disc** when read in
the coordinate. -/
theorem integrableOn_comp_symm_coverL2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hfe : f = ⇑e) (hball : closedBall c R ⊆ e.target) {G : Y → E}
    (hG : AEStronglyMeasurable (fun z => G (e.symm z)) (volume.restrict (ball c R)))
    (hint : IntegrableOn G (sheet f e c R) (coverL2Measure f Φ hfin hcov hf hΦc)) :
    IntegrableOn (fun z => G (e.symm z)) (ball c R) volume :=
  integrableOn_comp_symm hfin hcov hf (continuous_weightOf hΦc)
    (fun z => (weightOf_pos Φ z).le) hfe hball (fun z => weightOf_pos Φ z) hG hint

end Measure

/-! ### The weak equation in a coordinate -/

/-- **The weak Cauchy–Riemann equation of a covering, read in a coordinate.** -/
theorem integral_dbar_mul_symm [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (hfin : ∀ z, (f ⁻¹' {z}).Finite)
    (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
    (hlh : IsLocalHomeomorph f) (hΦ : ContDiff ℝ 2 Φ) (hreal : ∀ t, conj (Φ t) = Φ t)
    (hfe : f = ⇑e) (hRR' : R < R') (hball : closedBall c R' ⊆ e.target)
    {U : Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦ.continuous)}
    (hU : ∀ w : Y → ℂ, (∀ y, IsC2At f w y) → HasCompactSupport w →
      (∫ y, deltaOpY hlh Φ w y * conj (U y)
          ∂(coverL2Measure f Φ hfin hcov hf hΦ.continuous)) = wipY f Φ w g)
    (hζ : ContDiff ℝ 2 ζ) (hζs : tsupport ζ ⊆ closedBall c R) :
    (∫ z in ball c R', dbar ζ z * U (e.symm z)) = -∫ z in ball c R', ζ z * g (e.symm z) := by
  have hballR : closedBall c R ⊆ e.target :=
    (closedBall_subset_closedBall hRR'.le).trans hball
  set wT := sheetTest f e Φ ζ with hwT
  have hw2 : ∀ y, IsC2At f wT y := isC2At_sheetTest hlh hfe hΦ hζ hζs hballR
  have hwsupp : HasCompactSupport wT := hasCompactSupport_sheetTest hfe hζs hballR
  have hkey := hU wT hw2 hwsupp
  have hsub : e.symm '' closedBall c R ⊆ sheet f e c R' := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_sheet_symm hfe hball (closedBall_subset_ball hRR' hz)
  -- the left-hand side
  have hAzero : ∀ y, y ∉ sheet f e c R' → deltaOpY hlh Φ wT y * conj (U y) = 0 := by
    intro y hy
    have hyK : y ∉ e.symm '' closedBall c R := fun hmem => hy (hsub hmem)
    rw [deltaOpY_sheetTest_eq_zero hfe hζs hballR hyK, zero_mul]
  have hUmeas : AEStronglyMeasurable (fun z => (U : Y → ℂ) (e.symm z))
      (volume.restrict (ball c R')) :=
    aestronglyMeasurable_comp_symm hball (Lp.stronglyMeasurable U)
  have hAmeas : AEStronglyMeasurable
      (fun z => deltaOpY hlh Φ wT (e.symm z) * conj ((U : Y → ℂ) (e.symm z)))
      (volume.restrict (ball c R')) := by
    have h1 : AEStronglyMeasurable (fun z : ℂ => -(conj (dbar ζ z) * Complex.exp (Φ z)))
        (volume.restrict (ball c R')) := by
      have hc : Continuous fun z : ℂ => -(conj (dbar ζ z) * Complex.exp (Φ z)) :=
        ((Complex.continuous_conj.comp (continuous_dbar (hζ.of_le one_le_two))).mul
          (Complex.continuous_exp.comp hΦ.continuous)).neg
      exact hc.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun z => conj ((U : Y → ℂ) (e.symm z)))
        (volume.restrict (ball c R')) :=
      Complex.continuous_conj.comp_aestronglyMeasurable hUmeas
    refine (h1.mul h2).congr ?_
    refine (ae_restrict_iff' measurableSet_ball).2 (.of_forall fun z hz => ?_)
    have hzt : z ∈ e.target := hball (ball_subset_closedBall hz)
    simp only [Pi.mul_apply, hwT]
    rw [deltaOpY_sheetTest hfe hΦ hζ hzt]
  have hLHS : (∫ y, deltaOpY hlh Φ wT y * conj ((U : Y → ℂ) y)
        ∂(coverL2Measure f Φ hfin hcov hf hΦ.continuous))
      = ∫ z in ball c R', -(conj (dbar ζ z) * conj ((U : Y → ℂ) (e.symm z))) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hAzero,
      integral_coverL2Measure_sheet hfin hcov hf hΦ.continuous hfe hball hAmeas]
    refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
    have hzt : z ∈ e.target := hball (ball_subset_closedBall hz)
    rw [deltaOpY_sheetTest hfe hΦ hζ hzt, Complex.real_smul, ofReal_weightOf hreal]
    have hexp : Complex.exp (-(Φ z)) * Complex.exp (Φ z) = 1 := by
      rw [← Complex.exp_add]
      simp
    calc Complex.exp (-(Φ z)) * (-(conj (dbar ζ z) * Complex.exp (Φ z)) *
            conj ((U : Y → ℂ) (e.symm z)))
        = -((Complex.exp (-(Φ z)) * Complex.exp (Φ z)) *
            (conj (dbar ζ z) * conj ((U : Y → ℂ) (e.symm z)))) := by ring
      _ = -(conj (dbar ζ z) * conj ((U : Y → ℂ) (e.symm z))) := by rw [hexp, one_mul]
  -- the right-hand side
  have hBsource : ∀ y, y ∉ e.source →
      wT y * conj (g y) * Complex.exp (-(Φ (f y))) = 0 := by
    intro y hy
    rw [hwT, sheetTest_of_notMem_source hy, zero_mul, zero_mul]
  have hBzero : ∀ z, z ∉ ball c R' →
      fibreSum f (fun y => wT y * conj (g y) * Complex.exp (-(Φ (f y)))) z = 0 := by
    intro z hz
    by_cases hzt : z ∈ e.target
    · rw [fibreSum_of_mem_target hfe hBsource hzt]
      have hnot : e.symm z ∉ e.symm '' closedBall c R := by
        rintro ⟨z', hz', hEq⟩
        have h2 : z' = z := by
          rw [← apply_symm_of_isChartAt hfe (hballR hz'), hEq,
            apply_symm_of_isChartAt hfe hzt]
        subst h2
        exact hz (closedBall_subset_ball hRR' hz')
      rw [hwT, sheetTest_eq_zero hfe hζs hnot, zero_mul, zero_mul]
    · exact fibreSum_of_notMem_target hfe hBsource hzt
  have hRHS : wipY f Φ wT g = ∫ z in ball c R', conj (ζ z * g (e.symm z)) := by
    rw [wipY, ← setIntegral_eq_integral_of_forall_compl_eq_zero hBzero]
    refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
    have hzt : z ∈ e.target := hball (ball_subset_closedBall hz)
    rw [fibreSum_of_mem_target hfe hBsource hzt, hwT, sheetTest_symm hfe hzt,
      apply_symm_of_isChartAt hfe hzt, map_mul]
    have hexp : Complex.exp (Φ z) * Complex.exp (-(Φ z)) = 1 := by
      rw [← Complex.exp_add]
      simp
    calc conj (ζ z) * Complex.exp (Φ z) * conj (g (e.symm z)) * Complex.exp (-(Φ z))
        = (Complex.exp (Φ z) * Complex.exp (-(Φ z))) *
            (conj (ζ z) * conj (g (e.symm z))) := by ring
      _ = conj (ζ z) * conj (g (e.symm z)) := by rw [hexp, one_mul]
  -- combine
  rw [hLHS, hRHS] at hkey
  have hconj1 : (∫ z in ball c R', -(conj (dbar ζ z) * conj ((U : Y → ℂ) (e.symm z))))
      = -conj (∫ z in ball c R', dbar ζ z * (U : Y → ℂ) (e.symm z)) := by
    have hfun : (fun z => -(conj (dbar ζ z) * conj ((U : Y → ℂ) (e.symm z))))
        = fun z => -conj (dbar ζ z * (U : Y → ℂ) (e.symm z)) := by
      funext z
      rw [map_mul]
    rw [hfun, integral_neg, integral_conj]
  have hconj2 : (∫ z in ball c R', conj (ζ z * g (e.symm z)))
      = conj (∫ z in ball c R', ζ z * g (e.symm z)) := integral_conj
  rw [hconj1, hconj2] at hkey
  have h4 := congrArg (fun t : ℂ => conj t) hkey
  simp only [map_neg, Complex.conj_conj] at h4
  linear_combination -h4

/-! ### A solution in a coordinate -/

/-- **A solution of the Cauchy–Riemann equation in a coordinate**: on a smaller disc the weak
solution of the covering agrees almost everywhere with a differentiable function whose
Cauchy–Riemann derivative is the source read in the coordinate. -/
theorem exists_local_dbar_solution [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (hfin : ∀ z, (f ⁻¹' {z}).Finite)
    (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
    (hlh : IsLocalHomeomorph f) (hΦ : ContDiff ℝ 2 Φ) (hreal : ∀ t, conj (Φ t) = Φ t)
    (hg1 : ∀ y, IsC1At f g y) (hfe : f = ⇑e)
    {U : Lp ℂ 2 (coverL2Measure f Φ hfin hcov hf hΦ.continuous)}
    (hU : ∀ w : Y → ℂ, (∀ y, IsC2At f w y) → HasCompactSupport w →
      (∫ y, deltaOpY hlh Φ w y * conj (U y)
          ∂(coverL2Measure f Φ hfin hcov hf hΦ.continuous)) = wipY f Φ w g)
    (hR' : 0 < R') (hball : closedBall c R' ⊆ e.target) :
    ∃ v : ℂ → ℂ, (∀ z ∈ ball c (R' / 8), DifferentiableAt ℝ v z) ∧
      (∀ z ∈ ball c (R' / 8), dbar v z = g (e.symm z)) ∧
      ∀ᵐ z : ℂ, z ∈ ball c (R' / 8) → (U : Y → ℂ) (e.symm z) = v z := by
  classical
  -- the solution, read in the coordinate and truncated to the disc
  have hUmeas : AEStronglyMeasurable (fun z => (U : Y → ℂ) (e.symm z))
      (volume.restrict (ball c R')) :=
    aestronglyMeasurable_comp_symm hball (Lp.stronglyMeasurable U)
  have hKcpt : IsCompact (e.symm '' closedBall c R') := isCompact_symm_image hball
  have hsheetlt : (coverL2Measure f Φ hfin hcov hf hΦ.continuous) (sheet f e c R') < ⊤ :=
    lt_of_le_of_lt (measure_mono (sheet_subset_symm_image hfe)) hKcpt.measure_lt_top
  haveI : IsFiniteMeasure
      ((coverL2Measure f Φ hfin hcov hf hΦ.continuous).restrict (sheet f e c R')) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hUsheet : IntegrableOn (⇑U) (sheet f e c R')
      (coverL2Measure f Φ hfin hcov hf hΦ.continuous) :=
    ((Lp.memLp U).restrict _).integrable (by norm_num)
  have hu0 : IntegrableOn (fun z => (U : Y → ℂ) (e.symm z)) (ball c R') volume :=
    integrableOn_comp_symm_coverL2 hfin hcov hf hΦ.continuous hfe hball hUmeas hUsheet
  set u' := (ball c R').indicator (fun z => (U : Y → ℂ) (e.symm z)) with hu'def
  have hu' : Integrable u' := hu0.integrable_indicator measurableSet_ball
  -- the source, read in the coordinate and cut off
  let χ : ContDiffBump c := ⟨R' / 2, 3 * R' / 4, by linarith, by linarith⟩
  have hrIn : χ.rIn = R' / 2 := rfl
  have hrOut : χ.rOut = 3 * R' / 4 := rfl
  set g' : ℂ → ℂ := fun z => (χ z) • g (e.symm z) with hg'def
  have hgc : ∀ z ∈ e.target, ContDiffAt ℝ 1 (fun z' => g (e.symm z')) z := by
    intro z hz
    have h := (hg1 (e.symm z)).of_isChartAt (isChartAt_symm hfe hz)
    rwa [apply_symm_of_isChartAt hfe hz] at h
  have hg' : ContDiff ℝ 1 g' := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ ball c R'
    · exact χ.contDiff.contDiffAt.smul (hgc z (hball (ball_subset_closedBall hz)))
    · simp only [mem_ball, not_lt] at hz
      have hd : 3 * R' / 4 < dist z c := by linarith
      have hopen : IsOpen {w : ℂ | 3 * R' / 4 < dist w c} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hev : g' =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [hopen.mem_nhds hd] with w hw
        rw [hg'def]
        simp only
        rw [χ.zero_of_le_dist (by rw [hrOut]; exact le_of_lt hw), zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  -- the weak equation of the disc
  have hweak : ∀ ζ : ℂ → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ closedBall c (R' / 2) →
      (∫ w : ℂ, dbar ζ w * u' w) = -∫ w : ℂ, ζ w * g' w := by
    intro ζ hζ _ hζs
    have hζzero : ∀ w, w ∉ closedBall c (R' / 2) → ζ w = 0 := fun w hw =>
      Function.notMem_support.mp fun hcon => hw (hζs (subset_tsupport _ hcon))
    have hkey := integral_dbar_mul_symm hfin hcov hf hlh hΦ hreal hfe
      (show R' / 2 < R' by linarith) hball hU (hζ.of_le (WithTop.coe_le_coe.2 le_top)) hζs
    have hL : (∫ w : ℂ, dbar ζ w * u' w)
        = ∫ z in ball c R', dbar ζ z * (U : Y → ℂ) (e.symm z) := by
      rw [← integral_indicator measurableSet_ball]
      congr 1
      funext w
      by_cases hw : w ∈ ball c R'
      · rw [Set.indicator_of_mem hw, hu'def, Set.indicator_of_mem hw]
      · rw [Set.indicator_of_notMem hw, hu'def, Set.indicator_of_notMem hw, mul_zero]
    have hRint : (∫ w : ℂ, ζ w * g' w) = ∫ z in ball c R', ζ z * g (e.symm z) := by
      rw [← integral_indicator measurableSet_ball]
      congr 1
      funext w
      by_cases hw : w ∈ ball c R'
      · rw [Set.indicator_of_mem hw]
        by_cases hwζ : w ∈ closedBall c (R' / 2)
        · rw [hg'def]
          simp only
          rw [χ.one_of_mem_closedBall (by rwa [hrIn]), one_smul]
        · rw [hζzero w hwζ, zero_mul, zero_mul]
      · have hwζ : w ∉ closedBall c (R' / 2) := fun hcon =>
          hw (closedBall_subset_ball (by linarith) hcon)
        rw [Set.indicator_of_notMem hw, hζzero w hwζ, zero_mul]
    rw [hL, hRint]
    exact hkey
  -- the regularity theorem in the plane
  obtain ⟨v, hv1, hv2, hv3⟩ :=
    exists_dbar_of_weak (show (0 : ℝ) < R' / 2 by linarith) hu' hg' hweak
  have hrad : R' / 2 / 4 = R' / 8 := by ring
  rw [hrad] at hv1 hv2 hv3
  refine ⟨v, hv1, fun z hz => ?_, ?_⟩
  · have hmem : z ∈ closedBall c (R' / 2) := by
      simp only [mem_ball] at hz
      simp only [mem_closedBall]
      linarith
    rw [hv2 z hz, hg'def]
    simp only
    rw [χ.one_of_mem_closedBall (by rwa [hrIn]), one_smul]
  · filter_upwards [hv3] with z hz hzmem
    have hball8 : z ∈ ball c R' := by
      simp only [mem_ball] at hzmem ⊢
      linarith
    have := hz hzmem
    rwa [hu'def, Set.indicator_of_mem hball8] at this

end Rigidity.RET

end
