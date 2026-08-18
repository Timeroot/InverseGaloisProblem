/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverL2

/-!
# The measure of a covering read in a local coordinate

Above a disc contained in the target of a local coordinate the projection is a homeomorphism onto
its image, so the fibre sum of a function living on that one sheet is just the function read in the
coordinate.  Exhausting the sheet by cutoffs turns this statement for continuous functions into an
equality of measures: the projection carries the measure of the covering, restricted to the sheet,
to the weighted plane measure of the disc.  The equality of measures then applies to functions that
are merely measurable, which is what the elements of the `L²` space are.

## Main definitions

* `Rigidity.RET.discRamp` — a continuous cutoff of a disc, rising to one on all of it.
* `Rigidity.RET.sheet` — the part of a sheet lying above a disc.

## Main results

* `Rigidity.RET.fibreSum_of_mem_target` — the fibre sum of a function living on one sheet.
* `Rigidity.RET.map_weightMeasure_restrict_sheet` — the projection carries the measure of the
  covering, restricted to a sheet above a disc, to the weighted plane measure of the disc.
-/

open MeasureTheory Metric Filter Topology

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {e : OpenPartialHomeomorph Y ℂ}
  {c : ℂ} {R : ℝ} {n : ℕ}

/-! ### Fibre sums of a function living on one sheet -/

section Sheet

variable {M : Type*} [AddCommMonoid M] {F : Y → M}

/-- **The fibre sum of a function living on one sheet** is the function read in the coordinate. -/
theorem fibreSum_of_mem_target (hfe : f = ⇑e) (hF : ∀ y, y ∉ e.source → F y = 0) {z : ℂ}
    (hz : z ∈ e.target) : fibreSum f F z = F (e.symm z) := by
  have hmem : e.symm z ∈ f ⁻¹' {z} := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hfe]
    exact e.right_inv hz
  rw [fibreSum, finsum_mem_def]
  refine (finsum_eq_single _ (e.symm z) ?_).trans (Set.indicator_of_mem hmem F)
  intro x hx
  by_cases hxf : x ∈ f ⁻¹' {z}
  · refine (Set.indicator_of_mem hxf F).trans ?_
    by_cases hxs : x ∈ e.source
    · exfalso
      refine hx ?_
      have : e x = z := by
        have := Set.mem_singleton_iff.mp hxf
        rwa [hfe] at this
      rw [← this, e.left_inv hxs]
    · exact hF x hxs
  · exact Set.indicator_of_notMem hxf F

/-- A function living on one sheet has fibre sum zero off the target of the coordinate. -/
theorem fibreSum_of_notMem_target (hfe : f = ⇑e) (hF : ∀ y, y ∉ e.source → F y = 0) {z : ℂ}
    (hz : z ∉ e.target) : fibreSum f F z = 0 := by
  refine fibreSum_eq_zero fun y hy => hF y fun hys => hz ?_
  have : e y = z := by rwa [hfe] at hy
  rw [← this]
  exact e.map_source hys

end Sheet

/-! ### A cutoff of a disc -/

/-- **A continuous cutoff of a disc**: it vanishes near the boundary, is at most one, and rises to
one on the whole disc as the index grows. -/
def discRamp (c : ℂ) (R : ℝ) (n : ℕ) (z : ℂ) : ℝ :=
  max 0 (min 1 (((n : ℝ) + 1) * (R - dist z c) - 1))

theorem continuous_discRamp : Continuous (discRamp c R n) :=
  continuous_const.max (continuous_const.min
    ((continuous_const.mul (continuous_const.sub (continuous_id.dist continuous_const))).sub
      continuous_const))

theorem discRamp_nonneg (z : ℂ) : 0 ≤ discRamp c R n z := le_max_left _ _

theorem discRamp_le_one (z : ℂ) : discRamp c R n z ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem norm_discRamp_le_one (z : ℂ) : ‖discRamp c R n z‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (discRamp_nonneg z)]
  exact discRamp_le_one z

/-- The cutoff vanishes near the boundary of the disc. -/
theorem discRamp_eq_zero {z : ℂ} (hz : R - 1 / ((n : ℝ) + 1) ≤ dist z c) :
    discRamp c R n z = 0 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : ((n : ℝ) + 1) * (R - dist z c) - 1 ≤ 0 := by
    have h1 : R - dist z c ≤ 1 / ((n : ℝ) + 1) := by linarith
    have h2 : ((n : ℝ) + 1) * (R - dist z c) ≤ ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h1 hn.le
    rw [mul_one_div, div_self (ne_of_gt hn)] at h2
    linarith
  rw [discRamp]
  exact max_eq_left (min_le_of_right_le hle)

/-- The cutoff is one well inside the disc. -/
theorem discRamp_eq_one {z : ℂ} (hz : dist z c ≤ R - 2 / ((n : ℝ) + 1)) :
    discRamp c R n z = 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : 2 / ((n : ℝ) + 1) ≤ R - dist z c := by linarith
  have h2 : ((n : ℝ) + 1) * (2 / ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * (R - dist z c) :=
    mul_le_mul_of_nonneg_left h1 hn.le
  rw [mul_div_cancel₀ _ (ne_of_gt hn)] at h2
  rw [discRamp, min_eq_left (by linarith), max_eq_right zero_le_one]

/-- The support of the cutoff is a compact subset of the disc. -/
theorem tsupport_discRamp_subset :
    tsupport (discRamp c R n) ⊆ closedBall c (R - 1 / ((n : ℝ) + 1)) := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  by_contra hno
  exact hz (discRamp_eq_zero (le_of_lt (by simpa [mem_closedBall, not_le] using hno)))

theorem hasCompactSupport_discRamp : HasCompactSupport (discRamp c R n) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
    ((subset_tsupport _).trans tsupport_discRamp_subset)

/-- The cutoff vanishes off the disc. -/
theorem discRamp_eq_zero_of_le {z : ℂ} (hz : R ≤ dist z c) : discRamp c R n z = 0 := by
  refine discRamp_eq_zero (le_trans ?_ hz)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- **Inside the disc the cutoff is eventually one.** -/
theorem eventually_discRamp_eq_one {z : ℂ} (hz : dist z c < R) :
    ∀ᶠ m : ℕ in atTop, discRamp c R m z = 1 := by
  have hpos : 0 < R - dist z c := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / (R - dist z c))
  filter_upwards [eventually_ge_atTop N] with m hm
  refine discRamp_eq_one ?_
  have hm' : (2 : ℝ) / (R - dist z c) < (m : ℝ) + 1 := by
    have : (N : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have : 2 / ((m : ℝ) + 1) ≤ R - dist z c := by
    rw [div_le_iff₀ hmpos]
    rw [div_lt_iff₀ hpos] at hm'
    linarith
  linarith

/-- **The cutoffs converge to the indicator of the disc.** -/
theorem tendsto_discRamp (z : ℂ) :
    Tendsto (fun m : ℕ => discRamp c R m z) atTop
      (𝓝 ((ball c R).indicator (fun _ => (1 : ℝ)) z)) := by
  by_cases hz : z ∈ ball c R
  · rw [Set.indicator_of_mem hz]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_discRamp_eq_one (by simpa [mem_ball] using hz)] with m hm
    exact hm.symm
  · rw [Set.indicator_of_notMem hz]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with m
    exact (discRamp_eq_zero_of_le (by simpa [mem_ball, not_lt] using hz)).symm

/-! ### The part of a sheet above a disc -/

variable (f e c R) in
/-- **The part of a sheet above a disc**: the points of the source of the coordinate that the
projection sends into the disc. -/
def sheet : Set Y := e.source ∩ f ⁻¹' ball c R

theorem isOpen_sheet (hf : Continuous f) : IsOpen (sheet f e c R) :=
  e.open_source.inter (isOpen_ball.preimage hf)

theorem sheet_subset_source : sheet f e c R ⊆ e.source := Set.inter_subset_left

/-- On a sheet a function agrees with the function read in the coordinate. -/
theorem eqOn_sheet_comp_symm {E : Type*} (hfe : f = ⇑e) {G : Y → E} :
    Set.EqOn G (fun y => G (e.symm (f y))) (sheet f e c R) := fun y hy => by
  show G y = G (e.symm (f y))
  rw [hfe, e.left_inv (sheet_subset_source hy)]

theorem mem_sheet_symm (hfe : f = ⇑e) (hball : closedBall c R ⊆ e.target) {z : ℂ}
    (hz : z ∈ ball c R) : e.symm z ∈ sheet f e c R := by
  have hzt : z ∈ e.target := hball (ball_subset_closedBall hz)
  exact ⟨e.map_target hzt, by
    simp only [Set.mem_preimage]
    rwa [apply_symm_of_isChartAt hfe hzt]⟩

/-- The part of a sheet above a disc is carried by a compact piece of the sheet. -/
theorem isCompact_symm_image {r : ℝ} (hsub : closedBall c r ⊆ e.target) :
    IsCompact (e.symm '' closedBall c r) :=
  (isCompact_closedBall c r).image_of_continuousOn (e.continuousOn_symm.mono hsub)

theorem symm_image_subset_source {r : ℝ} (hsub : closedBall c r ⊆ e.target) :
    e.symm '' closedBall c r ⊆ e.source := by
  rintro _ ⟨z, hz, rfl⟩
  exact e.map_target (hsub hz)

theorem sheet_subset_symm_image (hfe : f = ⇑e) :
    sheet f e c R ⊆ e.symm '' closedBall c R := fun y hy =>
  ⟨f y, ball_subset_closedBall hy.2, by rw [hfe]; exact e.left_inv hy.1⟩

/-! ### Cutoffs on the total space -/

/-- **A cutoff on the total space living on one sheet**: the cutoff of the disc, read through the
projection on the source of the coordinate and extended by zero. -/
def sheetRamp (f : Y → ℂ) (e : OpenPartialHomeomorph Y ℂ) (c : ℂ) (R : ℝ) (n : ℕ) (y : Y) : ℝ :=
  e.source.indicator (fun y' => discRamp c R n (f y')) y

theorem sheetRamp_of_mem_source {y : Y} (hy : y ∈ e.source) :
    sheetRamp f e c R n y = discRamp c R n (f y) := Set.indicator_of_mem hy _

theorem sheetRamp_of_notMem_source {y : Y} (hy : y ∉ e.source) : sheetRamp f e c R n y = 0 :=
  Set.indicator_of_notMem hy _

theorem sheetRamp_nonneg (y : Y) : 0 ≤ sheetRamp f e c R n y :=
  Set.indicator_nonneg (fun _ _ => discRamp_nonneg _) y

theorem sheetRamp_le_one (y : Y) : sheetRamp f e c R n y ≤ 1 := by
  by_cases hy : y ∈ e.source
  · rw [sheetRamp_of_mem_source hy]
    exact discRamp_le_one _
  · rw [sheetRamp_of_notMem_source hy]
    exact zero_le_one

theorem norm_sheetRamp_le_one (y : Y) : ‖sheetRamp f e c R n y‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sheetRamp_nonneg y)]
  exact sheetRamp_le_one y

theorem sheetRamp_symm (hfe : f = ⇑e) {z : ℂ} (hz : z ∈ e.target) :
    sheetRamp f e c R n (e.symm z) = discRamp c R n z := by
  rw [sheetRamp_of_mem_source (e.map_target hz), apply_symm_of_isChartAt hfe hz]

theorem support_sheetRamp_subset (hfe : f = ⇑e) :
    Function.support (sheetRamp f e c R n) ⊆ e.symm '' closedBall c R := by
  intro y hy
  rw [Function.mem_support] at hy
  by_cases hys : y ∈ e.source
  · rw [sheetRamp_of_mem_source hys] at hy
    have hlt : dist (f y) c < R := by
      by_contra hno
      exact hy (discRamp_eq_zero_of_le (not_lt.mp hno))
    exact ⟨f y, le_of_lt hlt, by rw [hfe]; exact e.left_inv hys⟩
  · exact absurd (sheetRamp_of_notMem_source hys) hy

theorem continuous_sheetRamp [T2Space Y] (hf : Continuous f) (hfe : f = ⇑e)
    (hball : closedBall c R ⊆ e.target) : Continuous (sheetRamp f e c R n) := by
  have hK : IsCompact (e.symm '' closedBall c R) := isCompact_symm_image hball
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ e.source
  · refine ContinuousAt.congr
      ((continuous_discRamp (c := c) (R := R) (n := n)).comp hf).continuousAt ?_
    filter_upwards [e.open_source.mem_nhds hy] with y' hy'
    exact (sheetRamp_of_mem_source hy').symm
  · have hyK : y ∉ e.symm '' closedBall c R := fun h => hy (symm_image_subset_source hball h)
    have hconst : ContinuousAt (fun _ : Y => (0 : ℝ)) y := continuousAt_const
    refine hconst.congr ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hyK] with y' hy'
    exact (Function.notMem_support.mp fun h => hy' (support_sheetRamp_subset hfe h)).symm

theorem hasCompactSupport_sheetRamp [T2Space Y] (hfe : f = ⇑e)
    (hball : closedBall c R ⊆ e.target) : HasCompactSupport (sheetRamp f e c R n) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_symm_image hball)
    (support_sheetRamp_subset hfe)

/-- **The cutoffs on the total space converge to the indicator of the sheet.** -/
theorem tendsto_sheetRamp (y : Y) :
    Tendsto (fun m : ℕ => sheetRamp f e c R m y) atTop
      (𝓝 ((sheet f e c R).indicator (fun _ => (1 : ℝ)) y)) := by
  by_cases hy : y ∈ e.source
  · have hind : (sheet f e c R).indicator (fun _ => (1 : ℝ)) y
        = (ball c R).indicator (fun _ => (1 : ℝ)) (f y) := by
      by_cases hb : f y ∈ ball c R
      · have hmem : y ∈ sheet f e c R := ⟨hy, hb⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hb]
      · rw [Set.indicator_of_notMem fun h => hb h.2, Set.indicator_of_notMem hb]
    rw [hind]
    exact Tendsto.congr (fun m => (sheetRamp_of_mem_source hy).symm) (tendsto_discRamp (f y))
  · rw [Set.indicator_of_notMem fun h => hy h.1]
    exact Tendsto.congr (fun m => (sheetRamp_of_notMem_source hy).symm) tendsto_const_nhds

/-! ### The measure of a sheet -/

section Measure

variable (hfin : ∀ z, (f ⁻¹' {z}).Finite)
  (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
  {w : ℂ → ℝ} (hw : Continuous w) (hwnn : ∀ z, 0 ≤ w z)
  [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **The integral of a function living on one sheet** is the weighted plane integral of the
function read in the coordinate. -/
theorem integral_weightMeasure_of_subset_source (hfe : f = ⇑e) {F : Y → ℝ} (hFc : Continuous F)
    (hFs : HasCompactSupport F) (hFsupp : ∀ y, y ∉ e.source → F y = 0) :
    ∫ y, F y ∂(weightMeasure f hfin hcov hf w hw hwnn) = ∫ z in e.target, F (e.symm z) * w z := by
  have hzero : ∀ y, y ∉ e.source → F y * w (f y) = 0 := fun y hy => by rw [hFsupp y hy, zero_mul]
  rw [integral_weightMeasure_real hfin hcov hf hw hwnn hFc hFs,
    ← integral_indicator e.open_target.measurableSet]
  refine integral_congr_ae (.of_forall fun z => ?_)
  by_cases hz : z ∈ e.target
  · rw [Set.indicator_of_mem hz, fibreSum_of_mem_target hfe hzero hz,
      apply_symm_of_isChartAt hfe hz]
  · rw [Set.indicator_of_notMem hz, fibreSum_of_notMem_target hfe hzero hz]

/-- **The integral over a sheet of a function pulled back from the plane.** -/
theorem integral_sheet_comp (hfe : f = ⇑e) (hball : closedBall c R ⊆ e.target) {φ : ℂ → ℝ}
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∫ y in sheet f e c R, φ (f y) ∂(weightMeasure f hfin hcov hf w hw hwnn)
      = ∫ z in ball c R, φ z * w z := by
  obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support hφs
  have hKc : IsCompact (e.symm '' closedBall c R) := isCompact_symm_image hball
  have hFcont : ∀ m : ℕ, Continuous fun y => sheetRamp f e c R m y * φ (f y) := fun _ =>
    (continuous_sheetRamp hf hfe hball).mul (hφc.comp hf)
  have hFcs : ∀ m : ℕ, HasCompactSupport fun y => sheetRamp f e c R m y * φ (f y) := fun _ =>
    (hasCompactSupport_sheetRamp hfe hball).mul_right
  have hFsupp : ∀ m : ℕ, ∀ y, y ∉ e.source → sheetRamp f e c R m y * φ (f y) = 0 := fun _ y hy => by
    rw [sheetRamp_of_notMem_source hy, zero_mul]
  -- the sequence tends to the integral over the sheet
  have hL : Tendsto (fun m : ℕ => ∫ y, sheetRamp f e c R m y * φ (f y)
      ∂(weightMeasure f hfin hcov hf w hw hwnn)) atTop
      (𝓝 (∫ y in sheet f e c R, φ (f y) ∂(weightMeasure f hfin hcov hf w hw hwnn))) := by
    rw [← integral_indicator (isOpen_sheet hf).measurableSet]
    refine tendsto_integral_of_dominated_convergence
      ((e.symm '' closedBall c R).indicator fun _ => C)
      (fun m => (hFcont m).aestronglyMeasurable)
      ((integrableOn_const hKc.measure_lt_top.ne).integrable_indicator hKc.measurableSet)
      (fun m => .of_forall fun y => ?_) (.of_forall fun y => ?_)
    · by_cases hyK : y ∈ e.symm '' closedBall c R
      · rw [Set.indicator_of_mem hyK, norm_mul]
        calc ‖sheetRamp f e c R m y‖ * ‖φ (f y)‖ ≤ 1 * ‖φ (f y)‖ :=
              mul_le_mul_of_nonneg_right (norm_sheetRamp_le_one y) (norm_nonneg _)
          _ ≤ C := by rw [one_mul]; exact hC (f y)
      · rw [Set.indicator_of_notMem hyK,
          Function.notMem_support.mp fun h => hyK (support_sheetRamp_subset hfe h), zero_mul,
          norm_zero]
    · have heq : (sheet f e c R).indicator (fun _ => (1 : ℝ)) y * φ (f y)
          = (sheet f e c R).indicator (fun y => φ (f y)) y := by
        by_cases hy : y ∈ sheet f e c R
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
      rw [← heq]
      exact (tendsto_sheetRamp (f := f) (e := e) (c := c) (R := R) y).mul_const (φ (f y))
  -- the same sequence tends to the weighted plane integral
  have hstep : ∀ m : ℕ, ∫ y, sheetRamp f e c R m y * φ (f y)
      ∂(weightMeasure f hfin hcov hf w hw hwnn)
      = ∫ z in e.target, discRamp c R m z * φ z * w z := by
    intro m
    rw [integral_weightMeasure_of_subset_source hfin hcov hf hw hwnn hfe (hFcont m) (hFcs m)
      (hFsupp m)]
    refine setIntegral_congr_fun e.open_target.measurableSet fun z hz => ?_
    rw [sheetRamp_symm hfe hz, apply_symm_of_isChartAt hfe hz]
  have hplane : Tendsto (fun m : ℕ => ∫ z in e.target, discRamp c R m z * φ z * w z) atTop
      (𝓝 (∫ z in ball c R, φ z * w z)) := by
    have hball' : ball c R ⊆ e.target := (ball_subset_closedBall).trans hball
    have hrw : ∫ z in ball c R, φ z * w z
        = ∫ z in e.target, (ball c R).indicator (fun _ => (1 : ℝ)) z * φ z * w z := by
      have hcongr : ∫ z in e.target, (ball c R).indicator (fun _ => (1 : ℝ)) z * φ z * w z
          = ∫ z in e.target, (ball c R).indicator (fun z => φ z * w z) z := by
        refine setIntegral_congr_fun e.open_target.measurableSet fun z _ => ?_
        by_cases hz : z ∈ ball c R
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul, zero_mul]
      rw [hcongr, setIntegral_indicator measurableSet_ball, Set.inter_eq_right.mpr hball']
    rw [hrw]
    refine tendsto_integral_of_dominated_convergence
      ((closedBall c R).indicator fun z => |φ z * w z|)
      (fun m => (((continuous_discRamp.mul hφc).mul hw).aestronglyMeasurable))
      (((((hφc.mul hw).abs).continuousOn.integrableOn_compact
        (isCompact_closedBall c R)).integrable_indicator measurableSet_closedBall).restrict)
      (fun m => .of_forall fun z => ?_) (.of_forall fun z => ?_)
    · by_cases hz : z ∈ closedBall c R
      · rw [Set.indicator_of_mem hz, mul_assoc, norm_mul, Real.norm_eq_abs (φ z * w z)]
        exact mul_le_of_le_one_left (abs_nonneg _) (norm_discRamp_le_one z)
      · rw [Set.indicator_of_notMem hz,
          discRamp_eq_zero_of_le (not_lt.mp fun h => hz (le_of_lt h)), zero_mul, zero_mul,
          norm_zero]
    · exact ((tendsto_discRamp z).mul_const (φ z)).mul_const (w z)
  exact tendsto_nhds_unique hL (Tendsto.congr (fun m => (hstep m).symm) hplane)

/-- **The projection carries the measure of the covering, restricted to a sheet above a disc, to
the weighted plane measure of the disc.** -/
theorem map_weightMeasure_restrict_sheet (hfe : f = ⇑e) (hball : closedBall c R ⊆ e.target) :
    ((weightMeasure f hfin hcov hf w hw hwnn).restrict (sheet f e c R)).map f
      = (volume.withDensity fun z => ENNReal.ofReal (w z)).restrict (ball c R) := by
  have hKc : IsCompact (e.symm '' closedBall c R) := isCompact_symm_image hball
  haveI : IsFiniteMeasure
      ((weightMeasure f hfin hcov hf w hw hwnn).restrict (sheet f e c R)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono (sheet_subset_symm_image hfe)) hKc.measure_lt_top
  haveI : IsFiniteMeasure
      ((volume.withDensity fun z => ENNReal.ofReal (w z)).restrict (ball c R)) := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hw.continuousOn
    have hwM : ∀ z ∈ ball c R, w z ≤ M := fun z hz =>
      (le_abs_self _).trans (by simpa using hM z (ball_subset_closedBall hz))
    constructor
    rw [Measure.restrict_apply_univ, withDensity_apply _ measurableSet_ball]
    have hle : ∫⁻ z in ball c R, ENNReal.ofReal (w z) ≤ ∫⁻ _ in ball c R, ENNReal.ofReal M :=
      setLIntegral_mono measurable_const fun z hz => ENNReal.ofReal_le_ofReal (hwM z hz)
    refine lt_of_le_of_lt hle ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  refine Measure.ext_of_integral_eq_on_compactlySupported fun φ => ?_
  have hφc : Continuous fun z : ℂ => φ z := φ.continuous
  have hφs : HasCompactSupport fun z : ℂ => φ z := φ.hasCompactSupport
  have hlhs : ∫ z, φ z ∂(((weightMeasure f hfin hcov hf w hw hwnn).restrict
      (sheet f e c R)).map f) = ∫ z in ball c R, φ z * w z := by
    rw [integral_map hf.measurable.aemeasurable hφc.aestronglyMeasurable]
    exact integral_sheet_comp hfin hcov hf hw hwnn hfe hball hφc hφs
  have hrhs : ∫ z, φ z ∂((volume.withDensity fun z => ENNReal.ofReal (w z)).restrict (ball c R))
      = ∫ z in ball c R, φ z * w z := by
    rw [restrict_withDensity measurableSet_ball]
    have hd : (fun z => ENNReal.ofReal (w z))
        = fun z => ((Real.toNNReal (w z) : NNReal) : ENNReal) := rfl
    rw [hd, integral_withDensity_eq_integral_smul hw.measurable.real_toNNReal fun z => φ z]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hwnn z), smul_eq_mul, mul_comm]
  rw [hlhs, hrhs]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Reading a function through the coordinate is measurable for the measure the projection carries
the sheet to. -/
theorem aestronglyMeasurable_map_sheet (hfe : f = ⇑e) (hball : closedBall c R ⊆ e.target)
    {G : Y → E} (hG : AEStronglyMeasurable (fun z => G (e.symm z)) (volume.restrict (ball c R))) :
    AEStronglyMeasurable (fun z => G (e.symm z))
      (Measure.map f ((weightMeasure f hfin hcov hf w hw hwnn).restrict (sheet f e c R))) := by
  rw [map_weightMeasure_restrict_sheet hfin hcov hf hw hwnn hfe hball,
    restrict_withDensity measurableSet_ball]
  exact hG.mono_ac (withDensity_absolutelyContinuous _ _)

/-- **The integral over a sheet above a disc** is the weighted plane integral of the function read
in the coordinate. -/
theorem integral_weightMeasure_sheet (hfe : f = ⇑e) (hball : closedBall c R ⊆ e.target) {G : Y → E}
    (hG : AEStronglyMeasurable (fun z => G (e.symm z)) (volume.restrict (ball c R))) :
    ∫ y in sheet f e c R, G y ∂(weightMeasure f hfin hcov hf w hw hwnn)
      = ∫ z in ball c R, w z • G (e.symm z) := by
  rw [setIntegral_congr_fun (isOpen_sheet hf).measurableSet (eqOn_sheet_comp_symm hfe),
    ← integral_map hf.measurable.aemeasurable
      (aestronglyMeasurable_map_sheet hfin hcov hf hw hwnn hfe hball hG),
    map_weightMeasure_restrict_sheet hfin hcov hf hw hwnn hfe hball,
    restrict_withDensity measurableSet_ball]
  have hd : (fun z => ENNReal.ofReal (w z))
      = fun z => ((Real.toNNReal (w z) : NNReal) : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul hw.measurable.real_toNNReal]
  refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (hwnn z)]

/-- **A function integrable over a sheet above a disc is integrable over the disc when read in the
coordinate**, the weight being bounded below there. -/
theorem integrableOn_comp_symm (hfe : f = ⇑e) (hball : closedBall c R ⊆ e.target)
    (hwpos : ∀ z, 0 < w z) {G : Y → E}
    (hG : AEStronglyMeasurable (fun z => G (e.symm z)) (volume.restrict (ball c R)))
    (hint : IntegrableOn G (sheet f e c R) (weightMeasure f hfin hcov hf w hw hwnn)) :
    IntegrableOn (fun z => G (e.symm z)) (ball c R) volume := by
  have hsheet : Integrable (fun y => G (e.symm (f y)))
      ((weightMeasure f hfin hcov hf w hw hwnn).restrict (sheet f e c R)) :=
    hint.congr ((ae_restrict_iff' (isOpen_sheet hf).measurableSet).2
      (.of_forall fun y hy => eqOn_sheet_comp_symm hfe hy))
  have h1 : Integrable (fun z => G (e.symm z))
      (Measure.map f ((weightMeasure f hfin hcov hf w hw hwnn).restrict (sheet f e c R))) :=
    (integrable_map_measure (aestronglyMeasurable_map_sheet hfin hcov hf hw hwnn hfe hball hG)
      hf.measurable.aemeasurable).2 hsheet
  rw [map_weightMeasure_restrict_sheet hfin hcov hf hw hwnn hfe hball,
    restrict_withDensity measurableSet_ball,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (.of_forall fun z => ENNReal.ofReal_lt_top)] at h1
  have h2 : Integrable (fun z => w z • G (e.symm z)) (volume.restrict (ball c R)) := by
    refine h1.congr (.of_forall fun z => ?_)
    show (ENNReal.ofReal (w z)).toReal • G (e.symm z) = w z • G (e.symm z)
    rw [ENNReal.toReal_ofReal (hwnn z)]
  obtain ⟨δ, hδ0, hδ⟩ :=
    (isCompact_closedBall c R).exists_forall_le' hw.continuousOn (a := (0 : ℝ)) fun z _ => hwpos z
  refine Integrable.mono' (h2.norm.const_mul δ⁻¹) hG ?_
  refine (ae_restrict_iff' measurableSet_ball).2 (.of_forall fun z hz => ?_)
  have hwz : δ ≤ w z := hδ z (ball_subset_closedBall hz)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hwnn z), ← mul_assoc]
  refine le_mul_of_one_le_left (norm_nonneg _) ?_
  rw [← div_eq_inv_mul, le_div_iff₀ hδ0, one_mul]
  exact hwz

end Measure

end Rigidity.RET

end
