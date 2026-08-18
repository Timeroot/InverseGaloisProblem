/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverBound
import InverseGalois.Rigidity.RET.Analytic.Dbar.DiscChart
import InverseGalois.Rigidity.RET.Analytic.Dbar.LogWeight
import InverseGalois.Rigidity.RET.Analytic.Moderate

/-!
# The growth of the solution

The solution of the Cauchy–Riemann equation on a covering of a punctured plane carries a bound on
every disc over which it is holomorphic, and it is holomorphic away from the support of the source
of the equation.  Since that support is compact, a point far from it has a disc around its image
missing both the punctures and the image of the support, and over such a disc the bound applies.
Near a puncture the largest available disc has radius comparable to the distance to the puncture,
so the bound degrades like the reciprocal of that distance; at infinity a disc of radius one is
always available, and the weight then costs a factor of the square of the base coordinate.  Both
degradations are of moderate growth.

## Main results

* `Rigidity.RET.norm_sq_le_of_disc` — the bound, applied to a disc missing the punctures and the
  support of the source.
* `Rigidity.RET.isModerate_of_hasDiscBound` — **the solution is of moderate growth.**
-/

open Metric Topology Set

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f g u : Y → ℂ} {S : Finset ℂ} {B : ℝ}

/-! ### The bound on a disc of the base -/

/-- **The bound, applied to a disc of the base missing the punctures and the image of the support
of the source of the equation.** -/
theorem norm_sq_le_of_disc (hf : Continuous f) (hlh : IsLocalHomeomorph f)
    (hcov : IsCoveringMapOn f ((S : Set ℂ)ᶜ)) (hdbar : ∀ y, IsDbarAt f u (g y) y)
    (hbd : HasDiscBound f logWeight u B) {y : Y} {R r M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hball : ball (f y) R ⊆ ((S : Set ℂ)ᶜ))
    (hvan : ∀ y' : Y, f y' ∈ ball (f y) R → g y' = 0)
    (hM : ∀ z ∈ ball (f y) r, ‖z‖ ≤ M) :
    (Real.pi * r ^ 2) * ‖u y‖ ^ 2 ≤ (1 + M ^ 2) * B := by
  obtain ⟨e, hfe, htgt, hsymm⟩ := exists_chart_ball hf hlh hcov (hr.trans hrR) hball rfl
  have hsub : ball (f y) R ⊆ e.target := htgt.ge
  have hholo : ∀ z ∈ ball (f y) R, DifferentiableAt ℂ (fun t : ℂ => u (e.symm t)) z := by
    intro z hz
    have hzt : z ∈ e.target := hsub hz
    have hfz : f (e.symm z) = z := apply_symm_of_isChartAt hfe hzt
    have hg0 : g (e.symm z) = 0 := hvan _ (by rw [hfz]; exact hz)
    have hd : IsDbarAt f u 0 (e.symm z) := by
      have h := hdbar (e.symm z)
      rwa [hg0] at h
    exact differentiableAt_symm_of_isDbarAt_zero hfe hzt hd
  have hK : ∀ z ∈ ball (f y) r, 1 ≤ (1 + M ^ 2) * weightOf logWeight z := fun z hz =>
    one_le_mul_weightOf_logWeight (hM z hz)
  have h := hbd e hfe (f y) R r (1 + M ^ 2) hr hrR hsub hholo hK
  rwa [hsymm] at h

/-! ### Moderate growth -/

/-- **The solution of the Cauchy–Riemann equation is of moderate growth**: near a puncture the
distance to it times the solution is bounded, and at infinity the solution grows no faster than
the base coordinate. -/
theorem isModerate_of_hasDiscBound (hf : Continuous f) (hlh : IsLocalHomeomorph f)
    (hcov : IsCoveringMapOn f ((S : Set ℂ)ᶜ)) (hrange : ∀ y : Y, f y ∈ ((S : Set ℂ)ᶜ))
    (hdbar : ∀ y, IsDbarAt f u (g y) y) {Kc : Set Y} (hKc : IsCompact Kc)
    (hgvan : ∀ y ∉ Kc, g y = 0) (hB : 0 ≤ B) (hbd : HasDiscBound f logWeight u B) :
    IsModerate f S u where
  punct := by
    intro s hs
    -- the punctures other than `s`, and the image of the support of the source, form a closed set
    -- avoiding `s`
    set Z : Set ℂ := f '' Kc ∪ ((S : Set ℂ) \ {s}) with hZdef
    have hZclosed : IsClosed Z :=
      (hKc.image hf).isClosed.union (S.finite_toSet.subset diff_subset).isClosed
    have hsZ : s ∉ Z := by
      rintro (⟨y, -, hy⟩ | ⟨-, hy⟩)
      · apply hrange y
        rw [hy]
        exact Finset.mem_coe.mpr hs
      · exact hy rfl
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hZclosed.isOpen_compl s hsZ
    have hZdist : ∀ w ∈ Z, ε ≤ dist w s := by
      intro w hw
      by_contra hlt
      exact hεsub (mem_ball.mpr (not_le.mp hlt)) hw
    set δ : ℝ := ε / 2 with hδdef
    have hδ : 0 < δ := by positivity
    have hεδ : ε = 2 * δ := by rw [hδdef]; ring
    refine ⟨δ, hδ, Real.sqrt (16 * (1 + (‖s‖ + 2 * δ) ^ 2) * B / Real.pi), Real.sqrt_nonneg _,
      1, fun y hy => ?_⟩
    obtain ⟨hy1, hy2⟩ := hy
    set d : ℝ := ‖f y - s‖ with hddef
    have hne : f y - s ≠ 0 := sub_ne_zero.mpr (by simpa using hy2)
    have hd0 : 0 < d := by
      rw [hddef]
      exact norm_pos_iff.mpr hne
    have hdδ : d < δ := by
      have h := mem_ball.mp hy1
      rw [dist_eq_norm] at h
      rw [hddef]
      exact h
    -- a disc of radius `d / 2` around the image of the point misses everything to be avoided
    have hZavoid : ∀ w ∈ ball (f y) (d / 2), w ∉ Z := by
      intro w hw hwZ
      have h1 : dist w (f y) < d / 2 := mem_ball.mp hw
      have h2 : ε ≤ dist w s := hZdist w hwZ
      have h3 : dist w s ≤ dist w (f y) + dist (f y) s := dist_triangle _ _ _
      have h4 : dist (f y) s = d := by rw [dist_eq_norm, hddef]
      linarith
    have hballS : ball (f y) (d / 2) ⊆ ((S : Set ℂ)ᶜ) := by
      intro w hw
      simp only [Set.mem_compl_iff, Finset.mem_coe]
      intro hwS
      by_cases hws : w = s
      · have h1 : dist w (f y) < d / 2 := mem_ball.mp hw
        rw [hws, dist_comm, dist_eq_norm] at h1
        linarith
      · exact hZavoid w hw (Or.inr ⟨Finset.mem_coe.mpr hwS, hws⟩)
    have hvan : ∀ y' : Y, f y' ∈ ball (f y) (d / 2) → g y' = 0 := by
      intro y' hy'
      by_contra hg
      have hmem : y' ∈ Kc := by
        by_contra hnot
        exact hg (hgvan y' hnot)
      exact hZavoid _ hy' (Or.inl ⟨y', hmem, rfl⟩)
    have hM : ∀ z ∈ ball (f y) (d / 4), ‖z‖ ≤ ‖s‖ + 2 * δ := by
      intro z hz
      have h1 : dist z (f y) < d / 4 := mem_ball.mp hz
      rw [dist_eq_norm] at h1
      have he : z = z - f y + (f y - s) + s := by ring
      have h2 : ‖z‖ ≤ ‖z - f y‖ + ‖f y - s‖ + ‖s‖ := by
        calc ‖z‖ = ‖z - f y + (f y - s) + s‖ := by rw [← he]
          _ ≤ ‖z - f y + (f y - s)‖ + ‖s‖ := norm_add_le _ _
          _ ≤ ‖z - f y‖ + ‖f y - s‖ + ‖s‖ := by
              have h := norm_add_le (z - f y) (f y - s)
              linarith
      linarith
    have hkey := norm_sq_le_of_disc hf hlh hcov hdbar hbd (r := d / 4) (R := d / 2)
      (by linarith) (by linarith) hballS hvan hM
    rw [pow_one]
    have hsq : (‖u y‖ * d) ^ 2 ≤ 16 * (1 + (‖s‖ + 2 * δ) ^ 2) * B / Real.pi := by
      rw [mul_pow, le_div_iff₀ Real.pi_pos]
      nlinarith [hkey, Real.pi_pos]
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity)] at hle
  infty := by
    -- the punctures and the image of the support of the source lie in a disc of the base
    obtain ⟨r₀, hr₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
      ((hKc.image hf).isBounded.union S.finite_toSet.isBounded)
    refine ⟨Real.sqrt (13 * B / Real.pi), max (r₀ + 1) 1, 1, Real.sqrt_nonneg _, fun y hy => ?_⟩
    have hy1 : (1 : ℝ) ≤ ‖f y‖ := le_trans (le_max_right _ _) hy
    have hy0 : r₀ + 1 ≤ ‖f y‖ := le_trans (le_max_left _ _) hy
    -- the disc of radius one around the image of the point misses everything to be avoided
    have havoid : ∀ w ∈ ball (f y) (1 : ℝ), w ∉ f '' Kc ∪ ((S : Set ℂ)) := by
      intro w hw hwZ
      have h1 : ‖w - f y‖ < 1 := by
        have h := mem_ball.mp hw
        rwa [dist_eq_norm] at h
      have h2 : ‖w‖ ≤ r₀ := by
        have h := hr₀ hwZ
        rwa [mem_closedBall, dist_zero_right] at h
      have h3 : ‖f y‖ ≤ ‖f y - w‖ + ‖w‖ := by
        have h := norm_add_le (f y - w) w
        simpa using h
      have h4 : ‖f y - w‖ = ‖w - f y‖ := norm_sub_rev _ _
      linarith
    have hballS : ball (f y) (1 : ℝ) ⊆ ((S : Set ℂ)ᶜ) := fun w hw hwS =>
      havoid w hw (Or.inr hwS)
    have hvan : ∀ y' : Y, f y' ∈ ball (f y) (1 : ℝ) → g y' = 0 := by
      intro y' hy'
      by_contra hg
      have hmem : y' ∈ Kc := by
        by_contra hnot
        exact hg (hgvan y' hnot)
      exact havoid _ hy' (Or.inl ⟨y', hmem, rfl⟩)
    have hM : ∀ z ∈ ball (f y) (1 / 2 : ℝ), ‖z‖ ≤ ‖f y‖ + 1 / 2 := by
      intro z hz
      have h1 : ‖z - f y‖ < 1 / 2 := by
        have h := mem_ball.mp hz
        rwa [dist_eq_norm] at h
      have h2 : ‖z‖ ≤ ‖z - f y‖ + ‖f y‖ := by
        have h := norm_add_le (z - f y) (f y)
        simpa using h
      linarith
    have hkey := norm_sq_le_of_disc hf hlh hcov hdbar hbd (r := (1 / 2 : ℝ)) (R := (1 : ℝ))
      (by norm_num) (by norm_num) hballS hvan hM
    rw [pow_one]
    have hfac : 0 ≤ B * (9 * ‖f y‖ ^ 2 - 4 * ‖f y‖ - 5) := by
      refine mul_nonneg hB ?_
      nlinarith
    have hgoal : Real.pi * ‖u y‖ ^ 2 ≤ 13 * B * ‖f y‖ ^ 2 := by nlinarith [hkey, hfac]
    have hsq : ‖u y‖ ^ 2 ≤ (Real.sqrt (13 * B / Real.pi) * ‖f y‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 13 * B / Real.pi),
        div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
      nlinarith [hgoal]
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hle

end Rigidity.RET

end
