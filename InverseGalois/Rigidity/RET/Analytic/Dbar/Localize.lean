/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Commutator

/-!
# Reading the plane identities on an open set

The identities of the Cauchy–Riemann calculus are local, but the ones proved for the plane ask for
a function that is differentiable everywhere.  Multiplying by a cut-off replaces a function that is
differentiable on an open set by one that is differentiable everywhere and agrees with it near a
given point of that set, and the identities then transfer.

This is what lets the calculus of a covering, where a function is only ever read in a local
coordinate, appeal to the identities already proved for the plane.

## Main results

* `Rigidity.RET.exists_globalize` — a function differentiable on an open set agrees near each of
  its points with one differentiable on the whole plane.
* `Rigidity.RET.continuousAt_dbar_local`, `Rigidity.RET.contDiffAt_dbar_local` — the regularity of
  the operators, asked only on an open set.
* `Rigidity.RET.dbar_dz_comm_local`, `Rigidity.RET.dbar_deltaOp_sub_local` — the commutation
  identities, asked only on an open set.
-/

open Metric Topology

open scoped ContDiff

noncomputable section

namespace Rigidity.RET

/-- The holomorphic derivative only sees a function near the point. -/
theorem dz_congr {u v : ℂ → ℂ} {z : ℂ} (h : u =ᶠ[𝓝 z] v) : dz u z = dz v z := by
  simp only [dz, h.fderiv_eq]

/-- The holomorphic derivative is additive. -/
theorem dz_add {u v : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dz (fun w => u w + v w) z = dz u z + dz v z := by
  have h : fderiv ℝ (fun w => u w + v w) z = fderiv ℝ u z + fderiv ℝ v z :=
    (hu.hasFDerivAt.add hv.hasFDerivAt).fderiv
  simp only [dz, h, ContinuousLinearMap.add_apply]
  ring

/-- The holomorphic derivative is compatible with negation. -/
theorem dz_neg {u : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℝ u z) :
    dz (fun w => -u w) z = -dz u z := by
  have h : fderiv ℝ (fun w => -u w) z = -fderiv ℝ u z := hu.hasFDerivAt.neg.fderiv
  simp only [dz, h, ContinuousLinearMap.neg_apply]
  ring

/-- **The product rule for the holomorphic derivative.** -/
theorem dz_mul {u v : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dz (fun w => u w * v w) z = u z * dz v z + v z * dz u z := by
  have h : fderiv ℝ (fun w => u w * v w) z = u z • fderiv ℝ v z + v z • fderiv ℝ u z :=
    (hu.hasFDerivAt.mul hv.hasFDerivAt).fderiv
  simp only [dz, h, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Globalizing by a cut-off -/

/-- **A function differentiable on an open set agrees, near any point of that set, with one
differentiable on the whole plane.**  Multiply by a cut-off supported in a disc inside the set. -/
theorem exists_globalize {n : WithTop ℕ∞} (hn : n ≤ ∞) {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) {v : ℂ → ℂ} (hv : ∀ z ∈ U, ContDiffAt ℝ n v z) :
    ∃ (w : ℂ → ℂ) (V : Set ℂ), ContDiff ℝ n w ∧ IsOpen V ∧ z₀ ∈ V ∧ ∀ z ∈ V, w z = v z := by
  classical
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set b : ContDiffBump z₀ := ⟨ρ / 8, ρ / 4, by positivity, by linarith⟩ with hb
  set χ : ℂ → ℂ := fun z => ((b z : ℝ) : ℂ) with hχdef
  have hχtop : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hχ : ContDiff ℝ n χ := hχtop.of_le hn
  set v₀ : ℂ → ℂ := fun z => if z ∈ U then v z else 0 with hv₀def
  have hv₀ : ∀ z ∈ U, ContDiffAt ℝ n v₀ z := by
    intro z hz
    refine (hv z hz).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hz] with t ht
    simp [hv₀def, ht]
  have hsub : closedBall z₀ (ρ / 4) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  refine ⟨fun z => χ z * v₀ z, ball z₀ (ρ / 8), ?_, isOpen_ball,
    mem_ball_self (by positivity), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact hχ.contDiffAt.mul (hv₀ z hz)
    · have hout : ρ / 4 < dist z z₀ := by
        by_contra hle
        push_neg at hle
        exact hz (hsub (mem_closedBall.2 hle))
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      have hopen : IsOpen {t : ℂ | ρ / 4 < dist t z₀} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      filter_upwards [hopen.mem_nhds hout] with t ht
      simp [hχdef, b.zero_of_le_dist (le_of_lt ht)]
  · intro z hz
    have h1 : b z = 1 := b.one_of_mem_closedBall (ball_subset_closedBall hz)
    have h2 : z ∈ U := hball (ball_subset_ball (by linarith) hz)
    simp [hχdef, hv₀def, h1, h2]

/-! ### The identities on an open set -/

/-- **The two first-order operators commute**, asked only on an open set. -/
theorem dbar_dz_comm_local {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) {v : ℂ → ℂ}
    (hv : ∀ z' ∈ U, ContDiffAt ℝ 2 v z') : dbar (dz v) z = dz (dbar v) z := by
  obtain ⟨w, V, hw, hV, hzV, hagree⟩ := exists_globalize (n := 2) (by norm_cast) hU hz hv
  have hdz : ∀ z' ∈ V, dz w z' = dz v z' := fun z' hz' =>
    dz_congr (by filter_upwards [hV.mem_nhds hz'] with t ht using hagree t ht)
  have hdbar : ∀ z' ∈ V, dbar w z' = dbar v z' := fun z' hz' =>
    dbar_congr (by filter_upwards [hV.mem_nhds hz'] with t ht using hagree t ht)
  have e1 : dbar (dz v) z = dbar (dz w) z :=
    dbar_congr (by filter_upwards [hV.mem_nhds hzV] with t ht using (hdz t ht).symm)
  have e2 : dz (dbar w) z = dz (dbar v) z :=
    dz_congr (by filter_upwards [hV.mem_nhds hzV] with t ht using hdbar t ht)
  rw [e1, dbar_dz_comm hw, e2]

/-- **The Cauchy–Riemann operator of a function continuously differentiable on an open set is
continuous there.** -/
theorem continuousAt_dbar_local {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) {v : ℂ → ℂ}
    (hv : ∀ z' ∈ U, ContDiffAt ℝ 1 v z') : ContinuousAt (dbar v) z := by
  obtain ⟨w, V, hw, hV, hzV, hagree⟩ := exists_globalize (n := 1) (by simp) hU hz hv
  have hev : dbar w =ᶠ[𝓝 z] dbar v := by
    filter_upwards [hV.mem_nhds hzV] with t ht
    exact dbar_congr (by filter_upwards [hV.mem_nhds ht] with r hr using hagree r hr)
  exact (continuous_dbar hw).continuousAt.congr hev

/-- **The holomorphic derivative of a function continuously differentiable on an open set is
continuous there.** -/
theorem continuousAt_dz_local {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) {v : ℂ → ℂ}
    (hv : ∀ z' ∈ U, ContDiffAt ℝ 1 v z') : ContinuousAt (dz v) z := by
  obtain ⟨w, V, hw, hV, hzV, hagree⟩ := exists_globalize (n := 1) (by simp) hU hz hv
  have hev : dz w =ᶠ[𝓝 z] dz v := by
    filter_upwards [hV.mem_nhds hzV] with t ht
    exact dz_congr (by filter_upwards [hV.mem_nhds ht] with r hr using hagree r hr)
  exact (continuous_dz hw).continuousAt.congr hev

/-- **Each of the two operators costs one degree of smoothness**, asked only on an open set. -/
theorem contDiffAt_dbar_local {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) {v : ℂ → ℂ}
    (hv : ∀ z' ∈ U, ContDiffAt ℝ 2 v z') : ContDiffAt ℝ 1 (dbar v) z := by
  obtain ⟨w, V, hw, hV, hzV, hagree⟩ := exists_globalize (n := 2) (by norm_cast) hU hz hv
  have hev : dbar w =ᶠ[𝓝 z] dbar v := by
    filter_upwards [hV.mem_nhds hzV] with t ht
    exact dbar_congr (by filter_upwards [hV.mem_nhds ht] with r hr using hagree r hr)
  exact (contDiff_one_dbar hw).contDiffAt.congr_of_eventuallyEq hev.symm

/-- **Each of the two operators costs one degree of smoothness**, asked only on an open set. -/
theorem contDiffAt_dz_local {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) {v : ℂ → ℂ}
    (hv : ∀ z' ∈ U, ContDiffAt ℝ 2 v z') : ContDiffAt ℝ 1 (dz v) z := by
  obtain ⟨w, V, hw, hV, hzV, hagree⟩ := exists_globalize (n := 2) (by norm_cast) hU hz hv
  have hev : dz w =ᶠ[𝓝 z] dz v := by
    filter_upwards [hV.mem_nhds hzV] with t ht
    exact dz_congr (by filter_upwards [hV.mem_nhds ht] with r hr using hagree r hr)
  exact (contDiff_one_dz hw).contDiffAt.congr_of_eventuallyEq hev.symm

/-- **The commutator of the Cauchy–Riemann operator with its weighted adjoint**, asked only on an
open set. -/
theorem dbar_deltaOp_sub_local {Φ : ℂ → ℂ} (hΦ : ContDiff ℝ 2 Φ) {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) {v : ℂ → ℂ} (hv : ∀ z' ∈ U, ContDiffAt ℝ 2 v z') :
    dbar (deltaOp Φ v) z - deltaOp Φ (dbar v) z = v z * dbar (dz Φ) z := by
  obtain ⟨w, V, hw, hV, hzV, hagree⟩ := exists_globalize (n := 2) (by norm_cast) hU hz hv
  have hdz : ∀ z' ∈ V, dz w z' = dz v z' := fun z' hz' =>
    dz_congr (by filter_upwards [hV.mem_nhds hz'] with t ht using hagree t ht)
  have hdbar : ∀ z' ∈ V, dbar w z' = dbar v z' := fun z' hz' =>
    dbar_congr (by filter_upwards [hV.mem_nhds hz'] with t ht using hagree t ht)
  have hdelta : ∀ z' ∈ V, deltaOp Φ w z' = deltaOp Φ v z' := fun z' hz' => by
    simp only [deltaOp, hdz z' hz', hagree z' hz']
  have e1 : dbar (deltaOp Φ v) z = dbar (deltaOp Φ w) z :=
    dbar_congr (by filter_upwards [hV.mem_nhds hzV] with t ht using (hdelta t ht).symm)
  have e2 : deltaOp Φ (dbar w) z = deltaOp Φ (dbar v) z := by
    have hev : dbar w =ᶠ[𝓝 z] dbar v := by
      filter_upwards [hV.mem_nhds hzV] with t ht using hdbar t ht
    simp only [deltaOp, dz_congr hev, hdbar z hzV]
  rw [e1, ← e2, dbar_deltaOp_sub hΦ hw, hagree z hzV]

end Rigidity.RET

end
