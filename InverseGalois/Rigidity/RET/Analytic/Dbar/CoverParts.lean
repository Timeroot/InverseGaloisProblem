/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.FibreSum
import InverseGalois.Rigidity.RET.Analytic.Dbar.Parts

/-!
# Integration by parts on the total space of a covering

The fibre sum turns a compactly supported function on the total space of a covering of the plane
into a compactly supported function on the plane, and it commutes with the Cauchy–Riemann
operator.  Combining the two facts with the vanishing of the plane integral of `∂F/∂z̄` gives the
integration-by-parts identity that the `L²` theory on a covering rests on: the fibre-sum integral
of `∂u/∂z̄` vanishes for every compactly supported continuously differentiable `u`.

## Main results

* `Rigidity.RET.contDiff_fibreSum` — the fibre sum of a continuously differentiable function of
  compact support is continuously differentiable.
* `Rigidity.RET.dbar_fibreSum_eq` — the derivative of the fibre sum is the fibre sum of the
  derivative, at every point of the plane.
* `Rigidity.RET.integral_fibreSum_dbar` — the fibre-sum integral of a derivative vanishes.
-/

open Topology MeasureTheory

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ}

/-! ### Vanishing off the support -/

/-- A function vanishing near a point of the total space is killed there by the operator. -/
theorem isDbarAt_zero_of_eventuallyEq_zero (hlh : IsLocalHomeomorph f) {u : Y → ℂ} {y : Y}
    (hu : ∀ᶠ y' in 𝓝 y, u y' = 0) : IsDbarAt f u 0 y := by
  have h0 : IsDbarAt f (fun _ : Y => (0 : ℂ)) 0 y :=
    isDbarAt_comp_zero hlh (β := fun _ : ℂ => (0 : ℂ)) (differentiableAt_const 0)
  exact h0.congr (by filter_upwards [hu] with y' hy' using hy'.symm)

/-- **The derivative of a compactly supported function vanishes off its support.** -/
theorem eq_zero_of_notMem_tsupport (hlh : IsLocalHomeomorph f) {F G : Y → ℂ} {y : Y}
    (hdb : IsDbarAt f F (G y) y) (hy : y ∉ tsupport F) : G y = 0 := by
  have hev : ∀ᶠ y' in 𝓝 y, F y' = 0 := by
    filter_upwards [(isClosed_tsupport F).isOpen_compl.mem_nhds hy] with y' hy'
    exact image_eq_zero_of_notMem_tsupport hy'
  exact hdb.eq (isDbarAt_zero_of_eventuallyEq_zero hlh hev)

/-! ### The fibre sum of a differentiable function -/

section Integral

variable (hfin : ∀ z, (f ⁻¹' {z}).Finite)
  (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)

include hfin hcov hf in
/-- **The fibre sum of a continuously differentiable function of compact support is continuously
differentiable.** -/
theorem contDiff_fibreSum {F : Y → ℂ} (hC1 : ∀ y, IsC1At f F y) (hFs : HasCompactSupport F) :
    ContDiff ℝ 1 (fibreSum f F) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ f '' tsupport F
  · obtain ⟨y, -, rfl⟩ := hz
    haveI := (hfin (f y)).to_subtype
    obtain ⟨U, hU, hmem, s, hcont, hproj, hsurj, hinj⟩ := exists_sections (hcov (f y) ⟨y, rfl⟩)
    exact contDiffAt_fibreSum hcont hproj hsurj hinj hC1 (hU.mem_nhds hmem)
  · exact contDiffAt_const.congr_of_eventuallyEq (eventuallyEq_zero_fibreSum hf hFs hz).symm

include hfin hcov hf in
/-- **The operator commutes with the fibre sum**, at every point of the plane. -/
theorem dbar_fibreSum_eq (hlh : IsLocalHomeomorph f) {F G : Y → ℂ}
    (hdb : ∀ y, IsDbarAt f F (G y) y) (hFs : HasCompactSupport F) (z : ℂ) :
    dbar (fibreSum f F) z = fibreSum f G z := by
  by_cases hz : z ∈ f '' tsupport F
  · obtain ⟨y, -, rfl⟩ := hz
    haveI := (hfin (f y)).to_subtype
    obtain ⟨U, hU, hmem, s, hcont, hproj, hsurj, hinj⟩ := exists_sections (hcov (f y) ⟨y, rfl⟩)
    exact (dbar_fibreSum hcont hproj hsurj hinj hdb (hU.mem_nhds hmem)).2
  · have h1 : dbar (fibreSum f F) z = 0 := by
      rw [dbar_congr (eventuallyEq_zero_fibreSum hf hFs hz).symm]
      simp [dbar]
    rw [h1]
    exact (fibreSum_eq_zero fun y hy => eq_zero_of_notMem_tsupport hlh (hdb y)
      fun hmem => hz ⟨y, hmem, hy⟩).symm

include hfin hcov hf in
/-- **Integration by parts on a covering**: the fibre-sum integral of a derivative vanishes. -/
theorem integral_fibreSum_dbar (hlh : IsLocalHomeomorph f) {F G : Y → ℂ}
    (hC1 : ∀ y, IsC1At f F y) (hdb : ∀ y, IsDbarAt f F (G y) y) (hFs : HasCompactSupport F) :
    ∫ z : ℂ, fibreSum f G z = 0 := by
  have heq : ∀ z : ℂ, fibreSum f G z = dbar (fibreSum f F) z := fun z =>
    (dbar_fibreSum_eq hfin hcov hf hlh hdb hFs z).symm
  simp only [heq]
  exact integral_dbar_eq_zero (contDiff_fibreSum hfin hcov hf hC1 hFs)
    (hasCompactSupport_fibreSum hf hFs)

end Integral

end Rigidity.RET

end
