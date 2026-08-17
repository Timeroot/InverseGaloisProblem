/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Cover

/-!
# Summing a function along the fibres of a covering

A covering of a plane domain with finite fibres carries no canonical measure of its own, but a
function on the total space can always be pushed down to the base by summing it over each fibre.
Over an evenly covered neighbourhood the fibre sum is a finite sum of the function along local
sections of the projection, so it inherits from the function whatever local property the sections
transport — continuity here, and later differentiability.  Integrating the fibre sum over the base
is then a substitute for integrating the function over the total space.

## Main definitions

* `Rigidity.RET.fibreSum` — the sum of a function over the fibre of the projection.

## Main results

* `Rigidity.RET.exists_sections` — an evenly covered neighbourhood carries a family of local
  sections whose values at each point exhaust the fibre exactly once.
* `Rigidity.RET.fibreSum_eq_finsum` — over such a neighbourhood the fibre sum is the finite sum
  along the sections.
* `Rigidity.RET.fibreSum_add`, `Rigidity.RET.map_fibreSum`, `Rigidity.RET.fibreSum_mul_comp` — the
  fibre sum is additive, commutes with an additive map, and absorbs a factor pulled back from the
  base.
* `Rigidity.RET.continuous_fibreSum`, `Rigidity.RET.hasCompactSupport_fibreSum` — the fibre sum of
  a continuous compactly supported function is continuous and compactly supported.
* `Rigidity.RET.fibreSum_mono` — the fibre sum is monotone.
* `Rigidity.RET.dbar_fibreSum` — the Cauchy–Riemann operator commutes with the fibre sum.
-/

open Topology

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {z₀ : ℂ}

/-! ### Local sections -/

/-- **An evenly covered point has a neighbourhood carrying local sections of the projection whose
values exhaust each fibre exactly once.** -/
theorem exists_sections (h : IsEvenlyCovered f z₀ (f ⁻¹' {z₀})) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ s : ↥(f ⁻¹' {z₀}) → ℂ → Y,
      (∀ i, ContinuousOn (s i) U) ∧ (∀ i, ∀ z ∈ U, f (s i z) = z) ∧
      (∀ z ∈ U, ∀ y, f y = z → ∃ i, s i z = y) ∧
      (∀ z ∈ U, Function.Injective fun i => s i z) := by
  classical
  obtain ⟨-, U, hz₀U, hU, hfU, H, hH⟩ := h
  refine ⟨U, hU, hz₀U, fun i z => if hz : z ∈ U then ((H.symm (⟨z, hz⟩, i) : ↥(f ⁻¹' U)) : Y)
    else (i : Y), ?_, ?_, ?_, ?_⟩
  · -- continuity along a section
    intro i
    rw [continuousOn_iff_continuous_restrict]
    have hres : (U.restrict fun z => if hz : z ∈ U then ((H.symm (⟨z, hz⟩, i) : ↥(f ⁻¹' U)) : Y)
        else (i : Y)) = fun u : ↥U => ((H.symm (u, i) : ↥(f ⁻¹' U)) : Y) := by
      funext u
      simp only [Set.restrict_apply, dif_pos u.2]
    rw [hres]
    fun_prop
  · -- a section is a section
    intro i z hz
    have := hH (H.symm (⟨z, hz⟩, i))
    simpa [dif_pos hz] using this.symm
  · -- the sections exhaust the fibre
    intro z hz y hy
    have hyU : y ∈ f ⁻¹' U := by
      rw [Set.mem_preimage, hy]
      exact hz
    refine ⟨(H ⟨y, hyU⟩).2, ?_⟩
    have hfst : (H ⟨y, hyU⟩).1 = (⟨z, hz⟩ : ↥U) := by
      apply Subtype.ext
      rw [hH ⟨y, hyU⟩, hy]
    simp only [dif_pos hz]
    rw [← hfst, Prod.mk.eta, Homeomorph.symm_apply_apply]
  · -- and do so exactly once
    intro z hz i j hij
    simp only [dif_pos hz] at hij
    have h1 : (H.symm (⟨z, hz⟩, i) : ↥(f ⁻¹' U)) = H.symm (⟨z, hz⟩, j) := Subtype.ext hij
    have h2 := H.symm.injective h1
    exact (Prod.ext_iff.1 h2).2

/-! ### The fibre sum -/

section Algebra

variable {M : Type*} [AddCommMonoid M] {F : Y → M}

/-- **The fibre sum** of a function on the total space: its sum over the fibre of the projection. -/
def fibreSum (f : Y → ℂ) (F : Y → M) (z : ℂ) : M := ∑ᶠ y ∈ f ⁻¹' {z}, F y

omit [TopologicalSpace Y] in
/-- A function vanishing along a fibre has fibre sum zero there. -/
theorem fibreSum_eq_zero (h : ∀ y, f y = z₀ → F y = 0) : fibreSum f F z₀ = 0 :=
  finsum_mem_of_eqOn_zero fun y hy => h y (Set.mem_singleton_iff.mp hy)

omit [TopologicalSpace Y] in
/-- The fibre sum vanishes off the range of the projection. -/
theorem fibreSum_of_notMem_range (hz : z₀ ∉ Set.range f) : fibreSum f F z₀ = 0 :=
  fibreSum_eq_zero fun y hy => absurd ⟨y, hy⟩ hz

omit [TopologicalSpace Y] in
/-- **The fibre sum is additive.** -/
theorem fibreSum_add (hfin : (f ⁻¹' {z₀}).Finite) (F G : Y → M) :
    fibreSum f (fun y => F y + G y) z₀ = fibreSum f F z₀ + fibreSum f G z₀ :=
  finsum_mem_add_distrib hfin

omit [TopologicalSpace Y] in
/-- **The fibre sum commutes with an additive map.** -/
theorem map_fibreSum {N : Type*} [AddCommMonoid N] (φ : M →+ N) (F : Y → M)
    (hfin : (f ⁻¹' {z₀}).Finite) :
    φ (fibreSum f F z₀) = fibreSum f (fun y => φ (F y)) z₀ :=
  φ.map_finsum_mem F hfin

omit [TopologicalSpace Y] in
/-- **A constant factor comes out of the fibre sum.** -/
theorem fibreSum_const_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (c : R)
    (F : Y → R) : fibreSum f (fun y => c * F y) z₀ = c * fibreSum f F z₀ :=
  (mul_finsum_mem F c).symm

omit [TopologicalSpace Y] in
/-- The fibre sum is supported over the image of the support. -/
theorem support_fibreSum_subset (f : Y → ℂ) (F : Y → M) :
    Function.support (fibreSum f F) ⊆ f '' Function.support F := by
  intro z hz
  by_contra hno
  exact hz (fibreSum_eq_zero fun y hy => by
    by_contra hFy
    exact hno ⟨y, hFy, hy⟩)

/-- **The fibre sum of a compactly supported function is compactly supported.** -/
theorem hasCompactSupport_fibreSum (hf : Continuous f) (hF : HasCompactSupport F) :
    HasCompactSupport (fibreSum f F) := by
  have hK : IsCompact (f '' tsupport F) := hF.image hf
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  exact (support_fibreSum_subset f F).trans (Set.image_mono subset_closure)

omit [TopologicalSpace Y] in
/-- **Over an evenly covered neighbourhood the fibre sum is the finite sum along the sections.** -/
theorem fibreSum_eq_finsum {U : Set ℂ} {s : ↥(f ⁻¹' {z₀}) → ℂ → Y}
    (hproj : ∀ i, ∀ z ∈ U, f (s i z) = z)
    (hsurj : ∀ z ∈ U, ∀ y, f y = z → ∃ i, s i z = y)
    (hinj : ∀ z ∈ U, Function.Injective fun i => s i z) (F : Y → M) {z : ℂ} (hz : z ∈ U) :
    fibreSum f F z = ∑ᶠ i : ↥(f ⁻¹' {z₀}), F (s i z) := by
  have hrange : f ⁻¹' {z} = Set.range fun i => s i z := by
    ext y
    constructor
    · intro hy
      exact hsurj z hz y hy
    · rintro ⟨i, rfl⟩
      exact hproj i z hz
  rw [fibreSum, hrange, finsum_mem_range (hinj z hz)]

end Algebra

/-! ### Order -/

omit [TopologicalSpace Y] in
/-- The fibre sum of a nonnegative function is nonnegative. -/
theorem fibreSum_nonneg {F : Y → ℝ} (hF : ∀ y, 0 ≤ F y) (z : ℂ) : 0 ≤ fibreSum f F z :=
  finsum_nonneg fun y => finsum_nonneg fun _ => hF y

omit [TopologicalSpace Y] in
/-- **The fibre sum is monotone.** -/
theorem fibreSum_mono (hfin : (f ⁻¹' {z₀}).Finite) {F G : Y → ℝ} (h : ∀ y, F y ≤ G y) :
    fibreSum f F z₀ ≤ fibreSum f G z₀ := by
  have h1 : fibreSum f G z₀ = fibreSum f F z₀ + fibreSum f (fun y => G y - F y) z₀ := by
    rw [← fibreSum_add hfin]
    simp
  have h2 : 0 ≤ fibreSum f (fun y => G y - F y) z₀ :=
    fibreSum_nonneg (fun y => sub_nonneg.2 (h y)) z₀
  linarith

/-! ### Continuity -/

section Continuity

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M] {F : Y → M}

/-- **The fibre sum of a continuous function is continuous** over an evenly covered
neighbourhood. -/
theorem continuousOn_fibreSum [Finite ↥(f ⁻¹' {z₀})] {U : Set ℂ} {s : ↥(f ⁻¹' {z₀}) → ℂ → Y}
    (hcont : ∀ i, ContinuousOn (s i) U) (hproj : ∀ i, ∀ z ∈ U, f (s i z) = z)
    (hsurj : ∀ z ∈ U, ∀ y, f y = z → ∃ i, s i z = y)
    (hinj : ∀ z ∈ U, Function.Injective fun i => s i z) (hF : Continuous F) :
    ContinuousOn (fibreSum f F) U := by
  classical
  haveI : Fintype ↥(f ⁻¹' {z₀}) := Fintype.ofFinite _
  refine ContinuousOn.congr (f := fun z => ∑ i : ↥(f ⁻¹' {z₀}), F (s i z)) ?_ ?_
  · exact continuousOn_finset_sum _ fun i _ => hF.comp_continuousOn (hcont i)
  · intro z hz
    rw [fibreSum_eq_finsum hproj hsurj hinj F hz, finsum_eq_sum_of_fintype]

omit [TopologicalSpace M] [ContinuousAdd M] in
/-- Away from the image of the support the fibre sum vanishes on a whole neighbourhood. -/
theorem eventuallyEq_zero_fibreSum (hf : Continuous f) (hF : HasCompactSupport F) {z : ℂ}
    (hz : z ∉ f '' tsupport F) : (fun _ : ℂ => (0 : M)) =ᶠ[𝓝 z] fibreSum f F := by
  have hcl : IsClosed (f '' tsupport F) := (hF.image hf).isClosed
  filter_upwards [hcl.isOpen_compl.mem_nhds hz] with w hw
  refine (fibreSum_eq_zero fun y hy => ?_).symm
  exact image_eq_zero_of_notMem_tsupport fun hmem => hw ⟨y, hmem, hy⟩

/-- **The fibre sum of a continuous compactly supported function is continuous.** -/
theorem continuous_fibreSum (hfin : ∀ z, (f ⁻¹' {z}).Finite)
    (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)
    (hFc : Continuous F) (hFs : HasCompactSupport F) : Continuous (fibreSum f F) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ f '' tsupport F
  · obtain ⟨y, -, rfl⟩ := hz
    haveI := (hfin (f y)).to_subtype
    obtain ⟨U, hU, hmem, s, hcont, hproj, hsurj, hinj⟩ := exists_sections (hcov (f y) ⟨y, rfl⟩)
    exact (continuousOn_fibreSum hcont hproj hsurj hinj hFc).continuousAt (hU.mem_nhds hmem)
  · exact continuousAt_const.congr (eventuallyEq_zero_fibreSum hf hFs hz)

end Continuity

/-! ### A section is a local coordinate -/

variable {F : Y → ℂ} {σ : ℂ → Y} {U : Set ℂ} {z₁ : ℂ}

/-- **A continuous section of the projection is the inverse of a local coordinate.**  Both invert
the projection near the point, so they agree there. -/
theorem eventuallyEq_section_symm (hU : U ∈ 𝓝 z₁) (hc : ContinuousOn σ U)
    (hproj : ∀ z ∈ U, f (σ z) = z) {e : OpenPartialHomeomorph Y ℂ}
    (he : IsChartAt f e (σ z₁)) : σ =ᶠ[𝓝 z₁] ⇑e.symm := by
  have hca : ContinuousAt σ z₁ := hc.continuousAt hU
  have hpre : ∀ᶠ z in 𝓝 z₁, σ z ∈ e.source :=
    hca.preimage_mem_nhds (e.open_source.mem_nhds he.1)
  filter_upwards [hpre, hU] with z hz1 hz2
  have hval : e (σ z) = z := by rw [← congrFun he.2]; exact hproj z hz2
  exact (e.left_inv hz1).symm.trans (congrArg (⇑e.symm) hval)

/-- **The Cauchy–Riemann operator on the total space is read along a section** as the operator of
the composite. -/
theorem dbar_comp_section {c : ℂ} (hdb : IsDbarAt f F c (σ z₁)) (hU : U ∈ 𝓝 z₁)
    (hc : ContinuousOn σ U) (hproj : ∀ z ∈ U, f (σ z) = z) :
    DifferentiableAt ℝ (fun z => F (σ z)) z₁ ∧ dbar (fun z => F (σ z)) z₁ = c := by
  obtain ⟨e, he, hdiff, hval⟩ := hdb
  have hfz : f (σ z₁) = z₁ := hproj z₁ (mem_of_mem_nhds hU)
  rw [hfz] at hdiff hval
  have hev : (fun z => F (σ z)) =ᶠ[𝓝 z₁] fun w => F (e.symm w) :=
    (eventuallyEq_section_symm hU hc hproj he).fun_comp F
  exact ⟨hev.differentiableAt_iff.2 hdiff, by rw [dbar_congr hev, hval]⟩

/-- **Continuous differentiability on the total space is read along a section** as that of the
composite. -/
theorem contDiffAt_comp_section (hC1 : IsC1At f F (σ z₁)) (hU : U ∈ 𝓝 z₁)
    (hc : ContinuousOn σ U) (hproj : ∀ z ∈ U, f (σ z) = z) :
    ContDiffAt ℝ 1 (fun z => F (σ z)) z₁ := by
  obtain ⟨e, he, hdiff⟩ := hC1
  have hfz : f (σ z₁) = z₁ := hproj z₁ (mem_of_mem_nhds hU)
  rw [hfz] at hdiff
  exact hdiff.congr_of_eventuallyEq ((eventuallyEq_section_symm hU hc hproj he).fun_comp F)

/-! ### Differentiating the fibre sum -/

/-- The Cauchy–Riemann operator is additive over a finite sum. -/
theorem dbar_finset_sum {ι : Type*} (t : Finset ι) {u : ι → ℂ → ℂ} {z : ℂ}
    (h : ∀ i ∈ t, DifferentiableAt ℝ (u i) z) :
    dbar (fun w => ∑ i ∈ t, u i w) z = ∑ i ∈ t, dbar (u i) z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [dbar]
  | @insert a t ha ih =>
    have hsplit : (fun w => ∑ i ∈ insert a t, u i w) = fun w => u a w + ∑ i ∈ t, u i w := by
      funext w
      rw [Finset.sum_insert ha]
    have hda : DifferentiableAt ℝ (u a) z := h a (Finset.mem_insert_self a t)
    have hdt : ∀ i ∈ t, DifferentiableAt ℝ (u i) z := fun i hi =>
      h i (Finset.mem_insert_of_mem hi)
    have hsum : DifferentiableAt ℝ (fun w => ∑ i ∈ t, u i w) z := .fun_sum hdt
    rw [hsplit, Finset.sum_insert ha, dbar_add hda hsum, ih hdt]

omit [TopologicalSpace Y] in
/-- Near a point of an evenly covered neighbourhood the fibre sum is the sum along the sections. -/
theorem fibreSum_eventuallyEq {s : ↥(f ⁻¹' {z₀}) → ℂ → Y} (hproj : ∀ i, ∀ z ∈ U, f (s i z) = z)
    (hsurj : ∀ z ∈ U, ∀ y, f y = z → ∃ i, s i z = y)
    (hinj : ∀ z ∈ U, Function.Injective fun i => s i z) (F : Y → ℂ) (hU : U ∈ 𝓝 z₁) :
    fibreSum f F =ᶠ[𝓝 z₁] fun z => ∑ᶠ i : ↥(f ⁻¹' {z₀}), F (s i z) := by
  filter_upwards [hU] with z hz
  exact fibreSum_eq_finsum hproj hsurj hinj F hz

/-- **The fibre sum of a continuously differentiable function is continuously differentiable.** -/
theorem contDiffAt_fibreSum [Finite ↥(f ⁻¹' {z₀})] {s : ↥(f ⁻¹' {z₀}) → ℂ → Y}
    (hcont : ∀ i, ContinuousOn (s i) U) (hproj : ∀ i, ∀ z ∈ U, f (s i z) = z)
    (hsurj : ∀ z ∈ U, ∀ y, f y = z → ∃ i, s i z = y)
    (hinj : ∀ z ∈ U, Function.Injective fun i => s i z) (hC1 : ∀ y, IsC1At f F y)
    (hU : U ∈ 𝓝 z₁) : ContDiffAt ℝ 1 (fibreSum f F) z₁ := by
  classical
  haveI : Fintype ↥(f ⁻¹' {z₀}) := Fintype.ofFinite _
  have hterm : ∀ i, ContDiffAt ℝ 1 (fun z => F (s i z)) z₁ := fun i =>
    contDiffAt_comp_section (hC1 (s i z₁)) hU (hcont i) (hproj i)
  have hsum : ContDiffAt ℝ 1 (fun z => ∑ᶠ i : ↥(f ⁻¹' {z₀}), F (s i z)) z₁ := by
    have hcast : (fun z => ∑ᶠ i : ↥(f ⁻¹' {z₀}), F (s i z))
        = fun z => ∑ i : ↥(f ⁻¹' {z₀}), F (s i z) := by
      funext z
      exact finsum_eq_sum_of_fintype _
    rw [hcast]
    exact ContDiffAt.sum fun i _ => hterm i
  exact hsum.congr_of_eventuallyEq (fibreSum_eventuallyEq hproj hsurj hinj F hU)

/-- **The Cauchy–Riemann operator commutes with the fibre sum.**  The sections of the projection
are local coordinates, so differentiating the sum along them differentiates each term where it
sits on the total space. -/
theorem dbar_fibreSum [Finite ↥(f ⁻¹' {z₀})] {s : ↥(f ⁻¹' {z₀}) → ℂ → Y} {G : Y → ℂ}
    (hcont : ∀ i, ContinuousOn (s i) U) (hproj : ∀ i, ∀ z ∈ U, f (s i z) = z)
    (hsurj : ∀ z ∈ U, ∀ y, f y = z → ∃ i, s i z = y)
    (hinj : ∀ z ∈ U, Function.Injective fun i => s i z) (hdb : ∀ y, IsDbarAt f F (G y) y)
    (hU : U ∈ 𝓝 z₁) :
    DifferentiableAt ℝ (fibreSum f F) z₁ ∧ dbar (fibreSum f F) z₁ = fibreSum f G z₁ := by
  classical
  haveI : Fintype ↥(f ⁻¹' {z₀}) := Fintype.ofFinite _
  have hterm : ∀ i, DifferentiableAt ℝ (fun z => F (s i z)) z₁ ∧
      dbar (fun z => F (s i z)) z₁ = G (s i z₁) := fun i =>
    dbar_comp_section (hdb (s i z₁)) hU (hcont i) (hproj i)
  have hev := fibreSum_eventuallyEq hproj hsurj hinj F hU
  have hcast : (fun z => ∑ᶠ i : ↥(f ⁻¹' {z₀}), F (s i z))
      = fun z => ∑ i : ↥(f ⁻¹' {z₀}), F (s i z) := by
    funext z
    exact finsum_eq_sum_of_fintype _
  rw [hcast] at hev
  have hdiff : DifferentiableAt ℝ (fun z => ∑ i : ↥(f ⁻¹' {z₀}), F (s i z)) z₁ :=
    .fun_sum fun i _ => (hterm i).1
  refine ⟨hev.differentiableAt_iff.2 hdiff, ?_⟩
  rw [dbar_congr hev, dbar_finset_sum _ fun i _ => (hterm i).1,
    fibreSum_eq_finsum hproj hsurj hinj G (mem_of_mem_nhds hU), finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ => (hterm i).2

omit [TopologicalSpace Y] in
/-- **A factor pulled back from the base comes out of the fibre sum.** -/
theorem fibreSum_mul_comp (F : Y → ℂ) (h : ℂ → ℂ) :
    fibreSum f (fun y => F y * h (f y)) z₀ = fibreSum f F z₀ * h z₀ := by
  rw [fibreSum, fibreSum, finsum_mem_mul]
  exact finsum_mem_congr rfl fun y hy => by rw [Set.mem_singleton_iff.mp hy]

end Rigidity.RET

end
