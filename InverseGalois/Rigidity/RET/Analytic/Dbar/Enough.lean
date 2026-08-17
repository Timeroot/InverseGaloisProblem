/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Cover
import InverseGalois.Rigidity.RET.Analytic.Wall

/-!
# Solving the Cauchy–Riemann equation is enough

The one statement the existence direction of the Riemann existence theorem still asks of the
analysis is that the functions of moderate growth on a covering of a punctured plane see its deck
group.  This page reduces that statement to a single equation: if on every such covering the
Cauchy–Riemann equation `∂u/∂z̄ = g` can be solved, with a solution of moderate growth, for every
continuously differentiable `g` of compact support, then the functions of moderate growth do see
the deck group.

The reduction is the standard one.  A nontrivial deck transformation moves some point `y₀`, and the
projection is injective near `y₀`, so the moved point lies outside the coordinate patch at `y₀`.  A
smooth cut-off of the plane, equal to one at the base point and vanishing off a small disc, pulls
back to a function `χ` on the total space which is one at `y₀` and zero at the moved point — but
which is not holomorphic.  Its Cauchy–Riemann derivative is divisible by the coordinate centred at
the base point, since the cut-off is constant near the centre, so writing `∂χ/∂z̄ = (z - x₀) g` and
solving `∂u/∂z̄ = g` produces the correction `(z - x₀) u`, which vanishes at both points because the
coordinate does.  The difference `χ - (z - x₀) u` is then holomorphic, of moderate growth, one at
`y₀` and zero at the moved point.

## Main definitions

* `Rigidity.RET.DbarSolvable` — the Cauchy–Riemann equation with data of compact support is
  solvable, with a solution of moderate growth, on every covering of a punctured plane.

## Main results

* `Rigidity.RET.exists_cutoff` — a smooth cut-off of the plane whose Cauchy–Riemann derivative is
  divisible by the coordinate centred at its centre.
* `Rigidity.RET.hasEnoughFunctions_of_dbarSolvable` — solving the equation is enough.
-/

open Metric Topology

open scoped ContDiff

noncomputable section

namespace Rigidity.RET

/-! ### The total space of a covering is Hausdorff -/

/-- **The total space of a covering of a Hausdorff space is Hausdorff.**  Two points of one fibre
are separated because the projection is a separated map, and two points of different fibres by the
preimages of neighbourhoods separating their images. -/
theorem t2Space_of_isCoveringMap {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    [T2Space B] {p : X → B} (hp : IsCoveringMap p) : T2Space X := by
  refine ⟨fun x₁ x₂ hne => ?_⟩
  by_cases h : p x₁ = p x₂
  · exact hp.isSeparatedMap x₁ x₂ h hne
  · obtain ⟨t₁, t₂, ho₁, ho₂, hm₁, hm₂, hd⟩ := t2_separation h
    exact ⟨p ⁻¹' t₁, p ⁻¹' t₂, ho₁.preimage hp.continuous, ho₂.preimage hp.continuous, hm₁, hm₂,
      hd.preimage p⟩

/-! ### A cut-off of the plane -/

/-- **A smooth cut-off of the plane**, equal to one at a point and vanishing off a disc around it,
whose Cauchy–Riemann derivative is divisible by the coordinate centred at that point.

The quotient `γ` is again continuously differentiable: away from the centre because the coordinate
does not vanish, and at the centre because the cut-off is constant there, so the numerator vanishes
on a whole neighbourhood. -/
theorem exists_cutoff (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (r : ℝ) (β γ : ℂ → ℂ), 0 < r ∧ r < ρ ∧ (∀ z, ‖β z‖ ≤ 1) ∧ β c = 1 ∧
      (∀ z, r ≤ dist z c → β z = 0) ∧ (∀ z, r ≤ dist z c → γ z = 0) ∧
      (∀ z, DifferentiableAt ℝ β z) ∧ (∀ z, ContDiffAt ℝ 1 γ z) ∧
      (∀ z, dbar β z = (z - c) * γ z) := by
  set b : ContDiffBump c :=
    ⟨ρ / 8, ρ / 4, by positivity, by linarith⟩ with hb
  set β : ℂ → ℂ := fun z => ((b z : ℝ) : ℂ) with hβdef
  set γ : ℂ → ℂ := fun z => dbar β z * (z - c)⁻¹ with hγdef
  have hbsmooth : ContDiff ℝ ∞ β := Complex.ofRealCLM.contDiff.comp b.contDiff
  -- the cut-off is one on a disc around the centre, so its derivative vanishes there
  have hone : ∀ z ∈ ball c (ρ / 8), β z = 1 := fun z hz => by
    rw [hβdef]
    simp [b.one_of_mem_closedBall (ball_subset_closedBall hz)]
  have hdbar_in : ∀ z ∈ ball c (ρ / 8), dbar β z = 0 := by
    intro z hz
    have hev : β =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hone w hw
    rw [dbar_congr hev]
    exact dbar_eq_zero (differentiableAt_const 1)
  -- and it vanishes, together with its derivative, outside a slightly larger disc
  have hzero : ∀ z, ρ / 4 ≤ dist z c → β z = 0 := fun z hz => by
    rw [hβdef]
    simp [b.zero_of_le_dist hz]
  have hdbar_out : ∀ z, ρ / 4 < dist z c → dbar β z = 0 := by
    intro z hz
    have hev : β =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      have hopen : IsOpen {w : ℂ | ρ / 4 < dist w c} := isOpen_lt continuous_const
        (continuous_id.dist continuous_const)
      filter_upwards [hopen.mem_nhds hz] with w hw using hzero w (le_of_lt hw)
    rw [dbar_congr hev]
    exact dbar_eq_zero (differentiableAt_const 0)
  refine ⟨ρ / 2, β, γ, by positivity, by linarith, fun z => ?_, ?_, fun z hz => ?_,
    fun z hz => ?_, fun z => (hbsmooth.differentiable (by simp)) z, fun z => ?_, fun z => ?_⟩
  · rw [hβdef]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    exact b.le_one
  · exact hone c (mem_ball_self (by positivity))
  · exact hzero z (by linarith)
  · rw [hγdef]
    simp only
    rw [hdbar_out z (by linarith), zero_mul]
  · -- continuous differentiability of the quotient
    by_cases hzc : z = c
    · subst hzc
      have hev : γ =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by positivity : (0:ℝ) < ρ / 8))]
          with w hw
        rw [hγdef]
        simp [hdbar_in w hw]
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
    · have h1 : ContDiffAt ℝ 1 (fun w => dbar β w) z :=
        ((contDiff_dbar hbsmooth).contDiffAt).of_le (by simp)
      have h2 : ContDiffAt ℝ 1 (fun w : ℂ => (w - c)⁻¹) z :=
        ((contDiff_id.sub contDiff_const).contDiffAt).inv (sub_ne_zero.2 hzc)
      exact h1.mul h2
  · -- the divisibility
    by_cases hzc : z = c
    · subst hzc
      rw [hdbar_in z (mem_ball_self (by positivity)), sub_self, zero_mul]
    · rw [hγdef]
      simp only
      rw [← mul_assoc, mul_comm (z - c) (dbar β z), mul_assoc,
        mul_inv_cancel₀ (sub_ne_zero.2 hzc), mul_one]

/-! ### The reduction -/

/-- **The Cauchy–Riemann equation is solvable on every covering of a punctured plane**: for data
that is continuously differentiable and of compact support there is a solution of moderate
growth. -/
def DbarSolvable : Prop :=
  ∀ (S : Finset ℂ) (Y : Type) [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y]
    (q : Y → ↥((S : Set ℂ)ᶜ)), IsCoveringMap q →
      ∀ g : Y → ℂ, (∀ y, IsC1At (fun y => ((q y : ℂ))) g y) →
        (∃ K : Set Y, IsCompact K ∧ ∀ y ∉ K, g y = 0) →
        ∃ u : Y → ℂ, (∀ y, IsDbarAt (fun y => ((q y : ℂ))) u (g y) y) ∧
          IsModerate (fun y => ((q y : ℂ))) S u

/-- **Solving the Cauchy–Riemann equation on coverings is enough** for the functions of moderate
growth to see the deck group, and so for the existence direction of the Riemann existence
theorem. -/
theorem hasEnoughFunctions_of_dbarSolvable (hsolve : DbarSolvable) : HasEnoughFunctions := by
  intro S Y _ _ _ q hq hf hrange H _ _ _ _ _ _ htrans a ha
  classical
  set π : Y → ℂ := fun y => ((q y : ℂ)) with hπdef
  haveI : T2Space Y := t2Space_of_isCoveringMap hq
  -- a nontrivial deck transformation moves a point
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Y, a • y₀ ≠ y₀ := by
    by_contra hcon
    push_neg at hcon
    exact ha (eq_of_smul_eq_smul (α := Y) fun m => by rw [hcon m, one_smul])
  have hπeq : π (a • y₀) = π y₀ := IsOverBase.smul_eq a y₀
  -- a coordinate at the moved point, which the image of the point misses
  obtain ⟨e, hy₀e, hfe⟩ := hf y₀
  have he : IsChartAt π e y₀ := ⟨hy₀e, hfe⟩
  have hy₁src : a • y₀ ∉ e.source := by
    intro hmem
    refine hy₀ (e.injOn hmem hy₀e ?_)
    rw [← congrFun hfe (a • y₀), ← congrFun hfe y₀]
    exact hπeq
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 e.open_target (π y₀) he.mem_target
  obtain ⟨r, β, γ, hr, hrρ, hβ1, hβc, hβ0, hγ0, hβd, hγC1, hkey⟩ := exists_cutoff (π y₀) hρ
  -- the patch the cut-off lives on
  have hsub : closedBall (π y₀) r ⊆ e.target :=
    (closedBall_subset_ball hrρ).trans hball
  set K : Set Y := e.symm '' (closedBall (π y₀) r) with hK
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (π y₀) r).image_of_continuousOn (e.continuousOn_symm.mono hsub)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hKsub : K ⊆ e.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_target (hsub hz)
  -- the cut-off and the datum of the equation, transplanted to the total space
  set χ : Y → ℂ := fun y => if y ∈ e.source then β (π y) else 0 with hχdef
  set g : Y → ℂ := fun y => if y ∈ e.source then γ (π y) else 0 with hgdef
  have hvanish : ∀ y ∉ K, χ y = 0 ∧ g y = 0 := by
    intro y hy
    by_cases hs : y ∈ e.source
    · have hdist : r ≤ dist (π y) (π y₀) := by
        by_contra hlt
        push_neg at hlt
        refine hy ⟨π y, mem_closedBall.2 (le_of_lt hlt), ?_⟩
        rw [congrFun hfe y]
        exact e.left_inv hs
      refine ⟨?_, ?_⟩
      · simp only [hχdef, if_pos hs, hβ0 _ hdist]
      · simp only [hgdef, if_pos hs, hγ0 _ hdist]
    · refine ⟨?_, ?_⟩
      · simp only [hχdef, if_neg hs]
      · simp only [hgdef, if_neg hs]
  have hlocχ : ∀ y ∈ e.source, ∀ᶠ y' in 𝓝 y, β (π y') = χ y' := by
    intro y hy
    filter_upwards [e.open_source.mem_nhds hy] with y' h
    simp only [hχdef, if_pos h]
  have hlocg : ∀ y ∈ e.source, ∀ᶠ y' in 𝓝 y, γ (π y') = g y' := by
    intro y hy
    filter_upwards [e.open_source.mem_nhds hy] with y' h
    simp only [hgdef, if_pos h]
  have hout : ∀ y ∉ e.source, ∀ᶠ y' in 𝓝 y, (0 : ℂ) = χ y' ∧ (0 : ℂ) = g y' := by
    intro y hy
    have hyK : y ∉ K := fun h => hy (hKsub h)
    filter_upwards [hKclosed.isOpen_compl.mem_nhds hyK] with y' h
    exact ⟨((hvanish y' h).1).symm, ((hvanish y' h).2).symm⟩
  -- the datum is continuously differentiable and of compact support
  have hgC1 : ∀ y, IsC1At π g y := by
    intro y
    by_cases hy : y ∈ e.source
    · exact (isC1At_comp hf (hγC1 (π y))).congr (hlocg y hy)
    · exact (isC1At_comp hf (contDiffAt_const (c := (0 : ℂ)))).congr
        ((hout y hy).mono fun y' h => h.2)
  have hgsupp : ∃ K : Set Y, IsCompact K ∧ ∀ y ∉ K, g y = 0 :=
    ⟨K, hKcompact, fun y hy => (hvanish y hy).2⟩
  -- the Cauchy–Riemann derivative of the cut-off is divisible by the coordinate
  have hχdbar : ∀ y, IsDbarAt π χ ((π y - π y₀) * g y) y := by
    intro y
    by_cases hy : y ∈ e.source
    · have hgy : g y = γ (π y) := by simp only [hgdef, if_pos hy]
      rw [hgy, ← hkey (π y)]
      exact (isDbarAt_comp (y := y) hf (hβd (π y))).congr (hlocχ y hy)
    · have hgy : g y = 0 := (hvanish y (fun h => hy (hKsub h))).2
      rw [hgy, mul_zero]
      exact (isDbarAt_comp_zero (y := y) hf (differentiableAt_const (0 : ℂ))).congr
        ((hout y hy).mono fun y' h => h.1)
  -- solve, and correct
  obtain ⟨u, hu, hmodu⟩ := hsolve S Y q hq g hgC1 hgsupp
  refine ⟨fun y => χ y - (π y - π y₀) * u y, mem_coverRing.2 ⟨?_, ?_⟩, y₀, ?_⟩
  · refine isHolo_of_isDbarAt_zero hf fun y => ?_
    have h1 : IsDbarAt π (fun y' => π y' - π y₀) 0 y :=
      isDbarAt_comp_zero (y := y) hf (β := fun z => z - π y₀)
        (differentiableAt_id.sub (differentiableAt_const _))
    have h2 := (hχdbar y).sub (h1.mul (hu y))
    have hval : (π y - π y₀) * g y - ((π y - π y₀) * g y + u y * 0) = 0 := by ring
    rwa [hval] at h2
  · have hbound : ∀ y, ‖χ y‖ ≤ 1 := by
      intro y
      by_cases hy : y ∈ e.source
      · simpa only [hχdef, if_pos hy] using hβ1 (π y)
      · simp only [hχdef, if_neg hy, norm_zero]
        exact zero_le_one
    have hmodχ : IsModerate π S χ :=
      { punct := fun s _ => ⟨1, one_pos, 1, zero_le_one, 0, fun y _ => by
          simpa using hbound y⟩
        infty := ⟨1, 1, 0, zero_le_one, fun y _ => by simpa using hbound y⟩ }
    have hmodp : IsModerate π S (fun y => π y - π y₀) := by
      have h := isModerate_polynomial π S (Polynomial.X - Polynomial.C (π y₀))
      have hfun : (fun y => Polynomial.eval (π y) (Polynomial.X - Polynomial.C (π y₀)))
          = fun y => π y - π y₀ := by
        funext y
        simp
      rwa [hfun] at h
    exact hmodχ.sub (hmodp.mul hmodu)
  · have h₀ : χ y₀ = 1 := by simp only [hχdef, if_pos hy₀e, hβc]
    have h₁ : χ (a • y₀) = 0 := by simp only [hχdef, if_neg hy₁src]
    show χ (a • y₀) - (π (a • y₀) - π y₀) * u (a • y₀) ≠ χ y₀ - (π y₀ - π y₀) * u y₀
    rw [h₀, h₁, hπeq]
    simp

end Rigidity.RET

end
