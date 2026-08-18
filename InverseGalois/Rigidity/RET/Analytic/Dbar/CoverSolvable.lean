/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverModerate
import InverseGalois.Rigidity.RET.Analytic.Dbar.Enough
import InverseGalois.Rigidity.RET.Analytic.Algebraicity

/-!
# The Cauchy–Riemann equation is solvable on a covering

All the pieces of the `L²` method are in place: a covering of a punctured plane carries a measure,
the Cauchy–Riemann operator on it satisfies an a priori estimate driven by the curvature of a
weight, the estimate produces a weak solution of the equation, regularity turns the weak solution
into a genuine one, and the norm of the weak solution bounds the genuine one on every disc over
which it is holomorphic.  Taking for the weight the logarithm of `1 + |z|²`, whose curvature is
positive and whose size is polynomial, the bound on discs becomes the growth condition.

## Main results

* `Rigidity.RET.dbarSolvable` — **the Cauchy–Riemann equation with data of compact support is
  solvable, with a solution of moderate growth, on every covering of a punctured plane.**
* `Rigidity.RET.hasEnoughFunctions` — the functions of moderate growth on a covering of a punctured
  plane see its deck group.
-/

open Metric Topology MeasureTheory

noncomputable section

namespace Rigidity.RET

/-- **The Cauchy–Riemann equation with data of compact support is solvable, with a solution of
moderate growth, on every covering of a punctured plane with finite fibres.** -/
theorem dbarSolvable : DbarSolvable := by
  intro S Y _ _ _ q hq hfin' g hg1 hsupp
  classical
  obtain ⟨Kc, hKc, hgvan⟩ := hsupp
  set f : Y → ℂ := fun y => ((q y : ℂ)) with hfdef
  haveI : T2Space Y := t2Space_of_isCoveringMap hq
  have hlh : IsLocalHomeomorph f := isLocalHomeomorph_val_comp hq
  haveI : WeaklyLocallyCompactSpace Y := weaklyLocallyCompactSpace_of_isLocalHomeomorph hlh
  haveI : LocallyCompactSpace Y := inferInstance
  letI : MeasurableSpace Y := borel Y
  haveI : BorelSpace Y := ⟨rfl⟩
  have hf : Continuous f := continuous_subtype_val.comp hq.continuous
  have hopen : IsOpen ((S : Set ℂ)ᶜ) := S.finite_toSet.isClosed.isOpen_compl
  have hrange : ∀ y : Y, f y ∈ ((S : Set ℂ)ᶜ) := fun y => (q y).2
  have hcovOn : IsCoveringMapOn f ((S : Set ℂ)ᶜ) :=
    IsCoveringMapOn.of_isCoveringMap_subtype hopen hrange hq
  -- the fibres of the projection to the plane
  have hfin : ∀ z : ℂ, (f ⁻¹' {z}).Finite := by
    intro z
    by_cases hz : z ∈ ((S : Set ℂ)ᶜ)
    · refine (hfin' ⟨z, hz⟩).subset fun y hy => ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
      exact Subtype.ext hy
    · refine Set.finite_empty.subset fun y hy => ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
      refine absurd ?_ hz
      rw [← hy]
      exact (q y).2
  have hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z}) := by
    rintro _ ⟨y, rfl⟩
    exact IsEvenlyCovered.to_isEvenlyCovered_preimage
      (IsEvenlyCovered.subtypeVal_comp ((S : Set ℂ)ᶜ) hopen (hq (q y)))
  have hgs : HasCompactSupport g := HasCompactSupport.intro hKc hgvan
  obtain ⟨u, B, hB, hdbar, hbd⟩ := exists_isDbarAt_bound hfin hcov hf hlh contDiff_logWeight
    conj_logWeight curv_logWeight_pos hg1 hgs
  exact ⟨u, hdbar, isModerate_of_hasDiscBound hf hlh hcovOn hrange hdbar hKc hgvan hB hbd⟩

/-- **The functions of moderate growth on a covering of a punctured plane see its deck group.** -/
theorem hasEnoughFunctions : HasEnoughFunctions :=
  hasEnoughFunctions_of_dbarSolvable dbarSolvable

end Rigidity.RET

end
