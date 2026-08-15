/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.RectCut

/-!
# The boundary loop of a rectangle as a product of puncture loops

Fix a set `S` of punctures and a subset `X` of the plane containing the punctured rectangle. The
predicate `RectSpider X S x₀ x₁ y₀ y₁` says that the boundary loop of the rectangle, based at its
bottom-left corner, is an ordered product of loops winding once around each puncture inside it.

This file records the three ways the predicate is produced: a rectangle without punctures, a
rectangle cut in two by a vertical or a horizontal line, and a small square centred at a single
puncture. Together they are the inductive step, the base case and the leaf of the induction on the
number of punctures.

## Main results

* `Rigidity.RET.rectSpider_of_empty` — a rectangle containing no puncture.
* `Rigidity.RET.rectSpider_of_cut_vert`, `Rigidity.RET.rectSpider_of_cut_horiz` — cutting a
  rectangle along a line missing every puncture.
* `Rigidity.RET.rectSpider_of_single` — a square of half-side `a` centred at a puncture, small
  enough to sit inside a punctured disc.
-/

open scoped unitInterval
open CategoryTheory

noncomputable section

namespace Rigidity.RET

/-- The boundary loop of the rectangle is an ordered product of loops around the punctures of
`S` that it contains. -/
def RectSpider (X S : Set ℂ) (x₀ x₁ y₀ y₁ : ℝ) : Prop :=
  ∀ (hab : seg (cpt x₀ y₀) (cpt x₁ y₀) ⊆ X) (hbc : seg (cpt x₁ y₀) (cpt x₁ y₁) ⊆ X)
    (hcd : seg (cpt x₁ y₁) (cpt x₀ y₁) ⊆ X) (hda : seg (cpt x₀ y₁) (cpt x₀ y₀) ⊆ X),
    IsPunctureProd X (S ∩ rect x₀ x₁ y₀ y₁) (hab (left_mem_seg _ _))
      (FundamentalGroup.fromPath (boxLoop hab hbc hcd hda))

/-- The constant loop is the identity of the fundamental group. -/
theorem fromPath_refl {Y : Type*} [TopologicalSpace Y] (x : Y) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.refl x) = 1 := rfl

/-! ### Base case: no punctures -/

/-- **A rectangle containing no puncture** has null-homotopic boundary loop, the empty product. -/
theorem rectSpider_of_empty {X S : Set ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hsub : rect x₀ x₁ y₀ y₁ \ S ⊆ X) (hempty : S ∩ rect x₀ x₁ y₀ y₁ = ∅) :
    RectSpider X S x₀ x₁ y₀ y₁ := by
  intro hab hbc hcd hda
  have hRX : rect x₀ x₁ y₀ y₁ ⊆ X := by
    intro z hz
    refine hsub ⟨hz, fun hzS => ?_⟩
    have : z ∈ S ∩ rect x₀ x₁ y₀ y₁ := ⟨hzS, hz⟩
    rw [hempty] at this
    exact this
  rw [hempty, boxLoop_eq_refl (isSegClosed_iff_convex.mpr (convex_rect x₀ x₁ y₀ y₁)) hRX
    (cpt_mem_rect le_rfl hx le_rfl hy) (cpt_mem_rect hx le_rfl le_rfl hy)
    (cpt_mem_rect hx le_rfl hy le_rfl) (cpt_mem_rect le_rfl hx hy le_rfl) hab hbc hcd hda,
    fromPath_refl]
  exact IsPunctureProd.one _

/-! ### Vertical cut -/

/-- **Cutting a rectangle by a vertical line missing every puncture**: if both halves have
boundary loop a product of puncture loops, so does the rectangle. -/
theorem rectSpider_of_cut_vert {X S : Set ℂ} {x₀ x₁ y₀ y₁ c : ℝ}
    (h0 : x₀ ≤ c) (h1 : c ≤ x₁) (hy : y₀ ≤ y₁)
    (hsub : rect x₀ x₁ y₀ y₁ \ S ⊆ X)
    (havoid : ∀ s ∈ S, s ∈ rect x₀ x₁ y₀ y₁ → s.re ≠ c)
    (hL : RectSpider X S x₀ c y₀ y₁) (hR : RectSpider X S c x₁ y₀ y₁) :
    RectSpider X S x₀ x₁ y₀ y₁ := by
  intro hab hbc hcd hda
  have hp : cpt c y₀ ∈ seg (cpt x₀ y₀) (cpt x₁ y₀) := cpt_mem_seg_horiz h0 h1
  have hq : cpt c y₁ ∈ seg (cpt x₁ y₁) (cpt x₀ y₁) := cpt_mem_seg_horiz' h0 h1
  have hpq : seg (cpt c y₀) (cpt c y₁) ⊆ X :=
    (seg_vert_subset_diff ⟨le_rfl, hy⟩ ⟨hy, le_rfl⟩ ⟨h0, h1⟩ havoid).trans hsub
  have hdisj : Disjoint (S ∩ rect x₀ c y₀ y₁) (S ∩ rect c x₁ y₀ y₁) := by
    rw [Set.disjoint_left]
    rintro z ⟨hzS, hzL⟩ ⟨-, hzR⟩
    have hz : z ∈ rect x₀ x₁ y₀ y₁ := ⟨hzL.1, hzR.2.1, hzL.2.2.1, hzL.2.2.2⟩
    exact havoid z hzS hz (le_antisymm hzL.2.1 hzR.1)
  have key := isPunctureProd_boxLoop_cut hab hbc hcd hda hp hq hpq
    (hL _ _ _ _) (hR _ _ _ _) hdisj
  have hTeq : (S ∩ rect x₀ c y₀ y₁) ∪ (S ∩ rect c x₁ y₀ y₁) = S ∩ rect x₀ x₁ y₀ y₁ := by
    rw [← Set.inter_union_distrib_left, rect_union_vert h0 h1]
  rw [hTeq] at key
  exact key

/-! ### Horizontal cut -/

/-- **Cutting a rectangle by a horizontal line missing every puncture**: if both halves have
boundary loop a product of puncture loops, so does the rectangle. -/
theorem rectSpider_of_cut_horiz {X S : Set ℂ} {x₀ x₁ y₀ y₁ d : ℝ}
    (hx : x₀ ≤ x₁) (h0 : y₀ ≤ d) (h1 : d ≤ y₁)
    (hsub : rect x₀ x₁ y₀ y₁ \ S ⊆ X)
    (havoid : ∀ s ∈ S, s ∈ rect x₀ x₁ y₀ y₁ → s.im ≠ d)
    (hB : RectSpider X S x₀ x₁ y₀ d) (hT : RectSpider X S x₀ x₁ d y₁) :
    RectSpider X S x₀ x₁ y₀ y₁ := by
  intro hab hbc hcd hda
  refine isPunctureProd_boxLoop_rotate hab hbc hcd hda ?_
  have hp : cpt x₁ d ∈ seg (cpt x₁ y₀) (cpt x₁ y₁) := cpt_mem_seg_vert h0 h1
  have hq : cpt x₀ d ∈ seg (cpt x₀ y₁) (cpt x₀ y₀) := cpt_mem_seg_vert' h0 h1
  have hpq : seg (cpt x₁ d) (cpt x₀ d) ⊆ X :=
    (seg_horiz_subset_diff ⟨hx, le_rfl⟩ ⟨le_rfl, hx⟩ ⟨h0, h1⟩ havoid).trans hsub
  have hdisj : Disjoint (S ∩ rect x₀ x₁ y₀ d) (S ∩ rect x₀ x₁ d y₁) := by
    rw [Set.disjoint_left]
    rintro z ⟨hzS, hzB⟩ ⟨-, hzT⟩
    have hz : z ∈ rect x₀ x₁ y₀ y₁ := ⟨hzB.1, hzB.2.1, hzB.2.2.1, hzT.2.2.2⟩
    exact havoid z hzS hz (le_antisymm hzB.2.2.2 hzT.2.2.1)
  have key := isPunctureProd_boxLoop_cut hbc hcd hda hab hp hq hpq
    (isPunctureProd_boxLoop_rotate' _ _ _ _ (hB _ _ _ _))
    (isPunctureProd_boxLoop_rotate' _ _ _ _ (hT _ _ _ _)) hdisj
  have hTeq : (S ∩ rect x₀ x₁ y₀ d) ∪ (S ∩ rect x₀ x₁ d y₁) = S ∩ rect x₀ x₁ y₀ y₁ := by
    rw [← Set.inter_union_distrib_left, rect_union_horiz h0 h1]
  rw [hTeq] at key
  exact key

/-! ### The one-puncture square -/

/-- **A square centred at a puncture and small enough to sit in a punctured disc** has boundary
loop a loop winding once around that puncture. -/
theorem rectSpider_of_single {X S : Set ℂ} {s : ℂ} {a ρ : ℝ} (ha : 0 < a) (h2a : 2 * a < ρ)
    (hdisc : puncturedDisc s ρ ⊆ X)
    (hone : S ∩ rect (s.re - a) (s.re + a) (s.im - a) (s.im + a) = {s}) :
    RectSpider X S (s.re - a) (s.re + a) (s.im - a) (s.im + a) := by
  intro hab hbc hcd hda
  set w : ℂ := -(a : ℂ) - (a : ℂ) * Complex.I with hwdef
  have hwre : w.re = -a := by simp [hwdef]
  have hwim : w.im = -a := by simp [hwdef]
  have hw : w ≠ 0 := fun h => by
    have hz : (-a) = 0 := by rw [← hwre, h, Complex.zero_re]
    linarith
  have hwρ : ‖w‖ < ρ := by
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im w) ?_
    rw [hwre, hwim, abs_neg, abs_of_pos ha]
    linarith
  rw [hone]
  refine IsPunctureProd.single (isPunctureLoop_boxLoop' hdisc hw hwρ ?_ ?_ ?_ ?_ hab hbc hcd hda)
  · apply Complex.ext <;> simp [cpt, hwdef, sub_eq_add_neg]
  · apply Complex.ext <;> simp [cpt, hwdef, sub_eq_add_neg]
  · apply Complex.ext <;> simp [cpt, hwdef, sub_eq_add_neg]
  · apply Complex.ext <;> simp [cpt, hwdef, sub_eq_add_neg]

end Rigidity.RET

end
