/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.Rectangle
import InverseGalois.Rigidity.RET.Pi1.Topological.BoxCut
import InverseGalois.Rigidity.RET.Pi1.Topological.SquarePuncture

/-!
# Cutting an axis-parallel rectangle

An axis-parallel rectangle can be cut in two by a vertical line `re = c` or a horizontal line
`im = d`, and the two pieces are again axis-parallel rectangles. This file collects the geometry
of such a cut: the open rectangle and its topology, the membership of the cut point in the side
it subdivides, and the fact that the cutting segment misses a set of punctures as soon as the
cut coordinate does.

## Main results

* `Rigidity.RET.isOpen_openRect` — the open rectangle is open.
* `Rigidity.RET.seg_horiz_subset_diff`, `Rigidity.RET.seg_vert_subset_diff` — a horizontal or
  vertical segment inside a rectangle avoids the punctures whose coordinate it avoids.
* `Rigidity.RET.rect_union_vert`, `Rigidity.RET.rect_union_horiz` — the two pieces of a cut cover
  the rectangle.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### The open rectangle -/

/-- The open rectangle with sides parallel to the axes. -/
def openRect (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ :=
  {z : ℂ | x₀ < z.re ∧ z.re < x₁ ∧ y₀ < z.im ∧ z.im < y₁}

/-- The open rectangle is an open set. -/
theorem isOpen_openRect (x₀ x₁ y₀ y₁ : ℝ) : IsOpen (openRect x₀ x₁ y₀ y₁) := by
  have h : openRect x₀ x₁ y₀ y₁
      = (Complex.re ⁻¹' Set.Ioo x₀ x₁) ∩ (Complex.im ⁻¹' Set.Ioo y₀ y₁) := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  rw [h]
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_Ioo.preimage Complex.continuous_im)

/-- The open rectangle sits inside the closed one. -/
theorem openRect_subset_rect (x₀ x₁ y₀ y₁ : ℝ) :
    openRect x₀ x₁ y₀ y₁ ⊆ rect x₀ x₁ y₀ y₁ := by
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨h1.le, h2.le, h3.le, h4.le⟩

/-! ### Reversed segments through a coordinate -/

/-- A point of a horizontal side, read from right to left. -/
theorem cpt_mem_seg_horiz' {x₀ x₁ c y : ℝ} (h0 : x₀ ≤ c) (h1 : c ≤ x₁) :
    cpt c y ∈ seg (cpt x₁ y) (cpt x₀ y) := by
  rw [seg_symm]; exact cpt_mem_seg_horiz h0 h1

/-- A point of a vertical side, read from top to bottom. -/
theorem cpt_mem_seg_vert' {y₀ y₁ c x : ℝ} (h0 : y₀ ≤ c) (h1 : c ≤ y₁) :
    cpt x c ∈ seg (cpt x y₁) (cpt x y₀) := by
  rw [seg_symm]; exact cpt_mem_seg_vert h0 h1

/-! ### Segments of a rectangle avoiding the punctures -/

/-- A horizontal segment inside a rectangle, at a height attained by no puncture of the
rectangle, misses the punctures. -/
theorem seg_horiz_subset_diff {S : Set ℂ} {x₀ x₁ y₀ y₁ u v y : ℝ}
    (hu : u ∈ Set.Icc x₀ x₁) (hv : v ∈ Set.Icc x₀ x₁) (hy : y ∈ Set.Icc y₀ y₁)
    (havoid : ∀ s ∈ S, s ∈ rect x₀ x₁ y₀ y₁ → s.im ≠ y) :
    seg (cpt u y) (cpt v y) ⊆ rect x₀ x₁ y₀ y₁ \ S := by
  intro z hz
  have hzr : z ∈ rect x₀ x₁ y₀ y₁ :=
    seg_subset_rect (cpt_mem_rect hu.1 hu.2 hy.1 hy.2) (cpt_mem_rect hv.1 hv.2 hy.1 hy.2) hz
  exact ⟨hzr, fun hzS => havoid z hzS hzr (im_of_mem_seg (cpt_im u y) (cpt_im v y) hz)⟩

/-- A vertical segment inside a rectangle, at an abscissa attained by no puncture of the
rectangle, misses the punctures. -/
theorem seg_vert_subset_diff {S : Set ℂ} {x₀ x₁ y₀ y₁ u v x : ℝ}
    (hu : u ∈ Set.Icc y₀ y₁) (hv : v ∈ Set.Icc y₀ y₁) (hx : x ∈ Set.Icc x₀ x₁)
    (havoid : ∀ s ∈ S, s ∈ rect x₀ x₁ y₀ y₁ → s.re ≠ x) :
    seg (cpt x u) (cpt x v) ⊆ rect x₀ x₁ y₀ y₁ \ S := by
  intro z hz
  have hzr : z ∈ rect x₀ x₁ y₀ y₁ :=
    seg_subset_rect (cpt_mem_rect hx.1 hx.2 hu.1 hu.2) (cpt_mem_rect hx.1 hx.2 hv.1 hv.2) hz
  exact ⟨hzr, fun hzS => havoid z hzS hzr (re_of_mem_seg (cpt_re x u) (cpt_re x v) hz)⟩

/-! ### Splitting a rectangle in two -/

/-- Cutting a rectangle by a vertical line covers it. -/
theorem rect_union_vert {x₀ x₁ y₀ y₁ c : ℝ} (h0 : x₀ ≤ c) (h1 : c ≤ x₁) :
    rect x₀ c y₀ y₁ ∪ rect c x₁ y₀ y₁ = rect x₀ x₁ y₀ y₁ := by
  ext z
  constructor
  · rintro (⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩)
    · exact ⟨a1, a2.trans h1, a3, a4⟩
    · exact ⟨h0.trans a1, a2, a3, a4⟩
  · rintro ⟨a1, a2, a3, a4⟩
    rcases le_total z.re c with h | h
    · exact Or.inl ⟨a1, h, a3, a4⟩
    · exact Or.inr ⟨h, a2, a3, a4⟩

/-- Cutting a rectangle by a horizontal line covers it. -/
theorem rect_union_horiz {x₀ x₁ y₀ y₁ d : ℝ} (h0 : y₀ ≤ d) (h1 : d ≤ y₁) :
    rect x₀ x₁ y₀ d ∪ rect x₀ x₁ d y₁ = rect x₀ x₁ y₀ y₁ := by
  ext z
  constructor
  · rintro (⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩)
    · exact ⟨a1, a2, a3, a4.trans h1⟩
    · exact ⟨a1, a2, h0.trans a3, a4⟩
  · rintro ⟨a1, a2, a3, a4⟩
    rcases le_total z.im d with h | h
    · exact Or.inl ⟨a1, a2, a3, h⟩
    · exact Or.inr ⟨a1, a2, h, a4⟩

end Rigidity.RET

end
