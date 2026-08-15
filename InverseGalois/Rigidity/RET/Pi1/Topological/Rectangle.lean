/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.ConvexHomotopy

/-!
# Axis-parallel rectangles of the plane

The geometry needed to cut a rectangle into smaller rectangles: a rectangle is the set of points
whose real and imaginary parts lie in prescribed intervals, it is convex, so any two of its points
are joined inside it by a straight segment, and a segment with both endpoints on a horizontal
(resp. vertical) line stays on that line.

Points are named by their coordinates through `cpt`, which is the only spelling used downstream, so
that a cut of a rectangle is a manipulation of four real numbers.

## Main results

* `Rigidity.RET.rect` — the closed axis-parallel rectangle.
* `Rigidity.RET.convex_rect`, `Rigidity.RET.seg_subset_rect` — a rectangle is convex.
* `Rigidity.RET.im_of_mem_seg`, `Rigidity.RET.re_of_mem_seg` — a segment of a horizontal (resp.
  vertical) line stays on that line.
* `Rigidity.RET.cpt_mem_seg_horiz`, `Rigidity.RET.cpt_mem_seg_vert` — an intermediate point of a
  horizontal (resp. vertical) segment lies on it.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### Points and rectangles -/

/-- The point of the plane with the given coordinates. -/
def cpt (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem cpt_re (x y : ℝ) : (cpt x y).re = x := by simp [cpt]

@[simp] theorem cpt_im (x y : ℝ) : (cpt x y).im = y := by simp [cpt]

theorem cpt_eq (z : ℂ) : cpt z.re z.im = z := by
  apply Complex.ext <;> simp

/-- The closed rectangle with sides parallel to the axes. -/
def rect (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ :=
  {z : ℂ | x₀ ≤ z.re ∧ z.re ≤ x₁ ∧ y₀ ≤ z.im ∧ z.im ≤ y₁}

theorem mem_rect {x₀ x₁ y₀ y₁ : ℝ} {z : ℂ} :
    z ∈ rect x₀ x₁ y₀ y₁ ↔ x₀ ≤ z.re ∧ z.re ≤ x₁ ∧ y₀ ≤ z.im ∧ z.im ≤ y₁ := Iff.rfl

theorem cpt_mem_rect {x₀ x₁ y₀ y₁ x y : ℝ} (hx0 : x₀ ≤ x) (hx1 : x ≤ x₁) (hy0 : y₀ ≤ y)
    (hy1 : y ≤ y₁) : cpt x y ∈ rect x₀ x₁ y₀ y₁ := by
  simp only [mem_rect, cpt_re, cpt_im]
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- A rectangle is convex, being an intersection of two slabs. -/
theorem convex_rect (x₀ x₁ y₀ y₁ : ℝ) : Convex ℝ (rect x₀ x₁ y₀ y₁) := by
  have h : rect x₀ x₁ y₀ y₁
      = Complex.reLm ⁻¹' Set.Icc x₀ x₁ ∩ Complex.imLm ⁻¹' Set.Icc y₀ y₁ := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  rw [h]
  exact ((convex_Icc x₀ x₁).linear_preimage Complex.reLm).inter
    ((convex_Icc y₀ y₁).linear_preimage Complex.imLm)

/-- Two points of a rectangle are joined by a segment inside it. -/
theorem seg_subset_rect {x₀ x₁ y₀ y₁ : ℝ} {a b : ℂ} (ha : a ∈ rect x₀ x₁ y₀ y₁)
    (hb : b ∈ rect x₀ x₁ y₀ y₁) : seg a b ⊆ rect x₀ x₁ y₀ y₁ :=
  isSegClosed_iff_convex.mpr (convex_rect x₀ x₁ y₀ y₁) a ha b hb

/-- A rectangle grows with its coordinates. -/
theorem rect_mono {x₀ x₁ y₀ y₁ x₀' x₁' y₀' y₁' : ℝ} (h0 : x₀' ≤ x₀) (h1 : x₁ ≤ x₁')
    (h2 : y₀' ≤ y₀) (h3 : y₁ ≤ y₁') : rect x₀ x₁ y₀ y₁ ⊆ rect x₀' x₁' y₀' y₁' := by
  rintro z ⟨hz0, hz1, hz2, hz3⟩
  exact ⟨le_trans h0 hz0, le_trans hz1 h1, le_trans h2 hz2, le_trans hz3 h3⟩

/-! ### Coordinates along a segment -/

/-- A segment joining two points at the same height stays at that height. -/
theorem im_of_mem_seg {a b : ℂ} {y : ℝ} (ha : a.im = y) (hb : b.im = y) {z : ℂ}
    (hz : z ∈ seg a b) : z.im = y := by
  obtain ⟨t, -, rfl⟩ := hz
  simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im, ha, hb]
  ring

/-- A segment joining two points on the same vertical line stays on that line. -/
theorem re_of_mem_seg {a b : ℂ} {x : ℝ} (ha : a.re = x) (hb : b.re = x) {z : ℂ}
    (hz : z ∈ seg a b) : z.re = x := by
  obtain ⟨t, -, rfl⟩ := hz
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, ha, hb]
  ring

theorem cpt_add_smul_horiz (x₀ x₁ y t : ℝ) :
    cpt x₀ y + (t : ℂ) * (cpt x₁ y - cpt x₀ y) = cpt (x₀ + t * (x₁ - x₀)) y := by
  apply Complex.ext <;> simp [cpt]

theorem cpt_add_smul_vert (x y₀ y₁ t : ℝ) :
    cpt x y₀ + (t : ℂ) * (cpt x y₁ - cpt x y₀) = cpt x (y₀ + t * (y₁ - y₀)) := by
  apply Complex.ext <;> simp [cpt]

/-- An intermediate abscissa on a horizontal segment is a point of it. -/
theorem cpt_mem_seg_horiz {x₀ x₁ c y : ℝ} (h0 : x₀ ≤ c) (h1 : c ≤ x₁) :
    cpt c y ∈ seg (cpt x₀ y) (cpt x₁ y) := by
  rcases eq_or_lt_of_le (h0.trans h1) with heq | hlt
  · refine ⟨0, by norm_num, ?_⟩
    rw [show ((0 : ℝ) : ℂ) = 0 by norm_num, zero_mul, add_zero]
    congr 1
    linarith [h0, h1, heq]
  · have hne : x₁ - x₀ ≠ 0 := by linarith
    refine ⟨(c - x₀) / (x₁ - x₀),
      ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith⟩, ?_⟩
    rw [cpt_add_smul_horiz]
    congr 1
    rw [div_mul_cancel₀ _ hne]
    ring

/-- An intermediate ordinate on a vertical segment is a point of it. -/
theorem cpt_mem_seg_vert {y₀ y₁ c x : ℝ} (h0 : y₀ ≤ c) (h1 : c ≤ y₁) :
    cpt x c ∈ seg (cpt x y₀) (cpt x y₁) := by
  rcases eq_or_lt_of_le (h0.trans h1) with heq | hlt
  · refine ⟨0, by norm_num, ?_⟩
    rw [show ((0 : ℝ) : ℂ) = 0 by norm_num, zero_mul, add_zero]
    congr 1
    linarith [h0, h1, heq]
  · have hne : y₁ - y₀ ≠ 0 := by linarith
    refine ⟨(c - y₀) / (y₁ - y₀),
      ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith⟩, ?_⟩
    rw [cpt_add_smul_vert]
    congr 1
    rw [div_mul_cancel₀ _ hne]
    ring

end Rigidity.RET

end
