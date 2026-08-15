/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.Pi1Image
import InverseGalois.Rigidity.RET.Pi1.Topological.RectCut
import InverseGalois.Rigidity.RET.Pi1.Topological.Spider

/-!
# Frames around a rectangle

The rectangle induction cuts a rectangle into smaller ones and asks each piece for a system of
loops around the punctures it contains.  To make the resulting loops *generate* — and not merely
multiply out to the boundary loop — each piece must be accompanied by an open convex neighbourhood
of it, a **frame**, which contains no punctures beyond the ones inside the rectangle.  The frames
of the two halves of a cut then form an open cover of the frame of the whole, and the Seifert–van
Kampen theorem says the loops living in the halves generate the loops living in the whole.

A frame is grown by a fixed margin `m` beyond the cut line, so that the two half-frames overlap in
a slab; the hypothesis that no puncture lies in the closed slab is what keeps the punctures of a
half-frame confined to its rectangle.

## Main results

* `Rigidity.RET.RectFrame` — an open convex neighbourhood of a rectangle meeting the punctures
  only inside it.
* `Rigidity.RET.RectFrame.cutLeft` and friends — the frames of the four halves of a cut.
* `Rigidity.RET.frame_cover_re` — the two half-frames cover the frame.
* `Rigidity.RET.pi1Image_map_segArrow` — transporting the loops of a subregion along a segment of
  that subregion.
* `Rigidity.RET.isPunctureProd_boxLoop_rotate_pi1` — rotating the basepoint of a boundary loop
  while the loops accounted for stay those of a subregion.
* `Rigidity.RET.pi1Image_le_sup_of_cut` — Seifert–van Kampen for a cut, with both halves read at
  the basepoint of the whole.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### Open half-planes -/

/-- An open left half-plane is convex. -/
theorem convex_reLt (c : ℝ) : Convex ℝ {z : ℂ | z.re < c} :=
  convex_halfSpace_lt Complex.reLm.isLinear c

/-- An open right half-plane is convex. -/
theorem convex_reGt (c : ℝ) : Convex ℝ {z : ℂ | c < z.re} :=
  convex_halfSpace_gt Complex.reLm.isLinear c

/-- An open lower half-plane is convex. -/
theorem convex_imLt (d : ℝ) : Convex ℝ {z : ℂ | z.im < d} :=
  convex_halfSpace_lt Complex.imLm.isLinear d

/-- An open upper half-plane is convex. -/
theorem convex_imGt (d : ℝ) : Convex ℝ {z : ℂ | d < z.im} :=
  convex_halfSpace_gt Complex.imLm.isLinear d

/-- A left half-plane is open. -/
theorem isOpen_reLt (c : ℝ) : IsOpen {z : ℂ | z.re < c} :=
  isOpen_lt Complex.continuous_re continuous_const

/-- A right half-plane is open. -/
theorem isOpen_reGt (c : ℝ) : IsOpen {z : ℂ | c < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- A lower half-plane is open. -/
theorem isOpen_imLt (d : ℝ) : IsOpen {z : ℂ | z.im < d} :=
  isOpen_lt Complex.continuous_im continuous_const

/-- An upper half-plane is open. -/
theorem isOpen_imGt (d : ℝ) : IsOpen {z : ℂ | d < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

/-! ### Frames -/

/-- A **frame** for a rectangle is an open convex neighbourhood of it whose punctures all lie in
the rectangle. -/
structure RectFrame (S V : Set ℂ) (x₀ x₁ y₀ y₁ : ℝ) : Prop where
  /-- A frame is convex. -/
  isConvex : Convex ℝ V
  /-- A frame is open. -/
  isOpen : IsOpen V
  /-- A frame contains its rectangle. -/
  rect_subset : rect x₀ x₁ y₀ y₁ ⊆ V
  /-- A frame meets the punctures only inside its rectangle. -/
  inter_subset : S ∩ V ⊆ rect x₀ x₁ y₀ y₁

/-- **The frame of the left half of a vertical cut**, grown by `m` past the cut line: it is a
frame as soon as no puncture of the rectangle has real part in the closed slab `[c, c + m)`. -/
theorem RectFrame.cutLeft {S V : Set ℂ} {x₀ x₁ y₀ y₁ c m : ℝ}
    (h : RectFrame S V x₀ x₁ y₀ y₁) (h1 : c ≤ x₁) (hm : 0 < m)
    (hav : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re < c ∨ c + m ≤ t.re) :
    RectFrame S (V ∩ {z : ℂ | z.re < c + m}) x₀ c y₀ y₁ where
  isConvex := h.isConvex.inter (convex_reLt _)
  isOpen := h.isOpen.inter (isOpen_reLt _)
  rect_subset := fun z hz =>
    ⟨h.rect_subset (rect_mono le_rfl h1 le_rfl le_rfl hz), by
      have := hz.2.1; simp only [Set.mem_setOf_eq]; linarith⟩
  inter_subset := by
    rintro t ⟨htS, htV, htlt⟩
    have htR : t ∈ rect x₀ x₁ y₀ y₁ := h.inter_subset ⟨htS, htV⟩
    rcases hav t htS htR with hlt | hge
    · exact ⟨htR.1, hlt.le, htR.2.2.1, htR.2.2.2⟩
    · exact absurd htlt (not_lt.2 hge)

/-- **The frame of the right half of a vertical cut**, grown by `m` past the cut line. -/
theorem RectFrame.cutRight {S V : Set ℂ} {x₀ x₁ y₀ y₁ c m : ℝ}
    (h : RectFrame S V x₀ x₁ y₀ y₁) (h0 : x₀ ≤ c) (hm : 0 < m)
    (hav : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≤ c - m ∨ c < t.re) :
    RectFrame S (V ∩ {z : ℂ | c - m < z.re}) c x₁ y₀ y₁ where
  isConvex := h.isConvex.inter (convex_reGt _)
  isOpen := h.isOpen.inter (isOpen_reGt _)
  rect_subset := fun z hz =>
    ⟨h.rect_subset (rect_mono h0 le_rfl le_rfl le_rfl hz), by
      have := hz.1; simp only [Set.mem_setOf_eq]; linarith⟩
  inter_subset := by
    rintro t ⟨htS, htV, htgt⟩
    have htR : t ∈ rect x₀ x₁ y₀ y₁ := h.inter_subset ⟨htS, htV⟩
    rcases hav t htS htR with hle | hgt
    · exact absurd htgt (not_lt.2 hle)
    · exact ⟨hgt.le, htR.2.1, htR.2.2.1, htR.2.2.2⟩

/-- **The frame of the bottom half of a horizontal cut**, grown by `m` past the cut line. -/
theorem RectFrame.cutBot {S V : Set ℂ} {x₀ x₁ y₀ y₁ d m : ℝ}
    (h : RectFrame S V x₀ x₁ y₀ y₁) (h1 : d ≤ y₁) (hm : 0 < m)
    (hav : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im < d ∨ d + m ≤ t.im) :
    RectFrame S (V ∩ {z : ℂ | z.im < d + m}) x₀ x₁ y₀ d where
  isConvex := h.isConvex.inter (convex_imLt _)
  isOpen := h.isOpen.inter (isOpen_imLt _)
  rect_subset := fun z hz =>
    ⟨h.rect_subset (rect_mono le_rfl le_rfl le_rfl h1 hz), by
      have := hz.2.2.2; simp only [Set.mem_setOf_eq]; linarith⟩
  inter_subset := by
    rintro t ⟨htS, htV, htlt⟩
    have htR : t ∈ rect x₀ x₁ y₀ y₁ := h.inter_subset ⟨htS, htV⟩
    rcases hav t htS htR with hlt | hge
    · exact ⟨htR.1, htR.2.1, htR.2.2.1, hlt.le⟩
    · exact absurd htlt (not_lt.2 hge)

/-- **The frame of the top half of a horizontal cut**, grown by `m` past the cut line. -/
theorem RectFrame.cutTop {S V : Set ℂ} {x₀ x₁ y₀ y₁ d m : ℝ}
    (h : RectFrame S V x₀ x₁ y₀ y₁) (h0 : y₀ ≤ d) (hm : 0 < m)
    (hav : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≤ d - m ∨ d < t.im) :
    RectFrame S (V ∩ {z : ℂ | d - m < z.im}) x₀ x₁ d y₁ where
  isConvex := h.isConvex.inter (convex_imGt _)
  isOpen := h.isOpen.inter (isOpen_imGt _)
  rect_subset := fun z hz =>
    ⟨h.rect_subset (rect_mono le_rfl le_rfl h0 le_rfl hz), by
      have := hz.2.2.1; simp only [Set.mem_setOf_eq]; linarith⟩
  inter_subset := by
    rintro t ⟨htS, htV, htgt⟩
    have htR : t ∈ rect x₀ x₁ y₀ y₁ := h.inter_subset ⟨htS, htV⟩
    rcases hav t htS htR with hle | hgt
    · exact absurd htgt (not_lt.2 hle)
    · exact ⟨htR.1, htR.2.1, hgt.le, htR.2.2.2⟩

/-! ### The two half-frames cover the frame -/

/-- The two half-frames of a vertical cut cover the frame. -/
theorem frame_cover_re (V : Set ℂ) {c m : ℝ} (hm : 0 < m) :
    V ⊆ (V ∩ {z : ℂ | z.re < c + m}) ∪ (V ∩ {z : ℂ | c - m < z.re}) := by
  intro z hz
  rcases lt_or_ge z.re (c + m) with h | h
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr ⟨hz, by simp only [Set.mem_setOf_eq]; linarith⟩

/-- The two half-frames of a horizontal cut cover the frame. -/
theorem frame_cover_im (V : Set ℂ) {d m : ℝ} (hm : 0 < m) :
    V ⊆ (V ∩ {z : ℂ | z.im < d + m}) ∪ (V ∩ {z : ℂ | d - m < z.im}) := by
  intro z hz
  rcases lt_or_ge z.im (d + m) with h | h
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr ⟨hz, by simp only [Set.mem_setOf_eq]; linarith⟩

/-! ### A once-punctured convex region has cyclic fundamental group -/

/-- A loop winding once around the missing point of a convex region generates all of its loops,
stated for a region presented as an arbitrary set equal to the punctured one. -/
theorem zpowers_eq_top_of_isPunctureLoop' {W U : Set ℂ} (hconv : Convex ℝ W) {s : ℂ}
    (hs : s ∈ W) (hU : U = W \ {s}) {z₀ : ℂ} {hz₀ : z₀ ∈ U}
    {γ : FundamentalGroup ↥U ⟨z₀, hz₀⟩} (hγ : IsPunctureLoop U s hz₀ γ) :
    Subgroup.zpowers γ = ⊤ := by
  subst hU
  exact zpowers_eq_top_of_isPunctureLoop hconv hs hγ

/-! ### Transporting the loops of a subregion along a segment -/

/-- Transporting along a segment of a subregion carries the loops living in the subregion at one
endpoint onto those at the other. -/
theorem pi1Image_map_segArrow {X U : Set ℂ} (hUX : U ⊆ X) {a b : ℂ} (hab : seg a b ⊆ U)
    (habX : seg a b ⊆ X) :
    (pi1Image hUX (hab (right_mem_seg a b))).map
        (FundamentalGroup.transport (segArrow (seg_subset_symm habX))).toMonoidHom
      = pi1Image hUX (hab (left_mem_seg a b)) :=
  pi1Image_map_transport hUX (hab (right_mem_seg a b)) (hab (left_mem_seg a b))
    (segPath _ _ (seg_subset_symm habX))
    (fun t => seg_subset_symm hab (mem_seg_segPath (seg_subset_symm habX) t))

/-- **Moving the basepoint of a boundary loop to the next vertex**, when the loops accounted for
are exactly those living in a subregion carrying the whole quadrilateral. -/
theorem isPunctureProd_boxLoop_rotate_pi1 {X U T : Set ℂ} (hUX : U ⊆ X) {a b c d : ℂ}
    (hab : seg a b ⊆ U) (hbc : seg b c ⊆ U) (hcd : seg c d ⊆ U) (hda : seg d a ⊆ U)
    (h : IsPunctureProd X T (hUX (hbc (left_mem_seg _ _)))
      (FundamentalGroup.fromPath (boxLoop (hbc.trans hUX) (hcd.trans hUX) (hda.trans hUX)
        (hab.trans hUX)))
      (pi1Image hUX (hbc (left_mem_seg _ _)))) :
    IsPunctureProd X T (hUX (hab (left_mem_seg _ _)))
      (FundamentalGroup.fromPath (boxLoop (hab.trans hUX) (hbc.trans hUX) (hcd.trans hUX)
        (hda.trans hUX)))
      (pi1Image hUX (hab (left_mem_seg _ _))) := by
  have key := isPunctureProd_boxLoop_rotate (hab.trans hUX) (hbc.trans hUX) (hcd.trans hUX)
    (hda.trans hUX) h
  exact key.mono (le_of_eq (pi1Image_map_segArrow hUX hab (hab.trans hUX)).symm)

/-- **Moving the basepoint of a boundary loop to the previous vertex**, in the same form. -/
theorem isPunctureProd_boxLoop_rotate'_pi1 {X U T : Set ℂ} (hUX : U ⊆ X) {a b c d : ℂ}
    (hab : seg a b ⊆ U) (hbc : seg b c ⊆ U) (hcd : seg c d ⊆ U) (hda : seg d a ⊆ U)
    (h : IsPunctureProd X T (hUX (hab (left_mem_seg _ _)))
      (FundamentalGroup.fromPath (boxLoop (hab.trans hUX) (hbc.trans hUX) (hcd.trans hUX)
        (hda.trans hUX)))
      (pi1Image hUX (hab (left_mem_seg _ _)))) :
    IsPunctureProd X T (hUX (hbc (left_mem_seg _ _)))
      (FundamentalGroup.fromPath (boxLoop (hbc.trans hUX) (hcd.trans hUX) (hda.trans hUX)
        (hab.trans hUX)))
      (pi1Image hUX (hbc (left_mem_seg _ _))) :=
  isPunctureProd_boxLoop_rotate_pi1 hUX hbc hcd hda hab
    (isPunctureProd_boxLoop_rotate_pi1 hUX hcd hda hab hbc
      (isPunctureProd_boxLoop_rotate_pi1 hUX hda hab hbc hcd h))

/-! ### Seifert–van Kampen for a cut -/

/-- **The loops of a punctured frame are generated by those of its two punctured half-frames**,
both read at the basepoint of the whole: the ones of the half containing the basepoint directly,
the ones of the other half after transport along the segment joining the two basepoints. -/
theorem pi1Image_le_sup_of_cut {X S V VL VR : Set ℂ} (hSfin : S.Finite) (hVX : V \ S ⊆ X)
    (hLconv : Convex ℝ VL) (hLopen : IsOpen VL) (hRconv : Convex ℝ VR) (hRopen : IsOpen VR)
    (hLV : VL ⊆ V) (hRV : VR ⊆ V) (hcover : V ⊆ VL ∪ VR)
    {A P : ℂ} (hAP : seg A P ⊆ V \ S) (hAPL : seg A P ⊆ VL \ S) (hPR : P ∈ VR \ S) :
    pi1Image hVX (hAP (left_mem_seg A P))
      ≤ pi1Image ((Set.diff_subset_diff_left hLV).trans hVX) (hAPL (left_mem_seg A P))
        ⊔ (pi1Image ((Set.diff_subset_diff_left hRV).trans hVX) hPR).map
            (FundamentalGroup.transport
              (segArrow (seg_subset_symm (hAP.trans hVX)))).toMonoidHom := by
  have hLS : VL \ S ⊆ V \ S := Set.diff_subset_diff_left hLV
  have hRS : VR \ S ⊆ V \ S := Set.diff_subset_diff_left hRV
  have hcov : V \ S ⊆ (VL \ S) ∪ (VR \ S) := by
    rintro z ⟨hzV, hzS⟩
    rcases hcover hzV with h | h
    · exact Or.inl ⟨h, hzS⟩
    · exact Or.inr ⟨h, hzS⟩
  haveI : PathConnectedSpace ↥(VL \ S) :=
    Convex.pathConnectedSpace_diff_countable_complex hLconv hLopen hSfin.countable
      ⟨A, hAPL (left_mem_seg A P)⟩
  haveI : PathConnectedSpace ↥(VR \ S) :=
    Convex.pathConnectedSpace_diff_countable_complex hRconv hRopen hSfin.countable ⟨P, hPR⟩
  have hinter : (VL \ S) ∩ (VR \ S) = (VL ∩ VR) \ S := by
    ext z; constructor
    · rintro ⟨⟨h1, h2⟩, h3, -⟩; exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2, h3⟩
  haveI : PathConnectedSpace ↥((VL \ S) ∩ (VR \ S)) := by
    rw [hinter]
    exact Convex.pathConnectedSpace_diff_countable_complex (hLconv.inter hRconv)
      (hLopen.inter hRopen) hSfin.countable
      ⟨P, ⟨(hAPL (right_mem_seg A P)).1, hPR.1⟩, hPR.2⟩
  have hvk := pi1Image_le_sup_of_cover hVX hLS hRS hcov (hLopen.sdiff hSfin.isClosed)
    (hRopen.sdiff hSfin.isClosed) (hAPL (right_mem_seg A P)) hPR
  have h1 := pi1Image_map_segArrow hVX hAP (hAP.trans hVX)
  have h2 := pi1Image_map_segArrow (hLS.trans hVX) hAPL (hAP.trans hVX)
  calc pi1Image hVX (hAP (left_mem_seg A P))
      = (pi1Image hVX (hAP (right_mem_seg A P))).map _ := h1.symm
    _ ≤ (pi1Image (hLS.trans hVX) (hAPL (right_mem_seg A P))
          ⊔ pi1Image (hRS.trans hVX) hPR).map _ := Subgroup.map_mono hvk
    _ = (pi1Image (hLS.trans hVX) (hAPL (right_mem_seg A P))).map _
          ⊔ (pi1Image (hRS.trans hVX) hPR).map _ := Subgroup.map_sup _ _ _
    _ ≤ pi1Image (hLS.trans hVX) (hAPL (left_mem_seg A P))
          ⊔ (pi1Image (hRS.trans hVX) hPR).map _ := sup_le_sup_right (le_of_eq h2) _

end Rigidity.RET

end
