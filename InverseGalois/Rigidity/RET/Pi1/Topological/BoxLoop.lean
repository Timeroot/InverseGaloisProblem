/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.ConvexHomotopy

/-!
# Boundary loops of quadrilaterals

A quadrilateral of the plane whose four sides lie inside a region `X` has a boundary loop in `X`,
obtained by running once along the sides.  This file sets up the calculus of such loops in the
fundamental groupoid of `X`.

The building block is the *segment arrow*, the homotopy class of the straight path along a segment
contained in the region.  Cutting a segment at an interior point splits its arrow in two, and
reversing a segment reverses its arrow; from these, three facts about boundary loops follow.

The boundary loop may be based at any vertex, the change of basepoint being a conjugation by the
side joining the two vertices.  A segment joining a point of one side to a point of the opposite
side cuts the quadrilateral into two, and the boundary loop becomes the product of the two boundary
loops, one of them conjugated so that both are based at the original vertex.  Finally, a
quadrilateral whose vertices lie in a convex subset of the region has nullhomotopic boundary loop.

Together these let one chop a large quadrilateral into small ones and read off the boundary loop of
the large one as a product of conjugates of the small ones.

## Main results

* `Rigidity.RET.segArrow` — the class of the straight path along a segment of the region, with
  `Rigidity.RET.segArrow_trans`, `Rigidity.RET.segArrow_symm` and `Rigidity.RET.segArrow_self`.
* `Rigidity.RET.boxLoop` — the boundary loop of a quadrilateral, based at its first vertex.
* `Rigidity.RET.boxLoop_rotate` — moving the basepoint to the next vertex conjugates the loop.
* `Rigidity.RET.boxLoop_cut` — a cut between opposite sides splits the boundary loop in two.
* `Rigidity.RET.boxLoop_eq_refl` — a quadrilateral with vertices in a convex subset has trivial
  boundary loop.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

variable {X : Set ℂ}

/-! ### Paths running inside a subset -/

/-- A concatenation of two paths staying inside a set stays inside that set. -/
theorem mem_of_trans {K : Set ℂ} {x y z : ↥X} {P : Path x y} {Q : Path y z}
    (hP : ∀ t, ((P t : ↥X) : ℂ) ∈ K) (hQ : ∀ t, ((Q t : ↥X) : ℂ) ∈ K) (t : I) :
    ((P.trans Q t : ↥X) : ℂ) ∈ K := by
  have hmem : P.trans Q t ∈ Set.range (P.trans Q) := ⟨t, rfl⟩
  rw [Path.trans_range] at hmem
  rcases hmem with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact hu ▸ hP u
  · exact hu ▸ hQ u

/-! ### Segment arrows -/

/-- The class of the straight path between two points of a region of the plane. -/
def segArrow {X : Set ℂ} {a b : ℂ} (h : seg a b ⊆ X) :
    Path.Homotopic.Quotient (⟨a, h (left_mem_seg a b)⟩ : ↥X) ⟨b, h (right_mem_seg a b)⟩ :=
  Path.Homotopic.Quotient.mk (segPath _ _ h)

/-- A segment lies in a region exactly when the reversed segment does. -/
theorem seg_subset_symm {a b : ℂ} (h : seg a b ⊆ X) : seg b a ⊆ X := by
  rw [seg_symm]; exact h

/-- **Concatenating the two halves of a segment gives the segment.** -/
theorem segArrow_trans {a b c : ℂ} (hb : b ∈ seg a c) (hac : seg a c ⊆ X)
    (hab : seg a b ⊆ X) (hbc : seg b c ⊆ X) :
    (segArrow hab).trans (segArrow hbc) = segArrow hac := by
  rw [segArrow, segArrow, segArrow, ← Path.Homotopic.Quotient.mk_trans]
  refine Quotient.sound ?_
  refine homotopic_of_mem_convex (isSegClosed_seg a c) hac _ _ (fun t => ?_) (fun t => ?_)
  · exact mem_of_trans (fun u => seg_subset_left hb (mem_seg_segPath hab u))
      (fun u => seg_subset_right hb (mem_seg_segPath hbc u)) t
  · exact mem_seg_segPath hac t

/-- **A segment traversed backwards is the reverse of the segment.** -/
theorem segArrow_symm {a b : ℂ} (hab : seg a b ⊆ X) :
    segArrow (seg_subset_symm hab) = (segArrow hab).symm := by
  rw [segArrow, segArrow, ← Path.Homotopic.Quotient.mk_symm]
  refine Quotient.sound ?_
  refine homotopic_of_mem_convex (isSegClosed_seg a b) hab _ _ (fun t => ?_) (fun t => ?_)
  · rw [seg_symm]
    exact mem_seg_segPath (seg_subset_symm hab) t
  · exact mem_seg_segPath hab _

/-- **A constant segment is trivial.** -/
theorem segArrow_self {a : ℂ} (h : seg a a ⊆ X) :
    segArrow h = Path.Homotopic.Quotient.refl _ :=
  Quotient.sound (homotopic_refl_of_mem_convex (isSegClosed_seg a a) h _
    fun t => mem_seg_segPath h t)

/-! ### Cancellation in the fundamental groupoid -/

variable {Y : Type*} [TopologicalSpace Y]

/-- A path followed by its reverse cancels out of a longer composite. -/
theorem trans_symm_trans {x y z : Y} (f : Path.Homotopic.Quotient x y)
    (k : Path.Homotopic.Quotient x z) : f.trans (f.symm.trans k) = k := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

/-- The reverse of a path followed by the path cancels out of a longer composite. -/
theorem symm_trans_trans {x y z : Y} (f : Path.Homotopic.Quotient y x)
    (k : Path.Homotopic.Quotient x z) : f.symm.trans (f.trans k) = k := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-! ### The boundary loop of a quadrilateral -/

/-- The loop running once along the four sides of a quadrilateral of the plane, starting at its
first vertex. -/
def boxLoop {X : Set ℂ} {a b c d : ℂ} (hab : seg a b ⊆ X) (hbc : seg b c ⊆ X)
    (hcd : seg c d ⊆ X) (hda : seg d a ⊆ X) :
    Path.Homotopic.Quotient (⟨a, hab (left_mem_seg a b)⟩ : ↥X)
      ⟨a, hab (left_mem_seg a b)⟩ :=
  ((segArrow hab).trans (segArrow hbc)).trans ((segArrow hcd).trans (segArrow hda))

/-- **The starting vertex of a boundary loop may be moved to the next one**, at the cost of
conjugating by the side joining them. -/
theorem boxLoop_rotate {a b c d : ℂ} (hab : seg a b ⊆ X) (hbc : seg b c ⊆ X)
    (hcd : seg c d ⊆ X) (hda : seg d a ⊆ X) :
    boxLoop hab hbc hcd hda
      = (segArrow hab).trans ((boxLoop hbc hcd hda hab).trans (segArrow hab).symm) := by
  simp only [boxLoop, Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]

/-- **Cutting a quadrilateral in two.**  A segment joining a point of the first side to a point of
the third side splits the boundary loop into the boundary loops of the two halves, the far one
conjugated by the initial piece of the first side. -/
theorem boxLoop_cut {a b c d p q : ℂ} (hab : seg a b ⊆ X) (hbc : seg b c ⊆ X)
    (hcd : seg c d ⊆ X) (hda : seg d a ⊆ X) (hp : p ∈ seg a b) (hq : q ∈ seg c d)
    (hpq : seg p q ⊆ X) :
    boxLoop hab hbc hcd hda
      = ((segArrow ((seg_subset_left hp).trans hab)).trans
          ((boxLoop ((seg_subset_right hp).trans hab) hbc
              ((seg_subset_left hq).trans hcd) (seg_subset_symm hpq)).trans
            (segArrow ((seg_subset_left hp).trans hab)).symm)).trans
        (boxLoop ((seg_subset_left hp).trans hab) hpq
          ((seg_subset_right hq).trans hcd) hda) := by
  have hap : seg a p ⊆ X := (seg_subset_left hp).trans hab
  have hpb : seg p b ⊆ X := (seg_subset_right hp).trans hab
  have hcq : seg c q ⊆ X := (seg_subset_left hq).trans hcd
  have hqd : seg q d ⊆ X := (seg_subset_right hq).trans hcd
  have h1 : (segArrow hap).trans (segArrow hpb) = segArrow hab := segArrow_trans hp hab hap hpb
  have h2 : (segArrow hcq).trans (segArrow hqd) = segArrow hcd := segArrow_trans hq hcd hcq hqd
  simp only [boxLoop, Path.Homotopic.Quotient.trans_assoc]
  rw [segArrow_symm hpq, symm_trans_trans (segArrow hap), symm_trans_trans (segArrow hpq),
    ← Path.Homotopic.Quotient.trans_assoc (segArrow hap) (segArrow hpb), h1,
    ← Path.Homotopic.Quotient.trans_assoc (segArrow hcq) (segArrow hqd), h2]

/-- **The boundary loop of a quadrilateral contained in a convex subset is trivial.** -/
theorem boxLoop_eq_refl {K : Set ℂ} (hK : IsSegClosed K) (hKX : K ⊆ X)
    {a b c d : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K)
    (hab : seg a b ⊆ X) (hbc : seg b c ⊆ X) (hcd : seg c d ⊆ X) (hda : seg d a ⊆ X) :
    boxLoop hab hbc hcd hda = Path.Homotopic.Quotient.refl _ := by
  simp only [boxLoop, segArrow, ← Path.Homotopic.Quotient.mk_trans]
  refine Quotient.sound (homotopic_refl_of_mem_convex hK hKX _ fun t => ?_)
  exact mem_of_trans (mem_of_trans (fun u => hK a ha b hb (mem_seg_segPath hab u))
    (fun u => hK b hb c hc (mem_seg_segPath hbc u)))
    (mem_of_trans (fun u => hK c hc d hd (mem_seg_segPath hcd u))
      (fun u => hK d hd a ha (mem_seg_segPath hda u))) t

end Rigidity.RET

end
