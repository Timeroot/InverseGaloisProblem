/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureProd
import InverseGalois.Rigidity.RET.Pi1.Topological.PushLoop
import InverseGalois.Rigidity.RET.Pi1.Topological.MonodromyPath

/-!
# Cutting a boundary loop into products of puncture loops

The cutting calculus of `BoxLoop.lean` says that a quadrilateral cut in two has boundary loop the
product of the boundary loops of the halves, one of them conjugated back to the common basepoint.
This file lifts that identity to the predicate `IsPunctureProd`: if each half is an ordered product
of loops around the punctures it contains, so is the whole, provided the two halves contain
disjoint sets of punctures.

The two ingredients are the dictionary between concatenation of paths and multiplication in the
fundamental group — they are opposite to each other, which merely reverses the order of the
factors — and the fact that conjugating by a segment is transport along that segment, which
`IsPunctureProd` already survives.

## Main results

* `Rigidity.RET.IsPunctureProd.conjSeg` — conjugation by a segment preserves being a product of
  puncture loops.
* `Rigidity.RET.isPunctureProd_boxLoop_rotate` — so does moving the basepoint to the next vertex.
* `Rigidity.RET.isPunctureProd_boxLoop_cut` — the boundary loop of a quadrilateral cut in two is a
  product of puncture loops as soon as both halves are.
-/

open CategoryTheory

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### Concatenation, multiplication and transport -/

variable {Y : Type*} [TopologicalSpace Y]

/-- Reversing a homotopy class of paths twice does nothing. -/
theorem quotient_symm_symm {x y : Y} (P : Path.Homotopic.Quotient x y) : P.symm.symm = P := by
  refine Quotient.inductionOn P fun p => ?_
  exact congrArg Quotient.mk'' (Path.symm_symm p)

/-- Concatenation of loops is multiplication in the fundamental group, in the opposite order. -/
theorem fromPath_trans {x : Y} (P Q : Path.Homotopic.Quotient x x) :
    FundamentalGroup.fromPath (P.trans Q)
      = FundamentalGroup.fromPath Q * FundamentalGroup.fromPath P := rfl

/-- Transport of a loop along a homotopy class of paths, read as a concatenation. -/
theorem transport_fromPath {x y : Y} (q : Path.Homotopic.Quotient x y)
    (V : Path.Homotopic.Quotient x x) :
    FundamentalGroup.transport q (FundamentalGroup.fromPath V)
      = FundamentalGroup.fromPath (q.symm.trans (V.trans q)) := rfl

/-- A product of puncture loops survives transport along a homotopy class of paths. -/
theorem IsPunctureProd.transportQ {X T : Set ℂ} {z₀ z₁ : ℂ} {hz₀ : z₀ ∈ X} {hz₁ : z₁ ∈ X}
    (q : Path.Homotopic.Quotient (⟨z₀, hz₀⟩ : ↥X) ⟨z₁, hz₁⟩)
    {g : FundamentalGroup ↥X ⟨z₀, hz₀⟩} {N : Subgroup (FundamentalGroup ↥X ⟨z₀, hz₀⟩)}
    (h : IsPunctureProd X T hz₀ g N) :
    IsPunctureProd X T hz₁ (FundamentalGroup.transport q g)
      (N.map (FundamentalGroup.transport q).toMonoidHom) := by
  refine Quotient.inductionOn q fun r => ?_
  exact h.transport r

/-- **Conjugating a loop by a segment preserves being a product of puncture loops.** -/
theorem IsPunctureProd.conjSeg {X T : Set ℂ} {a p : ℂ} (hap : seg a p ⊆ X)
    (V : Path.Homotopic.Quotient (⟨p, hap (right_mem_seg _ _)⟩ : ↥X)
      ⟨p, hap (right_mem_seg _ _)⟩)
    {N : Subgroup (FundamentalGroup ↥X ⟨p, hap (right_mem_seg _ _)⟩)}
    (h : IsPunctureProd X T (hap (right_mem_seg _ _)) (FundamentalGroup.fromPath V) N) :
    IsPunctureProd X T (hap (left_mem_seg _ _))
      (FundamentalGroup.fromPath ((segArrow hap).trans (V.trans (segArrow hap).symm)))
      (N.map (FundamentalGroup.transport (segArrow (seg_subset_symm hap))).toMonoidHom) := by
  have key := h.transportQ (segArrow (seg_subset_symm hap))
  have hloop : FundamentalGroup.transport (segArrow (seg_subset_symm hap))
      (FundamentalGroup.fromPath V)
      = FundamentalGroup.fromPath ((segArrow hap).trans (V.trans (segArrow hap).symm)) := by
    rw [transport_fromPath, segArrow_symm hap, quotient_symm_symm]
  rw [hloop] at key
  exact key

/-! ### Rotating and cutting -/

/-- **Moving the basepoint of a boundary loop to the next vertex** preserves being a product of
puncture loops. -/
theorem isPunctureProd_boxLoop_rotate {X T : Set ℂ} {a b c d : ℂ}
    (hab : seg a b ⊆ X) (hbc : seg b c ⊆ X) (hcd : seg c d ⊆ X) (hda : seg d a ⊆ X)
    {N : Subgroup (FundamentalGroup ↥X ⟨b, hbc (left_mem_seg _ _)⟩)}
    (h : IsPunctureProd X T (hbc (left_mem_seg _ _))
      (FundamentalGroup.fromPath (boxLoop hbc hcd hda hab)) N) :
    IsPunctureProd X T (hab (left_mem_seg _ _))
      (FundamentalGroup.fromPath (boxLoop hab hbc hcd hda))
      (N.map (FundamentalGroup.transport (segArrow (seg_subset_symm hab))).toMonoidHom) := by
  rw [boxLoop_rotate]
  exact IsPunctureProd.conjSeg hab _ h

/-- **Moving the basepoint of a boundary loop to the previous vertex** preserves being a product
of puncture loops. -/
theorem isPunctureProd_boxLoop_rotate' {X T : Set ℂ} {a b c d : ℂ}
    (hab : seg a b ⊆ X) (hbc : seg b c ⊆ X) (hcd : seg c d ⊆ X) (hda : seg d a ⊆ X)
    {N : Subgroup (FundamentalGroup ↥X ⟨a, hab (left_mem_seg _ _)⟩)}
    (h : IsPunctureProd X T (hab (left_mem_seg _ _))
      (FundamentalGroup.fromPath (boxLoop hab hbc hcd hda)) N) :
    IsPunctureProd X T (hbc (left_mem_seg _ _))
      (FundamentalGroup.fromPath (boxLoop hbc hcd hda hab))
      (((N.map (FundamentalGroup.transport (segArrow (seg_subset_symm hda))).toMonoidHom).map
          (FundamentalGroup.transport (segArrow (seg_subset_symm hcd))).toMonoidHom).map
        (FundamentalGroup.transport (segArrow (seg_subset_symm hbc))).toMonoidHom) :=
  isPunctureProd_boxLoop_rotate hbc hcd hda hab
    (isPunctureProd_boxLoop_rotate hcd hda hab hbc
      (isPunctureProd_boxLoop_rotate hda hab hbc hcd h))

/-- **A quadrilateral cut in two has boundary loop the product of the boundary loops of the
halves**, as products of puncture loops around the punctures of each half. -/
theorem isPunctureProd_boxLoop_cut {X T₁ T₂ : Set ℂ} {a b c d p q : ℂ}
    (hab : seg a b ⊆ X) (hbc : seg b c ⊆ X) (hcd : seg c d ⊆ X) (hda : seg d a ⊆ X)
    (hp : p ∈ seg a b) (hq : q ∈ seg c d) (hpq : seg p q ⊆ X)
    {N₁ : Subgroup (FundamentalGroup ↥X ⟨a, hab (left_mem_seg _ _)⟩)}
    {N₂ : Subgroup (FundamentalGroup ↥X ⟨p, ((seg_subset_left hp).trans hab)
      (right_mem_seg _ _)⟩)}
    (hL : IsPunctureProd X T₁ (((seg_subset_left hp).trans hab) (left_mem_seg _ _))
      (FundamentalGroup.fromPath (boxLoop ((seg_subset_left hp).trans hab) hpq
          ((seg_subset_right hq).trans hcd) hda)) N₁)
    (hR : IsPunctureProd X T₂ (((seg_subset_right hp).trans hab) (left_mem_seg _ _))
      (FundamentalGroup.fromPath (boxLoop ((seg_subset_right hp).trans hab) hbc
          ((seg_subset_left hq).trans hcd) (seg_subset_symm hpq))) N₂)
    (hdisj : Disjoint T₁ T₂) :
    IsPunctureProd X (T₁ ∪ T₂) (hab (left_mem_seg _ _))
      (FundamentalGroup.fromPath (boxLoop hab hbc hcd hda))
      (N₁ ⊔ N₂.map (FundamentalGroup.transport
        (segArrow (seg_subset_symm ((seg_subset_left hp).trans hab)))).toMonoidHom) := by
  have hap : seg a p ⊆ X := (seg_subset_left hp).trans hab
  have hRc := IsPunctureProd.conjSeg hap _ hR
  rw [boxLoop_cut hab hbc hcd hda hp hq hpq, fromPath_trans]
  exact hL.mul hRc hdisj

end Rigidity.RET

end
