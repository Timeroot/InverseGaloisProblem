/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.BoxLoop
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureFill

/-!
# Pushing a boundary loop into a larger region

A `boxLoop` is built out of straight segments, and a straight segment of a region of the plane is
still a straight segment of any larger region.  So the loop transported along an inclusion of
regions is again a `boxLoop`, with the very same corners: nothing has to be computed.

The file also records the corresponding statements one level down, for the quotient of paths, and
the fact that transporting a loop along the constant path does nothing.

## Main results

* `Rigidity.RET.quotientMap_trans` — a continuous map sends a concatenation of homotopy classes of
  paths to the concatenation of the images.
* `Rigidity.RET.map_boxLoop` — the boundary loop of a box, read in a larger region, is the boundary
  loop of the same box.
* `Rigidity.RET.fundamentalGroupMulEquivOfPath_refl` — transport along the constant path is the
  identity.
-/

open CategoryTheory

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### Continuous maps and the quotient of paths -/

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-- A continuous map sends a concatenation of homotopy classes of paths to the concatenation of
the images. -/
theorem quotientMap_trans {x y z : Y} (P : Path.Homotopic.Quotient x y)
    (Q : Path.Homotopic.Quotient y z) (f : C(Y, Z)) :
    (P.trans Q).map f = (P.map f).trans (Q.map f) := by
  refine Quotient.inductionOn₂ P Q fun p q => ?_
  exact congrArg Quotient.mk'' (p.map_trans q f.continuous)

/-- A continuous map sends the reverse of a homotopy class of paths to the reverse of the image. -/
theorem quotientMap_symm {x y : Y} (P : Path.Homotopic.Quotient x y) (f : C(Y, Z)) :
    P.symm.map f = (P.map f).symm := by
  refine Quotient.inductionOn P fun p => ?_
  exact congrArg Quotient.mk'' (p.map_symm f.continuous)

/-- Transport along the constant path is the identity. -/
theorem fundamentalGroupMulEquivOfPath_refl (x : Y) (g : FundamentalGroup Y x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (Path.refl x) g = g := by
  have hiso : ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x)).symm
      (⟦Path.refl x⟧ : Path.Homotopic.Quotient x x)) = Iso.refl _ := Iso.ext rfl
  show ((Groupoid.isoEquivHom _ _).symm (⟦Path.refl x⟧ : Path.Homotopic.Quotient x x)).conj g = g
  rw [hiso, Iso.refl_conj]

/-! ### Segments and boxes in a larger region -/

/-- A segment of a region of the plane, read in a larger region. -/
theorem map_segArrow {X X' : Set ℂ} (hsub : X ⊆ X') {a b : ℂ} (h : seg a b ⊆ X) :
    (segArrow h).map (subsetIncl hsub) = segArrow (h.trans hsub) := rfl

/-- The boundary loop of a box, read in a larger region, is the boundary loop of the same box. -/
theorem map_boxLoop {X X' : Set ℂ} (hsub : X ⊆ X') {a b c d : ℂ}
    (hab : seg a b ⊆ X) (hbc : seg b c ⊆ X) (hcd : seg c d ⊆ X) (hda : seg d a ⊆ X) :
    (boxLoop hab hbc hcd hda).map (subsetIncl hsub)
      = boxLoop (hab.trans hsub) (hbc.trans hsub) (hcd.trans hsub) (hda.trans hsub) := by
  simp only [boxLoop, quotientMap_trans, map_segArrow]

/-- The inclusion of a punctured disc in a region is the inclusion of a subset. -/
theorem discIncl_eq_subsetIncl {X : Set ℂ} {s : ℂ} {ρ : ℝ} (h : puncturedDisc s ρ ⊆ X) :
    discIncl h = subsetIncl h := rfl

/-- The map on fundamental groups induced by an inclusion of regions, read on a loop. -/
theorem fundamentalGroup_map_eq {X X' : Set ℂ} (hsub : X ⊆ X') (x : ↥X)
    (g : Path.Homotopic.Quotient x x) :
    FundamentalGroup.map (subsetIncl hsub) x (FundamentalGroup.fromPath g)
      = FundamentalGroup.fromPath (g.map (subsetIncl hsub)) := rfl

end Rigidity.RET

end
