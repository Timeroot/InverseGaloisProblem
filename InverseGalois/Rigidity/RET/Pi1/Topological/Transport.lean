/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Groupoid.Grpd.Basic

/-!
# Transport of the fundamental group along a homeomorphism

A homotopy equivalence `e : X ≃ₕ Y` — in particular a homeomorphism `e : X ≃ₜ Y` — induces an
isomorphism of fundamental groups `FundamentalGroup X x ≃* FundamentalGroup Y (e x)`.  Mathlib
provides the functorial `FundamentalGroup.map` (a group *homomorphism* induced by a continuous map)
and the equivalence of fundamental groupoids induced by a homotopy equivalence
(`equivOfHomotopyEquiv`), but not the packaged group *isomorphism* at a basepoint.  We assemble it
here: a homotopy equivalence induces an equivalence of fundamental groupoids, whose (fully faithful)
functor carries the endomorphism monoid at `x` isomorphically onto the one at `e x`.

* `ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv` — **homotopy invariance of `π₁`**;
* `Homeomorph.fundamentalGroupMulEquiv` — its specialization to a homeomorphism.

This lets a `π₁` computation on one space be transported to any homotopy-equivalent space — e.g.
from the subtype model `{z : ℂ // z ≠ 0}` to the units `ℂˣ`, or (later) from a punctured plane to a
wedge of circles.
-/

open CategoryTheory

namespace ContinuousMap.HomotopyEquiv

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Homotopy invariance of the fundamental group.**  A homotopy equivalence `e : X ≃ₕ Y` induces a
group isomorphism `FundamentalGroup X x ≃* FundamentalGroup Y (e x)`.  It is the action on
endomorphism monoids of the (fully faithful) functor of the fundamental-groupoid equivalence
attached to `e`. -/
noncomputable def fundamentalGroupMulEquiv (e : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)

end ContinuousMap.HomotopyEquiv

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Transport of `π₁` along a homeomorphism.**  A homeomorphism `e : X ≃ₜ Y` induces a group
isomorphism `FundamentalGroup X x ≃* FundamentalGroup Y (e x)` — the special case of homotopy
invariance for the homotopy equivalence underlying `e`. -/
noncomputable def fundamentalGroupMulEquiv (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  e.toHomotopyEquiv.fundamentalGroupMulEquiv x

end Homeomorph

namespace CategoryTheory.End

/-- **Endomorphisms in a product category split.**  In `C × D`, an endomorphism of `(c, d)` is a
pair of endomorphisms, and composition is componentwise, so `End (c, d) ≃* End c × End d`. -/
@[simps]
def prodMulEquiv {C D : Type*} [Category C] [Category D] (c : C) (d : D) :
    End ((c, d) : C × D) ≃* End c × End d where
  toFun f := (f.1, f.2)
  invFun p := (p.1, p.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- **Endomorphisms in a product (Π-indexed) category split.**  In `∀ i, C i`, an endomorphism of a
point `p` is a family of endomorphisms `∀ i, End (p i)`, with composition taken componentwise, so
`End p ≃* ∀ i, End (p i)`. -/
@[simps]
def piMulEquiv {I : Type*} {C : I → Type*} [∀ i, Category (C i)] (p : ∀ i, C i) :
    End p ≃* ∀ i, End (p i) where
  toFun f i := f i
  invFun g := g
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end CategoryTheory.End

namespace FundamentalGroup

open FundamentalGroupoidFunctor

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The fundamental group of a product splits.**  `π₁(X × Y, (x, y)) ≃* π₁(X, x) × π₁(Y, y)`.
The fundamental groupoid of a product is the product of the fundamental groupoids
(`FundamentalGroupoidFunctor.prodIso`, an isomorphism in `Grpd`); its underlying functor is fully
faithful, carrying the endomorphism monoid at `(x, y)` isomorphically onto the one at the product
object, and endomorphisms in a product category split as a product (`End.prodMulEquiv`). -/
noncomputable def prodMulEquiv (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃* FundamentalGroup X x × FundamentalGroup Y y :=
  (((Cat.equivOfIso (Grpd.forgetToCat.mapIso
      (prodIso (TopCat.of X) (TopCat.of Y)))).fullyFaithfulFunctor.mulEquivEnd
        (FundamentalGroupoid.mk x, FundamentalGroupoid.mk y)).symm).trans
    (CategoryTheory.End.prodMulEquiv (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk y))

section Pi

universe u

variable {I : Type u} (X : I → Type u) [∀ i, TopologicalSpace (X i)]

/-- **The fundamental group of a Π-indexed product splits.**  For a family of spaces `X i` and a
basepoint `x : ∀ i, X i`,
`π₁(∀ i, X i, x) ≃* ∀ i, π₁(X i, x i)`.  This is the arbitrary-arity generalization of
`prodMulEquiv`: the fundamental groupoid functor preserves Π-products
(`FundamentalGroupoidFunctor.piIso`, an isomorphism in `Grpd`), and endomorphisms in a Π-indexed
category split componentwise (`End.piMulEquiv`).  Specializing `I := Fin r` computes the fundamental
group of a finite power such as the `r`-torus. -/
noncomputable def piMulEquiv (x : ∀ i, X i) :
    FundamentalGroup (∀ i, X i) x ≃* ∀ i, FundamentalGroup (X i) (x i) :=
  (((Cat.equivOfIso (Grpd.forgetToCat.mapIso
      (piIso (fun i => TopCat.of (X i))))).fullyFaithfulFunctor.mulEquivEnd
        (fun i => FundamentalGroupoid.mk (x i))).symm).trans
    (CategoryTheory.End.piMulEquiv (fun i => FundamentalGroupoid.mk (x i)))

end Pi

end FundamentalGroup
