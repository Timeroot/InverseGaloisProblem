/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Pair
import InverseGalois.CFT.TateCohomology.TensorPi

/-!
# A product of two representations tensored with coefficients over a prime field

A product of two representations is a product of a family indexed by the two booleans, so
everything proved about tensoring an arbitrary product with coefficients of finite rank over a
prime field applies to it.  What comes out is the statement in the form a module visibly built from
two halves needs: **the complete cohomology of a product of two representations killed by a prime,
tensored with coefficients of finite rank over the field with that many elements, is the product of
the complete cohomologies of the two factors tensored with the coefficients.**

The group of ideles is such a module: it is the infinite places and the finite ones.

## Main results

* `InverseGalois.CFT.Tate.tateTensorPairEquiv`: **the complete cohomology of a product of two
  representations tensored with the coefficients is the product of the two.**

## Tags

Tate cohomology, tensor product, prime field
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory

noncomputable section

variable {G : Type} [Group G] [Finite G] (A B W : Rep ℤ G) {p d : ℕ} [Fact p.Prime]
  (e : ↥W.V ≃+ (Fin d → ZMod p)) (hA : ∀ m : ↥A.V, p • m = 0) (hB : ∀ m : ↥B.V, p • m = 0)

omit [Finite G] [Fact p.Prime] in
include hA hB in
/-- Both members of a pair of representations killed by a number are killed by it. -/
theorem nsmul_eq_zero_pairFamily (b : Bool) (m : ↥(pairFamily A B b).V) : p • m = 0 := by
  cases b
  · exact hB m
  · exact hA m

include e hA hB in
/-- **The complete cohomology of a product of two representations killed by a prime, tensored with
coefficients of finite rank over the field with that many elements, is the product of the complete
cohomologies of the two factors tensored with the coefficients.** -/
def tateTensorPairEquiv (n : ℤ) :
    ↥(tateModule (tensorObj (pairRep A B) W) n) ≃+
      ↥(tateModule (tensorObj A W) n) × ↥(tateModule (tensorObj B W) n) :=
  let e₁ := tatePiEquiv (fun b => tensorObj (pairFamily A B b) W) n
  ((tateMapIso (tensorPiIso (pairFamily A B) W e
      (nsmul_eq_zero_pairFamily A B hA hB)) n).toLinearEquiv.toAddEquiv).trans <|
    AddEquiv.trans { toEquiv := e₁.toEquiv, map_add' := e₁.map_add } piBoolEquiv

end

end InverseGalois.CFT.Tate
