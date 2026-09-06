/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Product

/-!
# The complete cohomology of a product of two representations

A product of two representations is a product of a family indexed by the two booleans, so the
complete cohomology of a product of two representations is the product of their complete
cohomologies in every integer degree.  This file records that specialisation, together with the
identification of a function on the booleans with a pair, so that the general statement about
products can be used where a module is visibly built from two halves.

The arithmetic case is the group of ideles of a number field, which is a product of the local
factors at the infinite places and the local factors at the finite ones; the two halves are indexed
by different sets and are treated by the same argument, but the cohomology of the whole group is
only the product of the two contributions once this specialisation is available.

## Main definitions

* `InverseGalois.CFT.Tate.pairFamily`: the family indexed by the booleans with two given members.
* `InverseGalois.CFT.Tate.pairRep`: **the product of two representations.**
* `InverseGalois.CFT.Tate.piBoolEquiv`: a function on the booleans is a pair.

## Main results

* `InverseGalois.CFT.Tate.tatePairEquiv`: **the complete cohomology of a product of two
  representations is the product of their complete cohomologies**, in every integer degree.
* `InverseGalois.CFT.Tate.isZero_tateModule_pairRep`: a product of two representations without
  complete cohomology in a degree has none either.

## Tags

Tate cohomology, product, pair, idele
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory

noncomputable section

variable {k G : Type} [CommRing k] [Group G]

/-! ### A pair as a family indexed by the booleans -/

/-- A function on the booleans is a pair. -/
def piBoolEquiv {V : Bool → Type*} [∀ b, AddCommGroup (V b)] :
    (∀ b, V b) ≃+ V true × V false where
  toFun f := (f true, f false)
  invFun p := fun b => Bool.rec p.2 p.1 b
  left_inv _ := funext fun b => by cases b <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The family indexed by the booleans with two given members. -/
def pairFamily (A B : Rep k G) : Bool → Rep k G := fun b => cond b A B

@[simp]
theorem pairFamily_true (A B : Rep k G) : pairFamily A B true = A := rfl

@[simp]
theorem pairFamily_false (A B : Rep k G) : pairFamily A B false = B := rfl

/-- **The product of two representations.** -/
def pairRep (A B : Rep k G) : Rep k G := piRep (pairFamily A B)

@[simp]
theorem pairRep_ρ_apply (A B : Rep k G) (g : G) (x : ∀ b, ↥(pairFamily A B b).V) (b : Bool) :
    (pairRep A B).ρ g x b = (pairFamily A B b).ρ g (x b) := rfl

/-! ### The complete cohomology -/

variable [Finite G]

/-- **The complete cohomology of a product of two representations is the product of their complete
cohomologies**, in every integer degree. -/
def tatePairEquiv (A B : Rep k G) (n : ℤ) :
    ↥(tateModule (pairRep A B) n) ≃+ ↥(tateModule A n) × ↥(tateModule B n) :=
  let e := tatePiEquiv (pairFamily A B) n
  AddEquiv.trans { toEquiv := e.toEquiv, map_add' := e.map_add } piBoolEquiv

/-- **A product of two representations without complete cohomology in a degree has none either.** -/
theorem isZero_tateModule_pairRep (A B : Rep k G) (n : ℤ)
    (hA : Limits.IsZero (tateModule A n)) (hB : Limits.IsZero (tateModule B n)) :
    Limits.IsZero (tateModule (pairRep A B) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : Subsingleton ↥(tateModule A n) := ModuleCat.isZero_iff_subsingleton.1 hA
  haveI : Subsingleton ↥(tateModule B n) := ModuleCat.isZero_iff_subsingleton.1 hB
  exact (tatePairEquiv A B n).injective.subsingleton

end

end InverseGalois.CFT.Tate
