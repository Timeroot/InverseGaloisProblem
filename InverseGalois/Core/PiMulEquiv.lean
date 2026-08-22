/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Isomorphisms of dependent products of groups

Two isomorphisms of dependent products of groups that Mathlib provides for plain types but not for
groups: splitting off the first coordinate of a product indexed by `Fin (n + 1)`, and reindexing a
product along an equivalence of index types.  Both are the underlying equivalence of types together
with the observation that multiplication in a dependent product is pointwise, so the map is a
homomorphism by definition.

They are what turns a statement about one factor at a time into a statement about a finite product
of factors: an induction on `n` peels off `piFinSuccMulEquiv`, and `piCongrLeftMulEquiv` transports
the conclusion from `Fin n` to an arbitrary finite index type.

## Main definitions

* `InverseGalois.piFinSuccMulEquiv`: splitting off the first coordinate.
* `InverseGalois.piCongrLeftMulEquiv`: reindexing along an equivalence.
-/

namespace InverseGalois

/-- Splitting off the first coordinate of a dependent product indexed by `Fin (n + 1)`. -/
def piFinSuccMulEquiv {n : ℕ} (A : Fin (n + 1) → Type*) [∀ i, Group (A i)] :
    (∀ i, A i) ≃* A 0 × ∀ i : Fin n, A i.succ where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv := Fin.cons_self_tail
  right_inv p := Prod.ext (by simp) (by simp)
  map_mul' _ _ := rfl

/-- Reindexing a dependent product of groups along an equivalence of index types. -/
def piCongrLeftMulEquiv {ι ι' : Type*} (A : ι → Type*) [∀ i, Group (A i)] (φ : ι ≃ ι') :
    (∀ i, A i) ≃* ∀ j, A (φ.symm j) where
  __ := Equiv.piCongrLeft' A φ
  map_mul' _ _ := rfl

end InverseGalois
