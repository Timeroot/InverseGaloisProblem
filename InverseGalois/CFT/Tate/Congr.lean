/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Herbrand

/-!
# Transport of the Tate groups along an equivariant isomorphism

Two modules that are isomorphic by a map commuting with the two automorphisms have the same Tate
groups.  The isomorphism carries fixed points to fixed points and norms to norms, so the maps
induced on the Tate groups by it and by its inverse are mutually inverse.

This is the last piece of bookkeeping needed to use the computations of the Tate groups of a
product, of a finite family and of an induced module: a module met in practice is rarely presented
in one of those shapes on the nose, and what one has instead is an isomorphism onto such a shape.

## Main definitions

* `InverseGalois.CFT.tateH0Congr`, `InverseGalois.CFT.tateHm1Congr`: the Tate groups of isomorphic
  modules are isomorphic.

## Main results

* `InverseGalois.CFT.herbrand_congr`: **the Herbrand quotient only depends on the isomorphism class
  of a module with an automorphism.**

## Tags

Tate cohomology, Herbrand quotient, transport
-/

namespace InverseGalois.CFT

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {σA : A ≃+ A} {σB : B ≃+ B}

/-! ### Two elementary remarks -/

/-- The inverse of an equivariant isomorphism is equivariant. -/
theorem symm_equivariant (e : A ≃+ B) (he : ∀ a, e (σA a) = σB (e a)) (b : B) :
    e.symm (σB b) = σA (e.symm b) := by
  refine e.injective ?_
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- Equal fixed points have equal classes in `Ĥ⁰`. -/
theorem tateH0.mk_congr (n : ℕ) {x y : A} (hx : σA x = x) (hy : σA y = y) (h : x = y) :
    tateH0.mk σA n x hx = tateH0.mk σA n y hy := by
  subst h
  rfl

/-- Equal elements of norm zero have equal classes in `Ĥ⁻¹`. -/
theorem tateHm1.mk_congr (n : ℕ) {x y : A} (hx : normHom σA n x = 0) (hy : normHom σA n y = 0)
    (h : x = y) : tateHm1.mk σA n x hx = tateHm1.mk σA n y hy := by
  subst h
  rfl

/-! ### The upper Tate group -/

variable (e : A ≃+ B) (he : ∀ a, e (σA a) = σB (e a)) (n : ℕ)

/-- **Isomorphic modules have isomorphic upper Tate groups.** -/
def tateH0Congr : tateH0 σA n ≃+ tateH0 σB n where
  toFun := tateH0.map n e.toAddMonoidHom he
  invFun := tateH0.map n e.symm.toAddMonoidHom (symm_equivariant e he)
  left_inv c := by
    obtain ⟨x, hx, rfl⟩ := tateH0.mk_surjective c
    rw [tateH0.map_mk, tateH0.map_mk]
    exact tateH0.mk_congr n _ _ (e.symm_apply_apply x)
  right_inv d := by
    obtain ⟨y, hy, rfl⟩ := tateH0.mk_surjective d
    rw [tateH0.map_mk, tateH0.map_mk]
    exact tateH0.mk_congr n _ _ (e.apply_symm_apply y)
  map_add' _ _ := map_add _ _ _

theorem tateH0Congr_mk (x : A) (hx : σA x = x) :
    tateH0Congr e he n (tateH0.mk σA n x hx) = tateH0.mk σB n (e x) (by rw [← he, hx]) := rfl

include e he in
/-- The orders of the upper Tate groups of isomorphic modules agree. -/
theorem card_tateH0_congr : Nat.card (tateH0 σA n) = Nat.card (tateH0 σB n) :=
  Nat.card_congr (tateH0Congr e he n).toEquiv

/-! ### The lower Tate group -/

/-- **Isomorphic modules have isomorphic lower Tate groups.** -/
noncomputable def tateHm1Congr : tateHm1 σA n ≃+ tateHm1 σB n where
  toFun := tateHm1.map n e.toAddMonoidHom he
  invFun := tateHm1.map n e.symm.toAddMonoidHom (symm_equivariant e he)
  left_inv c := by
    obtain ⟨x, hx, rfl⟩ := tateHm1.mk_surjective c
    rw [tateHm1.map_mk, tateHm1.map_mk]
    exact tateHm1.mk_congr n _ _ (e.symm_apply_apply x)
  right_inv d := by
    obtain ⟨y, hy, rfl⟩ := tateHm1.mk_surjective d
    rw [tateHm1.map_mk, tateHm1.map_mk]
    exact tateHm1.mk_congr n _ _ (e.apply_symm_apply y)
  map_add' _ _ := map_add _ _ _

theorem tateHm1Congr_mk (x : A) (hx : normHom σA n x = 0) (hex : normHom σB n (e x) = 0) :
    tateHm1Congr e he n (tateHm1.mk σA n x hx) = tateHm1.mk σB n (e x) hex := rfl

include e he in
/-- The orders of the lower Tate groups of isomorphic modules agree. -/
theorem card_tateHm1_congr : Nat.card (tateHm1 σA n) = Nat.card (tateHm1 σB n) :=
  Nat.card_congr (tateHm1Congr e he n).toEquiv

/-! ### The Herbrand quotient -/

include e he in
/-- **The Herbrand quotient only depends on the isomorphism class of a module with an
automorphism.** -/
theorem herbrand_congr : herbrand σA n = herbrand σB n := by
  rw [herbrand, herbrand, card_tateH0_congr e he n, card_tateHm1_congr e he n]

end InverseGalois.CFT
