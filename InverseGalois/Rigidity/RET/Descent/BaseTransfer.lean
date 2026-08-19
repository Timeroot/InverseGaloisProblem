/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Statement

/-!
# Changing the presentation of the base field

`IsRegularGaloisGroupOverBase k F G` is stated for an abstract base `F / k` precisely so that the
base may arrive in whatever form a construction produces it — in the arithmetic descent it arrives
as an *intermediate field* `K(T)` of a tower `Ω / ℚ(T)`, while the recognizable conclusion
`IsRegularGaloisGroupOver K G` wants the base to be the standard model `RatFunc K`.

This file supplies the bridge: the predicate only depends on the `k`-isomorphism class of the base.
Transporting the realization `L / F` along `e : F ≃ₐ[k] F'` means giving `L` the `F'`-algebra
structure `algebraMap F L ∘ e.symm`.  Everything then follows from `F' → F` being an isomorphism:
`[F : F'] = 1`, so the degrees agree, and the two automorphism groups of `L` coincide as sets of
ring equivalences, so the Galois criterion `|Aut(L/F')| = [L : F']` holds and the group is still
`G`.  The constant field `k` and its action on `L` are untouched, so regularity is unchanged.

## Main result

* `IsRegularGaloisGroupOverBase.of_algEquiv`
-/

open Polynomial Module

namespace IsRegularGaloisGroupOverBase

variable {k : Type*} [Field k] {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
  {G : Type*} [Group G]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The base may be replaced by any `k`-isomorphic field.**

A regular realization of `G` over `F / k` is a regular realization over `F' / k` for every
`k`-isomorphic `F'`.  This is what lets a base produced as a subfield of a tower be recognized as
the standard rational function field. -/
theorem of_algEquiv (h : IsRegularGaloisGroupOverBase k F G) (e : F ≃ₐ[k] F') :
    IsRegularGaloisGroupOverBase k F' G := by
  obtain ⟨L, hLf, hAFL, hFD, hGal, hAkL, hST, hreg, ⟨φ⟩⟩ := h
  letI := hLf
  letI := hAFL
  letI := hFD
  letI := hGal
  letI := hAkL
  letI := hST
  -- `F'` acts on `F` and on `L` through `e.symm`.
  letI : Algebra F' F := e.symm.toAlgHom.toRingHom.toAlgebra
  letI : Algebra F' L := ((algebraMap F L).comp e.symm.toAlgHom.toRingHom).toAlgebra
  haveI : IsScalarTower F' F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k F' L := by
    refine IsScalarTower.of_algebraMap_eq fun q => ?_
    show algebraMap k L q = algebraMap F L (e.symm (algebraMap k F' q))
    rw [AlgEquiv.commutes]
    exact IsScalarTower.algebraMap_apply k F L q
  -- `F` is a one-dimensional `F'`-vector space, so the degrees over `F` and over `F'` agree.
  have hlin : Function.Bijective (Algebra.linearMap F' F) :=
    ⟨e.symm.injective, e.symm.surjective⟩
  haveI : Module.Finite F' F :=
    Module.Finite.of_surjective (Algebra.linearMap F' F) hlin.2
  haveI : FiniteDimensional F' L := Module.Finite.trans (R := F') F L
  have hrk1 : finrank F' F = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap F' F) hlin).finrank_eq, finrank_self]
  have hfr : finrank F' L = finrank F L := by
    rw [← finrank_mul_finrank F' F L, hrk1, one_mul]
  -- An `F`-automorphism of `L` is the same ring equivalence as an `F'`-automorphism.
  let ee : (L ≃ₐ[F] L) ≃* (L ≃ₐ[F'] L) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (R := F') (f := σ.toRingEquiv) fun x =>
        σ.commutes (e.symm x)
      invFun := fun σ => AlgEquiv.ofRingEquiv (R := F) (f := σ.toRingEquiv) fun x => by
        have hx : algebraMap F' L (e x) = algebraMap F L x := by
          show algebraMap F L (e.symm (e x)) = _
          rw [AlgEquiv.symm_apply_apply]
        have := σ.commutes (e x)
        rwa [hx] at this
      left_inv := fun σ => by ext x; rfl
      right_inv := fun σ => by ext x; rfl
      map_mul' := fun σ τ => by ext x; rfl }
  haveI : IsGalois F' L :=
    IsGalois.of_card_aut_eq_finrank F' L
      (by rw [Nat.card_congr ee.symm.toEquiv, IsGalois.card_aut_eq_finrank F L, hfr])
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hreg, ⟨ee.symm.trans φ⟩⟩

end IsRegularGaloisGroupOverBase
