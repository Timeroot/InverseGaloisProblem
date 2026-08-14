/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Rigidity.RET.GeometricIrreducibility
import InverseGalois.Rigidity.RET.RegularCriterion
import InverseGalois.Rigidity.RET.Statement

/-!
# Changing the base field along an isomorphism

A finite Galois extension is usually produced over the base field where it naturally lives, while
`IsRegularInverseGalois` insists on the base field `ℚ(T)` on the nose.  The two are reconciled by
an isomorphism of base fields, and this file records what such an isomorphism preserves.

Everything is phrased for a tower `K₁ → K₂ → L` whose lower step is onto: the two base fields are
then the same field seen twice, so the `K₁`- and `K₂`-structures on `L` agree.  Dimensions agree
because the lower step has degree one, and an automorphism of `L` fixing `K₂` pointwise fixes `K₁`
pointwise and conversely, because every element of `K₂` is the image of one of `K₁`.

The application is `IsRegularInverseGalois.of_ratFunc_ext`: a finite Galois extension of a
subfield `M ⊆ ℚ(T)` which happens to be isomorphic to `ℚ(T)` is, after the transport, a regular
realization of its Galois group.

## Main results

* `Rigidity.RET.finiteDimensional_of_surjective`, `Rigidity.RET.finrank_eq_of_surjective`,
  `Rigidity.RET.autCongrOfSurjective`, `Rigidity.RET.isGalois_of_surjective` — the transport.
* `IsRegularInverseGalois.of_ratFunc_ext` — a Galois extension of a rational subfield of `ℚ(T)`
  is a regular realization.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

section Transport

variable {K₁ K₂ L : Type*} [Field K₁] [Field K₂] [Field L] [Algebra K₁ K₂] [Algebra K₂ L]
  [Algebra K₁ L] [IsScalarTower K₁ K₂ L]

/-- A field extension whose structure map is onto has degree one. -/
theorem finrank_base_eq_one_of_surjective (h : Function.Surjective (algebraMap K₁ K₂)) :
    Module.finrank K₁ K₂ = 1 := by
  have e : K₁ ≃ₗ[K₁] K₂ :=
    LinearEquiv.ofBijective (Algebra.linearMap K₁ K₂) ⟨(algebraMap K₁ K₂).injective, h⟩
  rw [← e.finrank_eq, Module.finrank_self]

/-- Finiteness passes to a base field mapping onto the old one. -/
theorem finiteDimensional_of_surjective (h : Function.Surjective (algebraMap K₁ K₂))
    [FiniteDimensional K₂ L] : FiniteDimensional K₁ L := by
  haveI : FiniteDimensional K₁ K₂ := Module.Finite.of_surjective (Algebra.linearMap K₁ K₂) h
  exact FiniteDimensional.trans K₁ K₂ L

/-- The degree is unchanged by a base field mapping onto the old one. -/
theorem finrank_eq_of_surjective (h : Function.Surjective (algebraMap K₁ K₂)) :
    Module.finrank K₁ L = Module.finrank K₂ L := by
  rw [← Module.finrank_mul_finrank K₁ K₂ L, finrank_base_eq_one_of_surjective h, one_mul]

/-- **Automorphisms do not see the difference between the two base fields.**  Fixing `K₂`
pointwise implies fixing `K₁` pointwise because `K₁` maps into `K₂`, and conversely because that
map is onto. -/
def autCongrOfSurjective (h : Function.Surjective (algebraMap K₁ K₂)) :
    (L ≃ₐ[K₂] L) ≃* (L ≃ₐ[K₁] L) where
  toFun φ := AlgEquiv.ofRingEquiv (f := φ.toRingEquiv) (fun x => by
    rw [IsScalarTower.algebraMap_apply K₁ K₂ L]; exact φ.commutes _)
  invFun ψ := AlgEquiv.ofRingEquiv (f := ψ.toRingEquiv) (fun y => by
    obtain ⟨x, rfl⟩ := h y
    rw [← IsScalarTower.algebraMap_apply K₁ K₂ L]; exact ψ.commutes _)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- Being Galois passes to a base field mapping onto the old one: the degree and the number of
automorphisms are both unchanged. -/
theorem isGalois_of_surjective (h : Function.Surjective (algebraMap K₁ K₂))
    [FiniteDimensional K₂ L] [IsGalois K₂ L] : IsGalois K₁ L := by
  haveI := finiteDimensional_of_surjective (K₁ := K₁) (K₂ := K₂) (L := L) h
  refine IsGalois.of_card_aut_eq_finrank K₁ L ?_
  rw [← Nat.card_congr (autCongrOfSurjective (K₁ := K₁) (K₂ := K₂) (L := L) h).toEquiv,
    IsGalois.card_aut_eq_finrank K₂ L, finrank_eq_of_surjective (L := L) h]

end Transport

end Rigidity.RET

namespace IsRegularInverseGalois

/-- **A Galois extension of a rational subfield of `ℚ(T)` is a regular realization.**

If `M` is a field isomorphic to `ℚ(T)` sitting inside `ℚ(T)` as a subfield of finite index with
`ℚ(T)/M` Galois, then reading `ℚ(T)` as an extension of itself along the isomorphism exhibits the
Galois group of `ℚ(T)/M` as a regular inverse Galois group: the extension field is `ℚ(T)`, whose
constants are just `ℚ` (`Rigidity.RET.regular_ratFunc`). -/
theorem of_ratFunc_ext {G : Type*} [Group G] (M : Type) [Field M] [Algebra M (RatFunc ℚ)]
    [FiniteDimensional M (RatFunc ℚ)] [IsGalois M (RatFunc ℚ)] (e : RatFunc ℚ ≃+* M)
    (iso : (RatFunc ℚ ≃ₐ[M] RatFunc ℚ) ≃* G) : IsRegularInverseGalois G := by
  letI algMK : Algebra (RatFunc ℚ) M := (e : RatFunc ℚ →+* M).toAlgebra
  letI algLL : Algebra (RatFunc ℚ) (RatFunc ℚ) :=
    ((algebraMap M (RatFunc ℚ)).comp (e : RatFunc ℚ →+* M)).toAlgebra
  haveI tower : @IsScalarTower (RatFunc ℚ) M (RatFunc ℚ) algMK.toSMul Algebra.toSMul algLL.toSMul :=
    @IsScalarTower.of_algebraMap_eq (RatFunc ℚ) M (RatFunc ℚ) _ _ _ algMK _ algLL (fun _ => rfl)
  have hsurj : Function.Surjective (algebraMap (RatFunc ℚ) M) := e.surjective
  haveI fd : FiniteDimensional (RatFunc ℚ) (RatFunc ℚ) :=
    Rigidity.RET.finiteDimensional_of_surjective (K₁ := RatFunc ℚ) (K₂ := M) (L := RatFunc ℚ) hsurj
  haveI gal : IsGalois (RatFunc ℚ) (RatFunc ℚ) :=
    Rigidity.RET.isGalois_of_surjective (K₁ := RatFunc ℚ) (K₂ := M) (L := RatFunc ℚ) hsurj
  exact ⟨RatFunc ℚ, inferInstance, algLL, fd, gal, DivisionRing.toRatAlgebra,
    @Rigidity.RET.isScalarTower_rat_ratFunc (RatFunc ℚ) _ algLL _, Rigidity.RET.regular_ratFunc,
    ⟨(Rigidity.RET.autCongrOfSurjective (K₁ := RatFunc ℚ) (K₂ := M)
      (L := RatFunc ℚ) hsurj).symm.trans iso⟩⟩

end IsRegularInverseGalois
