/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Isogeny

/-!
# Isogenous lattices have the same Herbrand quotient

A lattice is a finitely generated free `ℤ`-module.  An injection of one lattice into another of the
same rank has finite cokernel, so by the invariance of the Herbrand quotient under a finite change
an equivariant injection between lattices of equal rank already forces the two Herbrand quotients
to agree.  No hypothesis on the index is needed: the ranks decide it.

The form in which this is used is that of an isogeny.  Two lattices carrying an action of the same
cyclic group and becoming isomorphic after tensoring with the rationals are related by a pair of
equivariant maps whose composites are multiplication by a nonzero integer -- clear the denominators
of a rational isomorphism and of its inverse -- and such a pair forces the ranks to agree.  The
Herbrand quotient of a lattice therefore depends only on the rational representation it carries,
which is what allows the unit lattice of a number field to be compared with a lattice of
permutations of places.

## Main results

* `InverseGalois.CFT.finite_quotient_range_of_finrank_eq`: an injection of lattices of equal rank
  has finite cokernel.
* `InverseGalois.CFT.herbrand_eq_of_injective_of_finrank_eq`: **an equivariant injection between
  lattices of equal rank does not change the Herbrand quotient.**
* `InverseGalois.CFT.injective_of_comp_eq_nsmul`: a map of lattices with a retraction up to a
  nonzero integer is injective.
* `InverseGalois.CFT.finrank_eq_of_isogeny`: isogenous lattices have the same rank.
* `InverseGalois.CFT.herbrand_eq_of_isogeny`: **isogenous lattices have the same Herbrand
  quotient.**

## Tags

Tate cohomology, Herbrand quotient, lattice, isogeny, commensurable
-/

namespace InverseGalois.CFT

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℕ}

/-! ### The cokernel of an injection of equal rank -/

/-- The image of a homomorphism of `ℤ`-modules, as a submodule, has the range as its underlying
subgroup. -/
theorem toAddSubgroup_range_toIntLinearMap (u : A →+ B) :
    (LinearMap.range u.toIntLinearMap).toAddSubgroup = u.range := by
  ext b
  exact Iff.rfl

/-- **An injection of lattices of equal rank has finite cokernel.** -/
theorem finite_quotient_range_of_finrank_eq [Module.Free ℤ A] [Module.Finite ℤ A]
    [Module.Free ℤ B] [Module.Finite ℤ B] (u : A →+ B) (hu : Function.Injective u)
    (hrank : Module.finrank ℤ A = Module.finrank ℤ B) : Finite (B ⧸ u.range) := by
  have hrange : Module.finrank ℤ (LinearMap.range u.toIntLinearMap) = Module.finrank ℤ B := by
    rw [LinearMap.finrank_range_of_inj (f := u.toIntLinearMap) hu, hrank]
  have hfin : Finite (B ⧸ LinearMap.range u.toIntLinearMap) :=
    Submodule.finiteQuotientOfFreeOfRankEq _ hrange
  rw [← toAddSubgroup_range_toIntLinearMap u]
  exact hfin

variable {σA : A ≃+ A} {σB : B ≃+ B}

/-- **An equivariant injection between lattices of equal rank does not change the Herbrand
quotient.** -/
theorem herbrand_eq_of_injective_of_finrank_eq [Module.Free ℤ A] [Module.Finite ℤ A]
    [Module.Free ℤ B] [Module.Finite ℤ B] (hσA : σA ^ n = 1) (hσB : σB ^ n = 1) (u : A →+ B)
    (hu : ∀ a, u (σA a) = σB (u a)) (hinj : Function.Injective u)
    (hrank : Module.finrank ℤ A = Module.finrank ℤ B)
    [Finite (tateH0 σA n)] [Finite (tateH0 σB n)]
    [Finite (tateHm1 σA n)] [Finite (tateHm1 σB n)] :
    herbrand σA n = herbrand σB n :=
  haveI := finite_quotient_range_of_finrank_eq u hinj hrank
  herbrand_eq_of_injective_of_finite_quotient hσA hσB u hu hinj

/-! ### Isogenies -/

/-- **A map of lattices with a retraction up to a nonzero integer is injective.** -/
theorem injective_of_comp_eq_nsmul [Module.Free ℤ A] (u : A →+ B) (v : B →+ A) {N : ℕ}
    (hN : N ≠ 0) (hvu : ∀ a, v (u a) = N • a) : Function.Injective u := by
  refine (injective_iff_map_eq_zero u).2 fun a ha => ?_
  have h : (N : ℤ) • a = 0 := by
    rw [natCast_zsmul, ← hvu a, ha, map_zero]
  exact (smul_eq_zero.1 h).resolve_left (Int.natCast_ne_zero.2 hN)

/-- **Isogenous lattices have the same rank.** -/
theorem finrank_eq_of_isogeny [Module.Free ℤ A] [Module.Finite ℤ A] [Module.Free ℤ B]
    [Module.Finite ℤ B] (u : A →+ B) (v : B →+ A) {N : ℕ} (hN : N ≠ 0)
    (hvu : ∀ a, v (u a) = N • a) (huv : ∀ b, u (v b) = N • b) :
    Module.finrank ℤ A = Module.finrank ℤ B :=
  le_antisymm
    (LinearMap.finrank_le_finrank_of_injective (f := u.toIntLinearMap)
      (injective_of_comp_eq_nsmul u v hN hvu))
    (LinearMap.finrank_le_finrank_of_injective (f := v.toIntLinearMap)
      (injective_of_comp_eq_nsmul v u hN huv))

/-- **Isogenous lattices have the same Herbrand quotient.**  A pair of equivariant maps whose
composites are multiplication by a nonzero integer is what a rational isomorphism of two lattices
becomes after its denominators, and those of its inverse, are cleared. -/
theorem herbrand_eq_of_isogeny [Module.Free ℤ A] [Module.Finite ℤ A] [Module.Free ℤ B]
    [Module.Finite ℤ B] (hσA : σA ^ n = 1) (hσB : σB ^ n = 1) (u : A →+ B) (v : B →+ A)
    (hu : ∀ a, u (σA a) = σB (u a)) {N : ℕ} (hN : N ≠ 0) (hvu : ∀ a, v (u a) = N • a)
    (huv : ∀ b, u (v b) = N • b)
    [Finite (tateH0 σA n)] [Finite (tateH0 σB n)]
    [Finite (tateHm1 σA n)] [Finite (tateHm1 σB n)] :
    herbrand σA n = herbrand σB n :=
  herbrand_eq_of_injective_of_finrank_eq hσA hσB u hu (injective_of_comp_eq_nsmul u v hN hvu)
    (finrank_eq_of_isogeny u v hN hvu huv)

end InverseGalois.CFT
