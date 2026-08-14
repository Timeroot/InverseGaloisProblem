/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdResidue

/-!
# Points of a cover over an algebraically closed field of constants

A cover of the line over an algebraically closed field of constants has no room, at any of its
points, for a residue field larger than the constants: the functions of the cover form an algebra
of finite type over the constants, so the residue field at a maximal ideal is a finite extension of
them, and an algebraically closed field has none.

Every function of the cover therefore has a value at every point, and — combined with the local
description of the functions regular at a prime — so does every function merely regular there.

## Main results

* `Rigidity.RET.exists_const_sub_mem` — a function of a finite-type algebra over an algebraically
  closed field agrees with a constant modulo any maximal ideal.
* `Rigidity.RET.exists_const_ordAtLeast_one_sub_of_finiteType` — a function regular at a prime of
  such an algebra agrees there, to first order, with a constant.
-/

open IsDedekindDomain

noncomputable section


namespace Rigidity.RET

section ResidueField

variable {k R : Type*} [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R]

/-- **A function agrees with a constant at a point.**  The residue field at a maximal ideal of an
algebra of finite type over an algebraically closed field is that field. -/
theorem surjective_algebraMap_of_finiteType {L : Type*} [Field L] [Algebra k L]
    [Algebra.FiniteType k L] : Function.Surjective (algebraMap k L) := by
  haveI : Module.Finite k L := finite_of_finite_type_of_isJacobsonRing k L
  haveI : Algebra.IsIntegral k L := Algebra.IsIntegral.of_finite k L
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := L)).2

/-- **A function agrees with a constant at a point.**  The residue field at a maximal ideal of an
algebra of finite type over an algebraically closed field is that field. -/
theorem exists_const_sub_mem [Algebra.FiniteType k R] (m : Ideal R) [hm : m.IsMaximal] (b : R) :
    ∃ c : k, b - algebraMap k R c ∈ m := by
  haveI : Algebra.FiniteType k (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m)
      (Ideal.Quotient.mkₐ_surjective k m)
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  obtain ⟨c, hc⟩ :=
    surjective_algebraMap_of_finiteType (k := k) (L := R ⧸ m) (Ideal.Quotient.mk m b)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, ← hc]
  rfl

variable [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [Algebra k K] [IsScalarTower k R K]

/-- **A function regular at a prime agrees there, to first order, with a constant.** -/
theorem exists_const_ordAtLeast_one_sub_of_finiteType [Algebra.FiniteType k R]
    {v : HeightOneSpectrum R} {z : K} (hz : OrdAtLeast K v 0 z) :
    ∃ c : k, OrdAtLeast K v 1 (z - algebraMap k K c) := by
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  exact exists_const_ordAtLeast_one_sub (fun b => exists_const_sub_mem v.asIdeal b) hz

end ResidueField

end Rigidity.RET
