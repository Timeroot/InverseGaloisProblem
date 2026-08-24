/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicAction
import InverseGalois.CFT.Local.UnitValuation

/-!
# Uniformizers fixed by a decomposition group

The Tate groups of the units of the valuation ring at a finite place of a Galois extension of number
fields vanish as soon as the decomposition group there fixes a uniformizer, and that is what makes
all but finitely many places invisible in the Herbrand quotient of the ideles.  This file produces
such a uniformizer at an unramified place, and shows that only finitely many places are left out.

A prime is unramified over the base exactly when the ideal generated there by the prime below is not
contained in its square.  In that case some element of the base ring lies in the prime and not in its
square, so it has valuation exactly one; its inverse is a unit of the completion of valuation minus
one, and it is fixed by the whole Galois group because it comes from the base field.  The places
where this fails are the ones dividing the different ideal, and a nonzero ideal has only finitely
many prime divisors.

## Main results

* `InverseGalois.CFT.intValuation_eq_of_mem_of_notMem_sq`: an element of a prime but not of its
  square has valuation exactly one there.
* `InverseGalois.CFT.exists_fixedUniformizer_of_not_map_le_sq`: **an unramified place carries a
  uniformizer fixed by its decomposition group.**
* `InverseGalois.CFT.exists_fixedUniformizer_of_isUnramifiedAt`: **a place unramified over the base
  carries a uniformizer fixed by its decomposition group.**
* `InverseGalois.CFT.finite_setOf_not_exists_fixedUniformizer`: **only finitely many places fail to
  carry a uniformizer fixed by the decomposition group.**

## Tags

number field, unramified, uniformizer, decomposition group, different ideal
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### The valuation of an element of a prime but not of its square -/

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

omit [IsDomain R] in
/-- An element of a prime but not of its square has valuation exactly one there. -/
theorem intValuation_eq_of_mem_of_notMem_sq (v : HeightOneSpectrum R) {r : R}
    (h1 : r ∈ v.asIdeal) (h2 : r ∉ v.asIdeal ^ 2) :
    v.intValuation r = WithZero.exp (-1 : ℤ) := by
  have hr : r ≠ 0 := by
    rintro rfl
    exact h2 (Submodule.zero_mem _)
  have hle : v.intValuation r ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    simpa using h1
  have hnle : ¬v.intValuation r ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact h2
  push_neg at hnle
  obtain ⟨c, hc⟩ : ∃ c : ℤ, v.intValuation r = WithZero.exp c :=
    ⟨WithZero.log (v.intValuation r), (WithZero.exp_log (v.intValuation_ne_zero r hr)).symm⟩
  rw [hc] at hle hnle ⊢
  rw [WithZero.exp_le_exp] at hle
  rw [WithZero.exp_lt_exp] at hnle
  congr 1
  push_cast at hle hnle
  lia

end Valuation

/-! ### A uniformizer coming from the base field -/

section BaseUniformizer

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

omit [NumberField k] [NumberField K] in
/-- **A prime whose ideal from the base is not contained in its square receives an element of the
base ring lying in it but not in its square.** -/
theorem exists_mem_notMem_sq_of_not_map_le_sq (v : HeightOneSpectrum (𝓞 K))
    (h : ¬Ideal.map (algebraMap (𝓞 k) (𝓞 K)) (v.asIdeal.under (𝓞 k)) ≤ v.asIdeal ^ 2) :
    ∃ ϖ : 𝓞 k, algebraMap (𝓞 k) (𝓞 K) ϖ ∈ v.asIdeal ∧
      algebraMap (𝓞 k) (𝓞 K) ϖ ∉ v.asIdeal ^ 2 := by
  by_contra hc
  push_neg at hc
  refine h ?_
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact hc x (Ideal.map_comap_le (Ideal.mem_map_of_mem (algebraMap (𝓞 k) (𝓞 K)) hx))

omit [NumberField k] in
/-- An element of the base field of valuation minus one at a prime gives a unit of the completion
there which is fixed by the decomposition group and has valuation one. -/
theorem exists_fixedUniformizer_of_valuation (v : HeightOneSpectrum (𝓞 K)) {a : k}
    (hval : v.valuation K (algebraMap k K a) = WithZero.exp (-1 : ℤ)) :
    ∃ π : (v.adicCompletion K)ˣ,
      (∀ g : ↥(stabilizer Gal(K/k) v),
          g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
        ∧ unitVal (Additive.ofMul π) = 1 := by
  set y : K := (algebraMap k K a)⁻¹ with hy
  have hyv : v.valuation K y = WithZero.exp (1 : ℤ) := by
    rw [hy, map_inv₀, hval]
    simp
  have hcoe : Valued.v ((y : WithVal (v.valuation K)) : v.adicCompletion K)
      = WithZero.exp (1 : ℤ) := by
    rw [Valued.valuedCompletion_apply]
    exact hyv
  have hne : ((y : WithVal (v.valuation K)) : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hcoe
    exact WithZero.exp_ne_zero hcoe.symm
  refine ⟨Units.mk0 _ hne, ?_, ?_⟩
  · intro g
    show adicCompletionAut v g.1 (mem_stabilizer_iff.mp g.2)
        ((y : WithVal (v.valuation K)) : v.adicCompletion K) = _
    rw [adicCompletionAut_coe]
    congr 1
    show (WithVal.equiv (v.valuation K)).symm (g.1 (WithVal.equiv (v.valuation K) y)) = _
    show g.1 y = y
    rw [hy, map_inv₀]
    congr 1
    exact AlgEquiv.commutes g.1 a
  · show WithZero.log (Valued.v ((y : WithVal (v.valuation K)) : v.adicCompletion K)) = 1
    rw [hcoe]
    simp

omit [NumberField k] in
/-- **An unramified place carries a uniformizer fixed by its decomposition group.**  Unramifiedness
is read as the ideal generated by the prime below not being contained in the square of the prime; an
element of the base ring witnessing that has valuation exactly one, and its inverse is a unit of the
completion of valuation one which the Galois group fixes because it comes from the base field. -/
theorem exists_fixedUniformizer_of_not_map_le_sq (v : HeightOneSpectrum (𝓞 K))
    (h : ¬Ideal.map (algebraMap (𝓞 k) (𝓞 K)) (v.asIdeal.under (𝓞 k)) ≤ v.asIdeal ^ 2) :
    ∃ π : (v.adicCompletion K)ˣ,
      (∀ g : ↥(stabilizer Gal(K/k) v),
          g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
        ∧ unitVal (Additive.ofMul π) = 1 := by
  obtain ⟨ϖ, h1, h2⟩ := exists_mem_notMem_sq_of_not_map_le_sq (k := k) v h
  refine exists_fixedUniformizer_of_valuation v (a := algebraMap (𝓞 k) k ϖ) ?_
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 k) (𝓞 K) K,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact intValuation_eq_of_mem_of_notMem_sq v h1 h2

/-- **A place unramified over the base carries a uniformizer fixed by its decomposition group.**
Were the ideal generated by the prime below contained in the square of the prime, the ramification
index would not be one, which is what unramifiedness gives. -/
theorem exists_fixedUniformizer_of_isUnramifiedAt (v : HeightOneSpectrum (𝓞 K))
    (h : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal) :
    ∃ π : (v.adicCompletion K)ˣ,
      (∀ g : ↥(stabilizer Gal(K/k) v),
          g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
        ∧ unitVal (Additive.ofMul π) = 1 := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI := h
  refine exists_fixedUniformizer_of_not_map_le_sq v fun hc => ?_
  exact (Ideal.ramificationIdx_ne_one_iff Ideal.map_comap_le).mpr hc
    (Ideal.ramificationIdx_eq_one_of_isUnramifiedAt v.ne_bot)

end BaseUniformizer

/-! ### Only finitely many places are ramified -/

section Finiteness

attribute [local instance] FractionRing.liftAlgebra

variable (k : Type*) {K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- A place at which the ideal generated by the prime below is contained in the square of the prime
divides the different ideal. -/
theorem dvd_differentIdeal_of_map_le_sq {v : HeightOneSpectrum (𝓞 K)}
    (h : Ideal.map (algebraMap (𝓞 k) (𝓞 K)) (v.asIdeal.under (𝓞 k)) ≤ v.asIdeal ^ 2) :
    v.asIdeal ∣ differentIdeal (𝓞 k) (𝓞 K) := by
  refine dvd_differentIdeal_iff.mpr fun hun => ?_
  have hne : Ideal.ramificationIdx (algebraMap (𝓞 k) (𝓞 K)) (v.asIdeal.under (𝓞 k)) v.asIdeal
      ≠ 1 := (Ideal.ramificationIdx_ne_one_iff Ideal.map_comap_le).mpr h
  exact hne (Ideal.ramificationIdx_eq_one_of_isUnramifiedAt v.ne_bot)

/-- Only finitely many places are ramified over the base field. -/
theorem finite_setOf_map_le_sq :
    {v : HeightOneSpectrum (𝓞 K) |
      Ideal.map (algebraMap (𝓞 k) (𝓞 K)) (v.asIdeal.under (𝓞 k)) ≤ v.asIdeal ^ 2}.Finite :=
  Set.Finite.subset (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 k) (B := 𝓞 K)))
    fun _ hv => dvd_differentIdeal_of_map_le_sq k hv

/-- **Only finitely many places fail to carry a uniformizer fixed by the decomposition group.** -/
theorem finite_setOf_not_exists_fixedUniformizer :
    {v : HeightOneSpectrum (𝓞 K) | ¬∃ π : (v.adicCompletion K)ˣ,
      (∀ g : ↥(stabilizer Gal(K/k) v),
          g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
        ∧ unitVal (Additive.ofMul π) = 1}.Finite :=
  Set.Finite.subset (finite_setOf_map_le_sq k) fun _ hv =>
    not_not.mp fun h => hv (exists_fixedUniformizer_of_not_map_le_sq _ h)

end Finiteness

end InverseGalois.CFT
