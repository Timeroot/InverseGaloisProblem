/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A rational function field is regular over its field of constants

Over any field `K`, the constants are relatively algebraically closed in `K(T)`: an element of
`RatFunc K` integral over `K` is already in `K`.

Integrality over `K` implies integrality over `K[T]`, and `K[T]` is integrally closed in its
fraction field, so the element is a polynomial `p`; then `(minpoly K p).comp p = 0` and
`natDegree_comp` force `natDegree p = 0`.

This is the hypothesis `hFreg` of `Rigidity.RET.isRegularGaloisGroupOverBase_fixedField` for the
number-field bases produced by the arithmetic descent.  The `K = ℚ` case is
`Rigidity.RET.regular_ratFunc`.

## Main results

* `Rigidity.RET.Descent.algebraicClosure_ratFunc`
* `Rigidity.RET.Descent.algebraicClosure_eq_bot_of_algEquiv` — regularity over `k` only depends on
  the `k`-isomorphism class of the extension.
-/

open Polynomial

namespace Rigidity.RET.Descent

/-- **A rational function field is regular over its constants.**  For any field `K`, an element of
`K(T)` algebraic over `K` is a constant. -/
theorem algebraicClosure_ratFunc (K : Type*) [Field K] :
    algebraicClosure K (RatFunc K) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [mem_algebraicClosure_iff'] at hx
  have hxT : IsIntegral K[X] x := hx.tower_top
  obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := K[X]) (x := x)).mp hxT
  let φ : K[X] →ₐ[K] RatFunc K := IsScalarTower.toAlgHom K K[X] (RatFunc K)
  have hφinj : Function.Injective φ := by
    show Function.Injective (algebraMap K[X] (RatFunc K))
    exact IsFractionRing.injective _ _
  have hpint : IsIntegral K p := by
    have hh : IsIntegral K (φ p) := (show φ p = x from hp) ▸ hx
    exact (isIntegral_algHom_iff φ hφinj).mp hh
  have key : Polynomial.aeval p (minpoly K p) = (minpoly K p).comp p := by
    rw [Polynomial.aeval_def]; rfl
  have hcomp : (minpoly K p).comp p = 0 := key.symm.trans (minpoly.aeval K p)
  have hdeg : (minpoly K p).natDegree * p.natDegree = 0 := by
    have h := Polynomial.natDegree_comp (p := minpoly K p) (q := p)
    rw [hcomp, Polynomial.natDegree_zero] at h
    exact h.symm
  have hqpos : 0 < (minpoly K p).natDegree := minpoly.natDegree_pos hpint
  have hp0 : p.natDegree = 0 := by
    rcases Nat.mul_eq_zero.mp hdeg with h | h
    · omega
    · exact h
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hp0
  rw [IntermediateField.mem_bot]
  exact ⟨c, by rw [← hp, ← hc, Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]⟩

/-- **Regularity transports along a `k`-isomorphism.**  If `k` is relatively algebraically closed
in `A` and `A ≃ₐ[k] B`, then it is relatively algebraically closed in `B`. -/
theorem algebraicClosure_eq_bot_of_algEquiv {k A B : Type*} [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (h : algebraicClosure k A = ⊥) :
    algebraicClosure k B = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hxA : e.symm x ∈ algebraicClosure k A := by
    refine (map_mem_algebraicClosure_iff (e : A →ₐ[k] B)).mp ?_
    rwa [show (e : A →ₐ[k] B) (e.symm x) = x from e.apply_symm_apply x]
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp (h ▸ hxA)
  refine IntermediateField.mem_bot.mpr ⟨c, ?_⟩
  rw [← e.commutes c, hc, e.apply_symm_apply]

end Rigidity.RET.Descent
