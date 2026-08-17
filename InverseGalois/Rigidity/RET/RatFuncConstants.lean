/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Constants, powers and coefficient automorphisms of a rational function field

Three independent toolkits for working with `RatFunc k`, all elementary but missing from
Mathlib in the exact shape needed downstream.

* **Constants.** `algebraicClosure_ratFunc`: a field `k` is relatively algebraically closed in
  `k(T)`.  (The repo already has this for `k = ℚ`; here it is over an arbitrary field.)

* **Powers.** `rootMultiplicity_dvd_of_pow_eq`: if a polynomial `q` becomes an `n`-th power in
  `k(T)`, then every root multiplicity of `q` is divisible by `n`.  Since `k[X]` is integrally
  closed, an `n`-th root in the fraction field is already a polynomial, and multiplicities then
  multiply.  This is the standard criterion certifying that a Kummer extension `X ^ n - q` is a
  field.

* **Coefficient automorphisms.** `ratFuncMapAlg`: an automorphism `σ` of `K` over `k` acts on
  `K(T)` coefficientwise, fixing `k(T)`, and this action is a group homomorphism which is
  injective — so orders of automorphisms are preserved.
-/

open Polynomial

namespace Rigidity.RET

noncomputable section

/-! ### Constants of a rational function field -/

/-- **A field is relatively algebraically closed in its rational function field.**
An element of `k(T)` algebraic over `k` is integral over `k[X]`, hence a polynomial, and a
polynomial satisfying an algebraic relation over `k` must be constant. -/
theorem algebraicClosure_ratFunc (k : Type*) [Field k] : algebraicClosure k (RatFunc k) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [mem_algebraicClosure_iff'] at hx
  have hxT : IsIntegral (Polynomial k) x := hx.tower_top
  obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Polynomial k) (x := x)).mp hxT
  let φ : Polynomial k →ₐ[k] RatFunc k := IsScalarTower.toAlgHom k (Polynomial k) (RatFunc k)
  have hφinj : Function.Injective φ := by
    show Function.Injective (algebraMap (Polynomial k) (RatFunc k))
    exact IsFractionRing.injective _ _
  have hpint : IsIntegral k p := by
    have hh : IsIntegral k (φ p) := (show φ p = x from hp) ▸ hx
    exact (isIntegral_algHom_iff φ hφinj).mp hh
  have key : Polynomial.aeval p (minpoly k p) = (minpoly k p).comp p := by
    rw [Polynomial.aeval_def]; rfl
  have hcomp : (minpoly k p).comp p = 0 := key.symm.trans (minpoly.aeval k p)
  have hdeg : (minpoly k p).natDegree * p.natDegree = 0 := by
    have h := Polynomial.natDegree_comp (p := minpoly k p) (q := p)
    rw [hcomp, Polynomial.natDegree_zero] at h
    exact h.symm
  have hqpos : 0 < (minpoly k p).natDegree := minpoly.natDegree_pos hpint
  have hp0 : p.natDegree = 0 := by
    rcases Nat.mul_eq_zero.mp hdeg with h | h
    · omega
    · exact h
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hp0
  rw [IntermediateField.mem_bot]
  refine ⟨c, ?_⟩
  rw [← hp, ← hc, Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]

/-! ### Powers in a rational function field -/

/-- Root multiplicities are multiplied by taking powers. -/
theorem rootMultiplicity_pow {R : Type*} [CommRing R] [IsDomain R] {p : R[X]} (hp : p ≠ 0)
    (a : R) (n : ℕ) : (p ^ n).rootMultiplicity a = n * p.rootMultiplicity a := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, rootMultiplicity_mul (by exact mul_ne_zero (pow_ne_zero _ hp) hp), ih]
      ring

/-- **An `n`-th power in `k(T)` is an `n`-th power of a polynomial**, so all its root
multiplicities are divisible by `n`. -/
theorem rootMultiplicity_dvd_of_pow_eq {k : Type*} [Field k] {q : k[X]} {n : ℕ} {y : RatFunc k}
    (hq : q ≠ 0) (hy : y ^ n = algebraMap k[X] (RatFunc k) q) (a : k) :
    n ∣ q.rootMultiplicity a := by
  have hinj : Function.Injective (algebraMap k[X] (RatFunc k)) := IsFractionRing.injective _ _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : q = 1 := by
      apply hinj
      rw [← hy, pow_zero, map_one]
    simp [this]
  · have hmonic : (X ^ n - C q).Monic := monic_X_pow_sub_C q (by omega)
    have hint : IsIntegral k[X] y := ⟨X ^ n - C q, hmonic, by simp [hy]⟩
    obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := k[X]) (x := y)).mp hint
    have hpq : p ^ n = q := by
      apply hinj
      rw [map_pow, hp, hy]
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact hq (by simpa [zero_pow hn.ne'] using hpq.symm)
    exact ⟨p.rootMultiplicity a, by rw [← hpq, rootMultiplicity_pow hp0]⟩

/-! ### Coefficient automorphisms -/

section Map

attribute [local instance] Polynomial.algebra

open scoped RatFunc

/-- Shortcut for a faithfulness fact whose instance search is pathologically slow. -/
instance (priority := high) faithfulSMul_polynomial_ratFunc (K : Type*) [Field K] :
    FaithfulSMul K[X] (RatFunc K) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective K[X] (RatFunc K))

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- An automorphism of `K` acts on `K(T)` coefficientwise. -/
def ratFuncMap (σ : K ≃ₐ[k] K) : RatFunc K ≃+* RatFunc K :=
  IsFractionRing.ringEquivOfRingEquiv (Polynomial.mapEquiv (σ : K ≃+* K))

@[simp] theorem ratFuncMap_algebraMap (σ : K ≃ₐ[k] K) (p : K[X]) :
    ratFuncMap σ (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (p.map σ) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (Polynomial.mapEquiv (σ : K ≃+* K)) p

/-- The coefficient action of `Aut(K/k)` on `K(T)` is multiplicative. -/
theorem ratFuncMap_mul (σ τ : K ≃ₐ[k] K) (x : RatFunc K) :
    ratFuncMap (σ * τ) x = ratFuncMap σ (ratFuncMap τ x) := by
  have h : (ratFuncMap (k := k) (σ * τ) : RatFunc K →+* RatFunc K)
      = (ratFuncMap (k := k) σ : RatFunc K →+* RatFunc K).comp (ratFuncMap τ) := by
    refine IsFractionRing.ringHom_ext (A := K[X]) fun p => ?_
    simp [Polynomial.map_map]
    rfl
  exact congrArg (fun f : RatFunc K →+* RatFunc K => f x) h

theorem ratFuncMap_one (x : RatFunc K) : ratFuncMap (1 : K ≃ₐ[k] K) x = x := by
  have h : (ratFuncMap (1 : K ≃ₐ[k] K) : RatFunc K →+* RatFunc K) = RingHom.id _ := by
    refine IsFractionRing.ringHom_ext (A := K[X]) fun p => ?_
    simp only [RingHom.coe_coe, ratFuncMap_algebraMap, RingHom.id_apply]
    congr 1
    exact Polynomial.map_id
  exact congrArg (fun f : RatFunc K →+* RatFunc K => f x) h

/-- The two ways of mapping a polynomial over the base field into `K(T)` agree. -/
theorem algebraMap_ratFunc_ratFunc (q : k[X]) :
    algebraMap (RatFunc k) (RatFunc K) (algebraMap k[X] (RatFunc k) q)
      = algebraMap K[X] (RatFunc K) (q.map (algebraMap k K)) := by
  have h1 : algebraMap (RatFunc k) (RatFunc K) (algebraMap k[X] (RatFunc k) q)
      = algebraMap k[X] (RatFunc K) q :=
    IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective k[X] (RatFunc K)) q
  rw [h1, IsScalarTower.algebraMap_apply k[X] K[X] (RatFunc K)]
  rfl

/-- Coefficientwise action of `Aut(K/k)` on `K(T)`, as a `k(T)`-algebra automorphism. -/
def ratFuncMapAlg (σ : K ≃ₐ[k] K) : RatFunc K ≃ₐ[RatFunc k] RatFunc K :=
  AlgEquiv.ofRingEquiv (f := ratFuncMap σ) (by
    have h : (ratFuncMap (k := k) σ).toRingHom.comp (algebraMap (RatFunc k) (RatFunc K)) =
        algebraMap (RatFunc k) (RatFunc K) := by
      refine IsFractionRing.ringHom_ext (A := k[X]) fun p => ?_
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        algebraMap_ratFunc_ratFunc, ratFuncMap_algebraMap, Polynomial.map_map]
      congr 2
      exact σ.toAlgHom.comp_algebraMap
    intro x
    exact congrArg (fun f : RatFunc k →+* RatFunc K => f x) h)

@[simp] theorem ratFuncMapAlg_apply (σ : K ≃ₐ[k] K) (x : RatFunc K) :
    ratFuncMapAlg σ x = ratFuncMap σ x := rfl

/-- Coefficientwise action of `Aut(K/k)` on `K(T)`, as a group homomorphism. -/
def ratFuncMapHom : (K ≃ₐ[k] K) →* (RatFunc K ≃ₐ[RatFunc k] RatFunc K) where
  toFun := ratFuncMapAlg
  map_one' := AlgEquiv.ext fun x => ratFuncMap_one x
  map_mul' σ τ := AlgEquiv.ext fun x => ratFuncMap_mul σ τ x

theorem ratFuncMapHom_injective :
    Function.Injective (ratFuncMapHom (k := k) (K := K)) := by
  intro σ τ h
  ext c
  have hc : ratFuncMap σ (algebraMap K[X] (RatFunc K) (C c))
      = ratFuncMap τ (algebraMap K[X] (RatFunc K) (C c)) :=
    congrArg (fun e : RatFunc K ≃ₐ[RatFunc k] RatFunc K => e (algebraMap K[X] (RatFunc K) (C c))) h
  rw [ratFuncMap_algebraMap, ratFuncMap_algebraMap, Polynomial.map_C, Polynomial.map_C] at hc
  have := (IsFractionRing.injective K[X] (RatFunc K)) hc
  exact C_injective this

/-- Passing to the coefficient action preserves the order of an automorphism. -/
theorem orderOf_ratFuncMapAlg (σ : K ≃ₐ[k] K) :
    orderOf (ratFuncMapAlg (k := k) σ) = orderOf σ :=
  orderOf_injective _ ratFuncMapHom_injective σ

end Map

end

end Rigidity.RET
