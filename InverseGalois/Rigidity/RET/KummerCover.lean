/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Existence

/-!
# Cyclic groups are geometric Galois covers: the Kummer cover `xⁿ = T`

The Riemann Existence Theorem asserts that *every* finite group is realized by a geometric Galois
cover of `ℙ¹_ℚ̄` (`IsGeometricGaloisCover`).  For **cyclic** groups the cover is completely
explicit and the statement is elementary algebra: the Kummer extension `ℚ̄(T)(ⁿ√T) / ℚ̄(T)`, i.e.
the degree-`n` cover `x ↦ xⁿ` of the projective line branched over `0` and `∞`.

This module proves that instance of the Riemann Existence conclusion outright.  The two ingredients
are

* irreducibility of `Xⁿ - T` over `k(T)` for every field `k` — Eisenstein at the prime `T` of `k[T]`
  followed by Gauss's lemma (`irreducible_X_pow_sub_C_X`); note that this is *unconditional* in `n`,
  where the general Kummer irreducibility criterion in Mathlib
  (`X_pow_sub_C_irreducible_of_odd`) covers only odd exponents; and
* Mathlib's Kummer theory (`autEquivZmod`), which computes the Galois group of the splitting field
  of `Xⁿ - a` as `ZMod n` once the base field contains a primitive `n`-th root of unity — which
  `ℚ̄(T)` does, `ℚ̄` being algebraically closed of characteristic zero.

## Main results

* `Rigidity.RET.irreducible_X_pow_sub_C_X_polynomial` — `Xⁿ - T` is irreducible over `k[T]`.
* `Rigidity.RET.irreducible_X_pow_sub_C_X` — `Xⁿ - T` is irreducible over `k(T)` for `n ≠ 0`.
* `Rigidity.RET.isGeometricGaloisCover_of_isCyclic` — every finite cyclic group is realized by a
  geometric Galois cover of `ℙ¹_ℚ̄`.
* `Rigidity.RET.IsGeometricGaloisCover.of_mulEquiv` — the predicate transports along a group
  isomorphism.
-/

namespace Rigidity.RET

open Polynomial

/-- `IsGeometricGaloisCover` only depends on the isomorphism class of the group. -/
theorem IsGeometricGaloisCover.of_mulEquiv {G G' : Type} [Group G] [Group G']
    (h : IsGeometricGaloisCover G) (e : G ≃* G') : IsGeometricGaloisCover G' := by
  obtain ⟨L, _, _, _, _, ⟨f⟩⟩ := h
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ⟨f.trans e⟩⟩

section Irreducibility

variable {k : Type*} [Field k]

/-- The ideal `(T) ⊆ k[T]` is prime. -/
private theorem isPrime_span_X : (Ideal.span {(Polynomial.X : k[X])}).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr prime_X

/-- **`Xⁿ - T` is irreducible over `k[T]`**, by Eisenstein at the prime `T`.

Stated over the polynomial ring rather than the function field, so that it can be pushed into any
fraction field of `k[T]` (Gauss's lemma), not only into `RatFunc k`. -/
theorem irreducible_X_pow_sub_C_X_polynomial {n : ℕ} (hn : n ≠ 0) :
    Irreducible ((X : k[X][X]) ^ n - C (Polynomial.X : k[X])) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hmonic : ((X : k[X][X]) ^ n - C (Polynomial.X : k[X])).Monic := monic_X_pow_sub_C _ hn
  have hdeg : ((X : k[X][X]) ^ n - C (Polynomial.X : k[X])).degree = (n : WithBot ℕ) :=
    degree_X_pow_sub_C hn0 _
  refine irreducible_of_eisenstein_criterion (P := Ideal.span {(Polynomial.X : k[X])})
    isPrime_span_X ?_ ?_ ?_ ?_ hmonic.isPrimitive
  · rw [hmonic.leadingCoeff]
    exact fun h => isPrime_span_X.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · intro m hm
    rw [hdeg] at hm
    have hmn : ¬ m = n := by
      intro h
      exact absurd hm (by simp [h])
    rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hmn]
    by_cases hm0 : m = 0
    · rw [if_pos hm0, zero_sub]
      exact neg_mem (Ideal.mem_span_singleton_self _)
    · rw [if_neg hm0, sub_zero]
      exact Ideal.zero_mem _
  · rw [hdeg]
    exact_mod_cast hn0
  · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg (Ne.symm hn), if_pos rfl, zero_sub,
      Ideal.span_singleton_pow]
    intro h
    have hdvd : (Polynomial.X : k[X]) ^ 2 ∣ Polynomial.X :=
      dvd_neg.mp (Ideal.mem_span_singleton.mp h)
    have := Polynomial.natDegree_le_of_dvd hdvd Polynomial.X_ne_zero
    simp at this

/-- **`Xⁿ - T` is irreducible over the rational function field `k(T)`**, for every field `k` and
every `n ≠ 0`.

Eisenstein at the prime `T` of `k[T]` gives irreducibility over the polynomial ring, and Gauss's
lemma transfers it to the fraction field.  Unlike the general Kummer criterion, this needs no parity
hypothesis on `n`: it is the special shape of the element `T`, a uniformizer at the origin, that
does the work. -/
theorem irreducible_X_pow_sub_C_X (k : Type*) [Field k] {n : ℕ} (hn : n ≠ 0) :
    Irreducible ((X : (RatFunc k)[X]) ^ n - C (RatFunc.X : RatFunc k)) := by
  have hmonic : ((X : k[X][X]) ^ n - C (Polynomial.X : k[X])).Monic := monic_X_pow_sub_C _ hn
  have := (hmonic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc k)).mp
    (irreducible_X_pow_sub_C_X_polynomial hn)
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, RatFunc.algebraMap_X]
    using this

end Irreducibility

/-- **Every finite cyclic group is realized by a geometric Galois cover of `ℙ¹_ℚ̄`.**

The cover is the Kummer extension `ℚ̄(T)(ⁿ√T) / ℚ̄(T)` with `n = |G|`, i.e. the degree-`n` map
`x ↦ xⁿ` of the projective line, branched over `0` and `∞`: `Xⁿ - T` is irreducible
(`irreducible_X_pow_sub_C_X`), `ℚ̄` contains a primitive `n`-th root of unity, and Kummer theory
identifies the Galois group of the splitting field with `ZMod n`.

This is the conclusion of the Riemann Existence Theorem for cyclic groups, obtained here by pure
algebra — no comparison between the analytic and algebraic fundamental groups is involved. -/
theorem isGeometricGaloisCover_of_isCyclic (G : Type) [Group G] [Finite G] [IsCyclic G] :
    IsGeometricGaloisCover G := by
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  haveI : NeZero (Nat.card G) := ⟨hn⟩
  haveI : NeZero ((Nat.card G : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hn⟩
  obtain ⟨ζ₀, hζ₀⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (Nat.card G)
  have hζ : IsPrimitiveRoot
      (algebraMap (AlgebraicClosure ℚ) GeomFunctionField ζ₀) (Nat.card G) :=
    hζ₀.map_of_injective (algebraMap (AlgebraicClosure ℚ) GeomFunctionField).injective
  have hprim : (primitiveRoots (Nat.card G) GeomFunctionField).Nonempty :=
    ⟨_, (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).mpr hζ⟩
  have H : Irreducible
      ((X : GeomFunctionField[X]) ^ Nat.card G - C (RatFunc.X : GeomFunctionField)) :=
    irreducible_X_pow_sub_C_X _ hn
  let L := ((X : GeomFunctionField[X]) ^ Nat.card G -
    C (RatFunc.X : GeomFunctionField)).SplittingField
  haveI : IsGalois GeomFunctionField L := isGalois_of_isSplittingField_X_pow_sub_C hprim H L
  haveI : FiniteDimensional GeomFunctionField L := IsSplittingField.finiteDimensional L
    ((X : GeomFunctionField[X]) ^ Nat.card G - C (RatFunc.X : GeomFunctionField))
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(autEquivZmod H L hζ).trans (zmodCyclicMulEquiv (inferInstance : IsCyclic G))⟩⟩

end Rigidity.RET
