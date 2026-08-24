/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicPowIndex
import InverseGalois.CFT.Local.InfinitePowIndex

/-!
# The product of the local indices of the `n`-th powers over a set of places

At every place of a number field the index of the `n`-th powers in the units of the completion,
multiplied by the normalised absolute value of `n` there, equals `n` times the number of `n`-th
roots of unity of the completion.  The normalising factors are exactly the ones appearing in the
product formula, so as soon as a finite set of places carries every place at which `n` has absolute
value different from one, those factors multiply to one over that set.

The product of the local indices over such a set is therefore `n` raised to the number of places,
times the product of the local numbers of `n`-th roots of unity.

## Main results

* `InverseGalois.CFT.apply_natCast_infinitePlace`: an infinite place sends a natural number to
  itself.
* `InverseGalois.CFT.finprod_finitePlace_eq_prod`: the product of the finite absolute values of a
  number, over a finite set of places carrying all the places where it is not one.
* `InverseGalois.CFT.prod_normalising_factors`: the normalising factors of the product formula, at a
  natural number, multiply to one over such a set.
* `InverseGalois.CFT.prod_index_range_powMonoidHom_units`: **the product of the local indices of the
  `n`-th powers** over the infinite places together with such a finite set of finite places.
* `InverseGalois.CFT.prod_index_range_powMonoidHom_units_of_isPrimitiveRoot`: **the same product
  when the base field contains a primitive `n`-th root of unity**, where every completion has
  exactly `n` roots of unity of order dividing `n`, so that the answer is `n` raised to twice the
  number of places.

## Tags

number field, place, local index, product formula, roots of unity
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### A cancellation lemma -/

/-- Two products whose normalising factors cancel. -/
theorem mul_eq_of_mul_normalising {A B P Q M N c d : ℝ} (h₁ : A * P = c * M) (h₂ : B * Q = d * N)
    (h₃ : P * Q = 1) : A * B = c * d * (M * N) := by
  have h : A * P * (B * Q) = A * B * (P * Q) := by ring
  rw [h₁, h₂, h₃, mul_one] at h
  rw [← h]
  ring

/-! ### The normalising factors at a natural number -/

section Places

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- An infinite place sends a natural number to itself. -/
theorem apply_natCast_infinitePlace (w : InfinitePlace K) (n : ℕ) :
    w ((n : ℕ) : K) = (n : ℝ) := by
  rw [← InfinitePlace.norm_embedding_eq w, map_natCast, Complex.norm_natCast]

/-- The product of the finite absolute values of a number, over a finite set of places carrying all
the places where it is not one. -/
theorem finprod_finitePlace_eq_prod {x : K} (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v, FinitePlace.mk v x ≠ 1 → v ∈ T) :
    ∏ᶠ w : FinitePlace K, w x = ∏ v ∈ T, FinitePlace.mk v x := by
  simp only [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm,
    HeightOneSpectrum.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply]
  exact finprod_eq_prod_of_mulSupport_subset _ fun v hv => Finset.mem_coe.mpr (hT v hv)

/-- **The normalising factors of the product formula, at a natural number**, over the infinite
places together with a finite set of finite places carrying all the finite places where the number
has absolute value different from one. -/
theorem prod_normalising_factors {n : ℕ} (hn : n ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ T) :
    (∏ w : InfinitePlace K, (n : ℝ) ^ w.mult) * ∏ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) = 1 := by
  have hx : ((n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← finprod_finitePlace_eq_prod T hT, ← NumberField.prod_abs_eq_one hx]
  exact congrArg (· * ∏ᶠ w : FinitePlace K, w ((n : ℕ) : K))
    (Finset.prod_congr rfl fun w _ => by rw [apply_natCast_infinitePlace w n])

end Places

/-! ### The product of the local indices -/

section ProductIndex

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
omit [NumberField K] in
/-- The archimedean local index formula, in the reals. -/
theorem index_range_powMonoidHom_units_infinitePlace_real (w : InfinitePlace K) (hn : n ≠ 0) :
    ((powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index : ℝ) * (n : ℝ) ^ w.mult
      = (n : ℝ) * (Nat.card ↥(rootsOfUnity n w.Completion) : ℝ) := by
  exact_mod_cast congrArg (Nat.cast (R := ℝ))
    (index_range_powMonoidHom_units_infinitePlace w hn)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- The archimedean half of the product of the local indices. -/
theorem prod_index_range_powMonoidHom_units_infinite (hn : n ≠ 0) :
    (∏ w : InfinitePlace K,
        ((powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index : ℝ))
      * ∏ w : InfinitePlace K, (n : ℝ) ^ w.mult
      = (n : ℝ) ^ Fintype.card (InfinitePlace K)
        * ∏ w : InfinitePlace K, (Nat.card ↥(rootsOfUnity n w.Completion) : ℝ) :=
  calc (∏ w : InfinitePlace K,
        ((powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index : ℝ))
      * ∏ w : InfinitePlace K, (n : ℝ) ^ w.mult
      = ∏ w : InfinitePlace K,
        ((powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index : ℝ)
          * (n : ℝ) ^ w.mult := Finset.prod_mul_distrib.symm
    _ = ∏ w : InfinitePlace K,
        (n : ℝ) * (Nat.card ↥(rootsOfUnity n w.Completion) : ℝ) :=
      Finset.prod_congr rfl fun w _ => index_range_powMonoidHom_units_infinitePlace_real w hn
    _ = (n : ℝ) ^ Fintype.card (InfinitePlace K)
        * ∏ w : InfinitePlace K, (Nat.card ↥(rootsOfUnity n w.Completion) : ℝ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- The nonarchimedean half of the product of the local indices. -/
theorem prod_index_range_powMonoidHom_units_finite (hn : n ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (∏ v ∈ T, ((powMonoidHom n :
        (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ))
      * ∏ v ∈ T, FinitePlace.mk v ((n : ℕ) : K)
      = (n : ℝ) ^ T.card
        * ∏ v ∈ T, (Nat.card ↥(rootsOfUnity n (v.adicCompletion K)) : ℝ) := by
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun v _ =>
    index_range_powMonoidHom_units_adicCompletion v hn,
    Finset.prod_mul_distrib, Finset.prod_const]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The product of the local indices of the `n`-th powers** over the infinite places together with
a finite set of finite places carrying all the finite places at which `n` has absolute value
different from one.  It is `n` raised to the number of places, times the product of the local
numbers of `n`-th roots of unity. -/
theorem prod_index_range_powMonoidHom_units (hn : n ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ T) :
    (∏ w : InfinitePlace K,
        (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index)
        * ∏ v ∈ T, (powMonoidHom n :
          (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index
      = n ^ (Fintype.card (InfinitePlace K) + T.card)
        * ((∏ w : InfinitePlace K, Nat.card ↥(rootsOfUnity n w.Completion))
          * ∏ v ∈ T, Nat.card ↥(rootsOfUnity n (v.adicCompletion K))) := by
  have key := mul_eq_of_mul_normalising (prod_index_range_powMonoidHom_units_infinite (K := K) hn)
    (prod_index_range_powMonoidHom_units_finite hn T) (prod_normalising_factors hn T hT)
  rw [← pow_add] at key
  exact_mod_cast key

end ProductIndex

/-! ### The product when the base field has enough roots of unity -/

section PrimitiveRoot

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

omit [NumberField K] in
/-- A field extension of one containing a primitive `n`-th root of unity has exactly `n` roots of
unity of order dividing `n`. -/
theorem card_rootsOfUnity_of_isPrimitiveRoot {L : Type*} [Field L] [Algebra K L] [NeZero n]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) : Nat.card ↥(rootsOfUnity n L) = n := by
  rw [Nat.card_eq_fintype_card,
    (hζ.map_of_injective (algebraMap K L).injective).card_rootsOfUnity]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The product of the local indices of the `n`-th powers when the base field contains a primitive
`n`-th root of unity.**  Every completion then has exactly `n` roots of unity of order dividing `n`,
so the product is `n` raised to twice the number of places. -/
theorem prod_index_range_powMonoidHom_units_of_isPrimitiveRoot [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ T) :
    (∏ w : InfinitePlace K,
        (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index)
        * ∏ v ∈ T, (powMonoidHom n :
          (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index
      = n ^ (2 * (Fintype.card (InfinitePlace K) + T.card)) := by
  have h₁ : (∏ w : InfinitePlace K, Nat.card ↥(rootsOfUnity n w.Completion))
      = n ^ Fintype.card (InfinitePlace K) := by
    rw [Finset.prod_congr rfl fun w _ =>
      card_rootsOfUnity_of_isPrimitiveRoot (L := w.Completion) hζ, Finset.prod_const,
      Finset.card_univ]
  have h₂ : (∏ v ∈ T, Nat.card ↥(rootsOfUnity n (v.adicCompletion K))) = n ^ T.card := by
    rw [Finset.prod_congr rfl fun v _ =>
      card_rootsOfUnity_of_isPrimitiveRoot (L := v.adicCompletion K) hζ, Finset.prod_const]
  rw [prod_index_range_powMonoidHom_units (NeZero.ne n) T hT, h₁, h₂, ← pow_add, ← pow_add,
    two_mul]

end PrimitiveRoot

end InverseGalois.CFT
