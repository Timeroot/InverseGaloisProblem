/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.SymbolProduct

/-!
# Fields in which minus one is a power of the exponent

The product formula for the power residue symbol over the finite places alone holds whenever the
number field has no real place, and the roots of unity of an odd order bigger than two already
force that.  At the exponent two they do not: the roots of unity of order two lie in every field.
What forces it there is a square root of minus one.

Both cases are covered by one condition, that **minus one be an exponent-th power**.  At an odd
exponent minus one is its own exponent-th power and the condition is empty, so a prime exponent
bigger than two is handled by the roots of unity as before; at the exponent two the condition is
exactly that the field contain a square root of minus one, and then a real embedding is impossible.
The condition is also the one under which the norm residue symbol of an element against itself is
trivial, so it is the single hypothesis carrying the whole of the duality at every prime exponent.

## Main definitions

* `InverseGalois.CFT.IsNegOnePow`: **minus one is an exponent-th power in the field.**

## Main results

* `InverseGalois.CFT.isNegOnePow_of_odd`: an odd exponent asks nothing.
* `InverseGalois.CFT.IsNegOnePow.map`: the condition passes along a homomorphism of fields.
* `InverseGalois.CFT.isTotallyComplex_of_isNegOnePow`: **a number field carrying the roots of unity
  of a prime order in which minus one is a power of that order is totally complex.**
* `InverseGalois.CFT.prod_localSymbol_eq_one_of_isNegOnePow`: **the product formula for the power
  residue symbol over the finite places, at every prime exponent.**

## Tags

power residue symbol, product formula, totally complex, root of unity
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Minus one as a power -/

/-- **Minus one is an exponent-th power in the field.**  At an odd exponent minus one is its own
exponent-th power, so the condition asks nothing; at an even one it asks the field for a root of
minus one of that order. -/
def IsNegOnePow (K : Type) [Field K] (n : ℕ) : Prop := ∃ c : Kˣ, c ^ n = -1

/-- An odd exponent asks nothing: minus one is its own odd power. -/
theorem isNegOnePow_of_odd {K : Type} [Field K] {n : ℕ} (hodd : Odd n) : IsNegOnePow K n :=
  ⟨-1, hodd.neg_one_pow⟩

/-- Minus one stays an exponent-th power along a homomorphism of fields. -/
theorem IsNegOnePow.map {K L : Type} [Field K] [Field L] {n : ℕ} (h : IsNegOnePow K n)
    (f : K →+* L) : IsNegOnePow L n := by
  obtain ⟨c, hc⟩ := h
  have hcv : ((c : K)) ^ n = -1 := by simpa using congrArg Units.val hc
  refine ⟨Units.map (f : K →* L) c, Units.ext ?_⟩
  have hfc : f (((c : K)) ^ n) = f (-1) := by rw [hcv]
  simpa using hfc

/-! ### No real place -/

section Place

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

omit [NumberField K] in
/-- A field in which minus one is an even power has no real place: a real embedding would turn the
witness into a real number an even power of which is negative. -/
theorem not_isReal_of_isNegOnePow (h : IsNegOnePow K n) (hn : 2 ∣ n) (w : InfinitePlace K) :
    ¬ w.IsReal := by
  intro hw
  obtain ⟨j, rfl⟩ := hn
  obtain ⟨c, hc⟩ := h.map (InfinitePlace.embedding_of_isReal hw)
  have hcv : ((c : ℝ)) ^ (2 * j) = -1 := by simpa using congrArg Units.val hc
  have hpos : (0 : ℝ) ≤ ((c : ℝ)) ^ (2 * j) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) j
  rw [hcv] at hpos
  norm_num at hpos

/-- **A number field carrying the roots of unity of a prime order in which minus one is a power of
that order is totally complex.**  At an odd prime the roots of unity already force it; at the
exponent two the witness is a square root of minus one. -/
theorem isTotallyComplex_of_isNegOnePow (hn : n.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (h : IsNegOnePow K n) : IsTotallyComplex K := by
  rcases eq_or_lt_of_le hn.two_le with h2 | h2
  · exact ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1
      (not_isReal_of_isNegOnePow h ⟨1, by omega⟩ w)⟩
  · exact isTotallyComplex_of_isPrimitiveRoot h2 hζ

end Place

/-! ### The product formula at every prime exponent -/

section Product

variable {k : Type} [Field k] [NumberField k] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 k) → ℕ}

/-- **The product formula for the power residue symbol at every prime exponent**: minus one being
a power of that order makes the field totally complex, whether the order is two or not. -/
theorem finprod_localSymbol_eq_one_of_isNegOnePow (hn : n.Prime) (hneg : IsNegOnePow k n)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a b : kˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
          (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1 := by
  haveI := isTotallyComplex_of_isNegOnePow hn hζ hneg
  exact finprod_localSymbol_eq_one hn hres hζ a b

/-- **The product formula for the power residue symbol at every prime exponent**, read over a
finite set of finite places outside which the symbols are trivial. -/
theorem prod_localSymbol_eq_one_of_isNegOnePow (hn : n.Prime) (hneg : IsNegOnePow k n)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a b : kˣ) (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hS : ∀ v ∉ S,
      localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1) :
    ∏ v ∈ S, localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1 := by
  haveI := isTotallyComplex_of_isNegOnePow hn hζ hneg
  exact prod_localSymbol_eq_one hn hres hζ a b S hS

end Product

end InverseGalois.CFT
