/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.SymbolProduct

/-!
# The product formula for the power residue symbol over a field with real places

The product formula for the power residue symbol reads global reciprocity through a cyclic algebra
whose splitting field is the radical extension cutting out a root of the second argument.  Over a
totally complex field the archimedean invariants of a Brauer class all vanish, so reciprocity
leaves exactly the product of the local symbols at the finite places.  A field carrying a real
place is not covered by that argument, and for the exponent two — the one exponent whose roots of
unity a field with a real place can contain — it needs replacing.

The replacement is the observation that an archimedean invariant vanishes as soon as the splitting
field embeds into the reals over the embedding attached to the place: the relative Brauer group of
the completion at a real place is the relative Brauer group of the reals, and it grows along an
algebra map.  For the radical extension cutting out a square root, that embedding exists exactly
when the radicand is not negative at the place.  So the product over the finite places is still
one, for a second argument which is nowhere negative.

## Main results

* `InverseGalois.CFT.infinitePlaceInvariant_eq_one_of_algHom_real`: a Brauer class split by an
  extension embedding into the reals over the embedding attached to a real place has trivial
  invariant at that place.
* `InverseGalois.CFT.finprod_localSymbol_eq_one_of_nonneg`: **the power residue symbols of two
  units of a number field multiply to one over the finite places, for a prime exponent whose roots
  of unity the field contains and a second argument which is not negative at any real place.**
* `InverseGalois.CFT.prod_localSymbol_eq_one_of_nonneg`: the same, read over a finite set of places
  carrying the symbols.

## Tags

power residue symbol, Hilbert symbol, product formula, real place, quadratic extension, Brauer
group, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Polynomial

/-! ### Splitting a Brauer class along a real embedding -/

section RealSplit

variable {k F : Type} [Field k] [NumberField k] [Field F] [Algebra k F]

omit [NumberField k] in
/-- **A Brauer class split by an extension which embeds into the reals over the embedding attached
to a real place has trivial invariant at that place.**  The completion at a real place splits the
same classes as the reals along that embedding, and the classes split by an extension are split by
any extension receiving it. -/
theorem infinitePlaceInvariant_eq_one_of_algHom_real [Algebra k ℝ] {u : InfinitePlace k}
    (hu : u.IsReal) (halg : (algebraMap k ℝ) = (InfinitePlace.embedding_of_isReal hu : k →+* ℝ))
    (ψ : F →ₐ[k] ℝ) {x : BrauerGroup.{0, 0} k} (hx : x ∈ BrauerGroup.relative k F) :
    infinitePlaceInvariant k u x = 1 := by
  rw [infinitePlaceInvariant_eq_one_iff, relative_completion_eq_relative_real k hu halg]
  exact relative_le_relative_of_algHom ψ hx

end RealSplit

/-! ### A square root over the reals -/

/-- The polynomial cutting out a square root of a real number which is not negative splits over the
reals, its two roots being the square roots of that number. -/
theorem splits_X_pow_two_sub_C_of_nonneg {c : ℝ} (hc : 0 ≤ c) :
    Splits (X ^ 2 - C c : ℝ[X]) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r ^ 2 = c := ⟨Real.sqrt c, Real.sq_sqrt hc⟩
  have hfac : (X ^ 2 - C c : ℝ[X]) = (X - C r) * (X - C (-r)) := by
    rw [← hr, map_pow, map_neg]
    ring
  rw [hfac]
  exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)

/-! ### The product formula -/

section Product

variable {k : Type} [Field k] [NumberField k] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 k) → ℕ}

/-- **The power residue symbols of two units of a number field multiply to one over the finite
places**, for an exponent which is prime and whose roots of unity the field contains, and a second
argument which is not negative at any real place.  At a complex place every Brauer class has
trivial invariant.  A real place forces the exponent to be two, because a field containing the
roots of unity of any bigger order is totally complex; the polynomial cutting out a square root of
the second argument then splits over the reals, so the radical extension presenting the cyclic
algebra embeds into the reals over the embedding attached to the place, and the invariant vanishes
there too. -/
theorem finprod_localSymbol_eq_one_of_nonneg (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a b : kˣ)
    (hb : ∀ (u : InfinitePlace k) (hu : u.IsReal),
      0 ≤ InfinitePlace.embedding_of_isReal hu (b : k)) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
          (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1 := by
  refine finprod_localSymbol_eq_one_of_forall_infinitePlaceInvariant hn hres hζ a b
    fun u x hx => ?_
  rcases u.isReal_or_isComplex with hu | hu
  · have hn2 : n = 2 := by
      by_contra hne
      haveI := isTotallyComplex_of_isPrimitiveRoot (lt_of_le_of_ne hn.two_le (Ne.symm hne)) hζ
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex u)) hu
    letI : Algebra k ℝ := (InfinitePlace.embedding_of_isReal hu).toAlgebra
    have hsplit : Splits (((X ^ n - C (b : k)) : k[X]).map (algebraMap k ℝ)) := by
      rw [hn2, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
      exact splits_X_pow_two_sub_C_of_nonneg (hb u hu)
    exact infinitePlaceInvariant_eq_one_of_algHom_real hu rfl
      (IsSplittingField.lift (X ^ n - C (b : k)).SplittingField _ hsplit) hx
  · rw [infinitePlaceInvariant_of_isComplex k hu, MonoidHom.one_apply]

/-- **The product formula for the power residue symbol over a field with real places**, read over a
finite set of finite places outside which the symbols are trivial. -/
theorem prod_localSymbol_eq_one_of_nonneg (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a b : kˣ)
    (hb : ∀ (u : InfinitePlace k) (hu : u.IsReal),
      0 ≤ InfinitePlace.embedding_of_isReal hu (b : k))
    (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hS : ∀ v ∉ S,
      localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1) :
    ∏ v ∈ S, localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1 := by
  have hsub : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 k) =>
      localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b)) ⊆ (S : Set _) := by
    intro v hv
    by_contra hvS
    exact hv (hS v hvS)
  rw [← finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact finprod_localSymbol_eq_one_of_nonneg hn hres hζ a b hb

end Product

end InverseGalois.CFT
