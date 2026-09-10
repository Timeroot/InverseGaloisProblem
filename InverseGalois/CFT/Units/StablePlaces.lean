/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ClassSet
import InverseGalois.CFT.Units.FirstInequality
import InverseGalois.CFT.Units.PrimeAbove

/-!
# A stable set of places carrying the classes and the exponent

Constructions that prescribe local behaviour at a finite set of places of a number field ask three
things of that set at once: that it be stable under the Galois group over the base field, so that
a conjugate of a prescribed place is again prescribed; that it contain the places dividing the
exponent, so that the wild places are never among the free ones; and that it be large enough to
carry the ideal classes, so that an arbitrary system of orders away from it comes from an element
of the field.

This file assembles a single finite set with all three properties, starting from any finite set of
places one wishes to include.  Two ingredients do the work.  The first is the finiteness of the
places above a nonzero natural number, which is the finiteness of the prime factors of the ideal
that number generates.  The second is the set carrying the ideal classes, which is already stable,
so it can simply be adjoined; stability of the rest is arranged by passing to the union of the
translates, and enlarging the set only weakens the condition on the systems of orders.

## Main results

* `InverseGalois.CFT.finite_setOf_finitePlace_natCast_ne_one`: only finitely many places of a
  number field carry a given nonzero natural number.
* `InverseGalois.CFT.exists_stable_ord_places`: every finite set of places lies inside a finite
  Galois stable set of places which contains the places above a prescribed exponent and away from
  which every finitely supported system of orders is realised by an element of the field.

## Tags

class field theory, place, ideal class group, Galois stable set
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### The places above a natural number -/

section Above

variable {K : Type*} [Field K] [NumberField K]

/-- **Only finitely many places of a number field carry a given nonzero natural number.** -/
theorem finite_setOf_finitePlace_natCast_ne_one {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | FinitePlace.mk v ((n : ℕ) : K) ≠ 1}.Finite := by
  have hne : Ideal.span {((n : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast Nat.cast_ne_zero.2 hn
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  rw [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  by_contra hcon
  exact hv ((finitePlace_natCast_eq_one_iff v n).2 hcon)

end Above

/-! ### A stable set of places carrying the ideal classes and the exponent -/

section Assemble

variable (k K : Type*) [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]

/-- **Every finite set of places of a number field sits inside a finite set of places, stable
under the Galois group over a base field, which contains the places above a prescribed exponent
and away from which every finitely supported system of orders is realised by an element of the
field.** -/
theorem exists_stable_ord_places {ℓ : ℕ} (hℓ : ℓ ≠ 0) (X : Set (HeightOneSpectrum (𝓞 K)))
    (hX : X.Finite) :
    ∃ Tn : Finset (HeightOneSpectrum (𝓞 K)), X ⊆ (Tn : Set (HeightOneSpectrum (𝓞 K))) ∧
      (∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((ℓ : ℕ) : K) ≠ 1 → v ∈ Tn) ∧
      ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
        (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
        ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))), ord K v (a : K) = m v := by
  classical
  obtain ⟨T, hTfin, hTst, hTrepr⟩ := exists_finite_stable_ord_repr (k := k) (K := K)
  obtain ⟨Y, hXY, hYfin, hYst⟩ := exists_finite_stable_superset (G := Gal(K/k))
    (X ∪ {v : HeightOneSpectrum (𝓞 K) | FinitePlace.mk v ((ℓ : ℕ) : K) ≠ 1})
    (hX.union (finite_setOf_finitePlace_natCast_ne_one hℓ))
  refine ⟨(hTfin.union hYfin).toFinset, fun v hv => ?_, fun σ v hv => ?_, fun v hv => ?_,
    fun m hm => ?_⟩
  · exact (Set.Finite.mem_toFinset _).2 (Or.inr (hXY (Or.inl hv)))
  · rw [Set.Finite.mem_toFinset] at hv ⊢
    exact hv.elim (fun h => Or.inl ((hTst σ v).2 h)) fun h => Or.inr ((hYst σ v).2 h)
  · exact (Set.Finite.mem_toFinset _).2 (Or.inr (hXY (Or.inr hv)))
  · obtain ⟨a, ha⟩ := hTrepr m hm
    refine ⟨a, fun v hv => ha v fun hc => hv ?_⟩
    exact (Set.Finite.mem_toFinset _).2 (Or.inl hc)

end Assemble

end InverseGalois.CFT
