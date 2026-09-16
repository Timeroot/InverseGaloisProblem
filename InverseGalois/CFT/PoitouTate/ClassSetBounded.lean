/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ClassSetAvoid
import InverseGalois.CFT.Units.ClassPlaces

/-!
# A correction room of a size the field alone decides

A construction that prescribes the orders of an element of a number field has to allow the element
an order nobody asked for at finitely many primes: the **correction room**.  Two things are wanted
of it.  It must avoid the primes some other part of the construction has already spoken for, which
costs nothing but a choice of representatives of the ideal classes.  And its size must be known in
advance, because a count that consumes the units for the correction room as a spanning family has
to fix the size of that family before the primes to be avoided are chosen.

Both are available together.  Keeping one prime for each ideal class occurring in a supporting set
leaves a supporting set of at most as many primes as there are classes; the smaller set is a subset
of the larger, so it still avoids whatever the larger avoided.  Closing under a finite group of
automorphisms multiplies the bound by the order of the group and preserves everything else.  The
resulting bound — the class number, times the degree — belongs to the field and its extension, not
to the primes.

## Main results

* `InverseGalois.CFT.exists_bounded_ord_repr_disjoint`: **a set of primes of at most the class
  number many elements, avoiding a prescribed finite set, away from which every finitely supported
  system of orders is realised.**
* `InverseGalois.CFT.exists_bounded_stable_ord_repr_disjoint`: the same set stable under a finite
  group of automorphisms, at the cost of a factor the order of the group.

## Tags

class group, class number, fractional ideal, prescribed order, number field, place
-/

namespace InverseGalois.CFT

open FractionalIdeal IsDedekindDomain NumberField Rigidity.RET

open scoped nonZeroDivisors

/-! ### A bounded correction room -/

section Bounded

variable (K : Type) [Field K] [NumberField K]

/-- **A set of primes of at most the class number many elements, avoiding a prescribed finite set,
away from which every finitely supported system of orders is realised by an element of the field.**
The set supporting the ideal classes is first moved off the prescribed set, then thinned to one
prime for each ideal class it meets. -/
theorem exists_bounded_ord_repr_disjoint (E : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ X : Set (HeightOneSpectrum (𝓞 K)), X.Finite ∧ (∀ v ∈ X, v ∉ E) ∧
      Nat.card ↥X ≤
        Nat.card ((FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ (toPrincipalIdeal (𝓞 K) K).range) ∧
      ∀ n : HeightOneSpectrum (𝓞 K) → ℤ,
        (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, n v = 0) →
        ∃ a : Kˣ, ∀ v ∉ X, ord K v (a : K) = n v := by
  obtain ⟨X, hXfin, hXE, hXrepr⟩ := exists_finite_ord_repr_disjoint K E
  obtain ⟨A, hAX, hAfin, hAcard, hArepr⟩ := exists_card_le_ord_repr_of_ord_repr K hXfin hXrepr
  exact ⟨A, hAfin, fun v hv => hXE v (hAX hv), hAcard, hArepr⟩

end Bounded

/-! ### Making the bounded correction room invariant -/

section Stable

variable {k : Type*} {K : Type} [Field k] [Field K] [NumberField K] [Algebra k K]
  [Finite Gal(K/k)]

/-- **A set of primes stable under the Galois group, avoiding a prescribed stable finite set,
bounded by the class number times the order of the group, away from which every finitely supported
system of orders is realised by an element of the field.**  The union of the translates of a bounded
set is covered by the group times the set, which is what bounds it. -/
theorem exists_bounded_stable_ord_repr_disjoint (E : Finset (HeightOneSpectrum (𝓞 K)))
    (hE : ∀ (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ E → g • v ∈ E) :
    ∃ X : Set (HeightOneSpectrum (𝓞 K)), X.Finite ∧
      (∀ (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), g • v ∈ X ↔ v ∈ X) ∧
      (∀ v ∈ X, v ∉ E) ∧
      Nat.card ↥X ≤ Nat.card Gal(K/k) *
        Nat.card ((FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ (toPrincipalIdeal (𝓞 K) K).range) ∧
      ∀ n : HeightOneSpectrum (𝓞 K) → ℤ,
        (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, n v = 0) →
        ∃ a : Kˣ, ∀ v ∉ X, ord K v (a : K) = n v := by
  classical
  obtain ⟨A, hAfin, hAE, hAcard, hArepr⟩ := exists_bounded_ord_repr_disjoint K E
  haveI : Finite ↥A := hAfin.to_subtype
  refine ⟨⋃ g : Gal(K/k), (fun v => g • v) '' A, Set.finite_iUnion fun g => hAfin.image _,
    fun g v => ?_, ?_, ?_, fun n hn => ?_⟩
  · constructor
    · rintro hgv
      obtain ⟨s, w, hw, hwv⟩ := Set.mem_iUnion.mp hgv
      refine Set.mem_iUnion.mpr ⟨g⁻¹ * s, w, hw, ?_⟩
      show (g⁻¹ * s) • w = v
      rw [mul_smul, show s • w = g • v from hwv, inv_smul_smul]
    · rintro hv
      obtain ⟨s, w, hw, hwv⟩ := Set.mem_iUnion.mp hv
      refine Set.mem_iUnion.mpr ⟨g * s, w, hw, ?_⟩
      show (g * s) • w = g • v
      rw [mul_smul, show s • w = v from hwv]
  · rintro v hv hvE
    obtain ⟨g, w, hw, hwv⟩ := Set.mem_iUnion.mp hv
    refine hAE w hw ?_
    have hgv : g⁻¹ • v ∈ E := hE g⁻¹ v hvE
    rwa [← show g • w = v from hwv, inv_smul_smul] at hgv
  · have hsurj : Nat.card ↥(⋃ g : Gal(K/k), (fun v => g • v) '' A)
        ≤ Nat.card (Gal(K/k) × ↥A) := by
      refine Nat.card_le_card_of_surjective
        (fun ga => (⟨ga.1 • (ga.2 : HeightOneSpectrum (𝓞 K)),
          Set.mem_iUnion.mpr ⟨ga.1, ga.2, ga.2.2, rfl⟩⟩ :
            ↥(⋃ g : Gal(K/k), (fun v => g • v) '' A))) fun y => ?_
      obtain ⟨g, w, hw, hwv⟩ := Set.mem_iUnion.mp y.2
      exact ⟨(g, ⟨w, hw⟩), Subtype.ext hwv⟩
    refine hsurj.trans ?_
    rw [Nat.card_prod]
    exact Nat.mul_le_mul_left _ hAcard
  · obtain ⟨a, ha⟩ := hArepr n hn
    exact ⟨a, fun v hv => ha v fun hvA =>
      hv (Set.mem_iUnion.mpr ⟨1, v, hvA, one_smul _ v⟩)⟩

end Stable

end InverseGalois.CFT
