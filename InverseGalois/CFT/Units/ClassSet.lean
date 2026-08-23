/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.Places

/-!
# A finite set of primes carrying the ideal classes

The ideles of a number field are not the ideles that are units outside a finite set of places, but
they differ from them only by a principal idele, and the reason is the finiteness of the class
number.  This file records the finiteness statement in the form the comparison needs: there is a
finite set `T` of primes such that every prescribed system of orders, vanishing at all but finitely
many primes, is realised away from `T` by a single element of the field.

The set is obtained by choosing one fractional ideal in each ideal class and collecting the primes
where those finitely many representatives are not trivial.  A system of orders is the exponent
vector of a fractional ideal; that ideal lies in the class of one of the representatives, so it
differs from the representative by a principal ideal, and away from `T` the representative
contributes nothing.  Enlarging `T` to the union of its translates makes it stable under a finite
group of automorphisms without disturbing the property, which is what the equivariant computation of
the Herbrand quotient requires.

## Main results

* `InverseGalois.CFT.exists_finite_ord_repr`: **a finite set of primes away from which every
  finitely supported system of orders is realised by an element of the field.**
* `InverseGalois.CFT.exists_finite_stable_ord_repr`: **the same set may be taken stable under the
  Galois group.**

## Tags

number field, class group, fractional ideal, order, idele
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField FractionalIdeal Rigidity.RET

open scoped nonZeroDivisors

/-! ### The set attached to the ideal classes -/

section ClassSet

variable (K : Type*) [Field K] [NumberField K]

/-- **A finite set of primes away from which every finitely supported system of orders is realised
by an element of the field.**  Choose one fractional ideal in each of the finitely many ideal
classes and let the set be the primes where some representative is nontrivial.  A system of orders
is the exponent vector of a fractional ideal, which differs from the representative of its class by
a principal ideal; away from the chosen set the representative has no exponent, so the generator of
that principal ideal has the prescribed orders there. -/
theorem exists_finite_ord_repr :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
      ∀ n : HeightOneSpectrum (𝓞 K) → ℤ,
        (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, n v = 0) →
        ∃ a : Kˣ, ∀ v ∉ T, ord K v (a : K) = n v := by
  classical
  have hsurj : ∀ c : ClassGroup (𝓞 K), ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk I = c :=
    fun c => ClassGroup.induction (K := K) (P := fun c => ∃ I, ClassGroup.mk I = c)
      (fun I => ⟨I, rfl⟩) c
  choose rep hrep using hsurj
  refine ⟨⋃ c : ClassGroup (𝓞 K),
      {v | FractionalIdeal.count K v (rep c : FractionalIdeal (𝓞 K)⁰ K) ≠ 0}, ?_, ?_⟩
  · exact Set.finite_iUnion fun c =>
      Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors _)
  intro n hn
  set I : FractionalIdeal (𝓞 K)⁰ K := ∏ᶠ v, (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n v with hIdef
  have hcount : ∀ v, FractionalIdeal.count K v I = n v := fun v =>
    FractionalIdeal.count_finprod K v n hn
  by_cases hI0 : I = 0
  · refine ⟨1, fun v _ => ?_⟩
    have hv := hcount v
    rw [hI0, FractionalIdeal.count_zero] at hv
    rw [← hv]
    simp
  set Iu : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 I hI0 with hIuDef
  have h2 : (QuotientGroup.mk' (toPrincipalIdeal (𝓞 K) K).range) Iu
      = (QuotientGroup.mk' (toPrincipalIdeal (𝓞 K) K).range) (rep (ClassGroup.mk Iu)) := by
    have h := congrArg (ClassGroup.equiv K) (hrep (ClassGroup.mk Iu)).symm
    simpa using h
  rw [QuotientGroup.mk'_eq_mk'] at h2
  obtain ⟨z, ⟨x, rfl⟩, hz⟩ := h2
  refine ⟨x⁻¹, fun v hv => ?_⟩
  have hvT : FractionalIdeal.count K v (rep (ClassGroup.mk Iu) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    by_contra hc
    exact hv (Set.mem_iUnion.mpr ⟨ClassGroup.mk Iu, hc⟩)
  have hzz := congrArg (fun u : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
    FractionalIdeal.count K v (u : FractionalIdeal (𝓞 K)⁰ K)) hz
  simp only [Units.val_mul, coe_toPrincipalIdeal] at hzz
  rw [FractionalIdeal.count_mul K v (Units.ne_zero Iu)
    (spanSingleton_ne_zero_iff.mpr (Units.ne_zero x)), hvT] at hzz
  have hIuval : (Iu : FractionalIdeal (𝓞 K)⁰ K) = I := rfl
  rw [hIuval, hcount v] at hzz
  have hx : ord K v ((x : K)) = -n v := by
    rw [ord_def]
    lia
  rw [Units.val_inv_eq_inv_val, ord_inv, hx, neg_neg]

end ClassSet

/-! ### Making the set invariant -/

section Stable

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]

/-- **A finite set of primes, stable under the Galois group, away from which every finitely
supported system of orders is realised by an element of the field.**  Replacing the set attached to
the ideal classes by the union of its translates makes it invariant, keeps it finite, and only
enlarges it, so the property is retained. -/
theorem exists_finite_stable_ord_repr :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
      (∀ (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), g • v ∈ T ↔ v ∈ T) ∧
      ∀ n : HeightOneSpectrum (𝓞 K) → ℤ,
        (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, n v = 0) →
        ∃ a : Kˣ, ∀ v ∉ T, ord K v (a : K) = n v := by
  obtain ⟨T, hTfin, hTrepr⟩ := exists_finite_ord_repr K
  refine ⟨⋃ g : Gal(K/k), (fun v => g • v) '' T, Set.finite_iUnion fun g => hTfin.image _,
    fun g v => ?_, fun n hn => ?_⟩
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
  · obtain ⟨a, ha⟩ := hTrepr n hn
    exact ⟨a, fun v hv => ha v fun hvT =>
      hv (Set.mem_iUnion.mpr ⟨1, v, hvT, one_smul _ v⟩)⟩

end Stable

end InverseGalois.CFT
