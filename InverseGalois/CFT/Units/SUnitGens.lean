/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.SUnit
import InverseGalois.CFT.Units.SpanExtension

/-!
# How many generators the units for a finite set of primes need

The units for a finite set of primes of a number field sit in an extension: the units of the ring
of integers, with the orders at the chosen primes for quotient.  The quotient is a subgroup of the
free abelian group on the chosen primes, so it needs no more generators than there are primes, and
the number of generators of the whole group is at most the number of generators of the units of the
ring of integers plus the number of chosen primes.

The point of counting rather than merely being finitely generated is an ordering one.  A count of a
cohomology class consumes its coefficients as a spanning family of a definite size, and that size
enters the count before the coefficients are known.  Here the size is bounded by the number of
primes alone, so a bound on the number of primes — even when the primes themselves are chosen much
later — already fixes the size.

## Main results

* `InverseGalois.CFT.exists_fin_span_sUnits`: **the units for a finite set of primes are spanned by
  the generators of the units of the ring of integers together with one element for each prime.**
* `InverseGalois.CFT.exists_fin_span_sUnits_of_card_le`: the same against a bound on the number of
  primes, which is the form an ordering constraint consumes.

## Tags

number field, S-unit, Dirichlet unit theorem, generators, spanning family
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Gens

variable {K : Type*} [Field K] [NumberField K]

/-- **The units for a finite set of primes are spanned by the generators of the units of the ring
of integers together with one element for each prime.**  The orders at the chosen primes present
the group as an extension whose kernel is the units of the ring of integers and whose range is a
subgroup of the free abelian group on the primes. -/
theorem exists_fin_span_sUnits (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    {d₁ : ℕ} (a : Fin d₁ → Additive (𝓞 K)ˣ) (ha : Submodule.span ℤ (Set.range a) = ⊤) :
    ∃ b : Fin (d₁ + Nat.card ↥S) → Additive ↥(sUnits K S),
      Submodule.span ℤ (Set.range b) = ⊤ := by
  classical
  haveI : Finite ↥S := hS.to_subtype
  haveI : Fintype ↥S := Fintype.ofFinite ↥S
  have hrange : Set.range (Subtype.val : ↥S → HeightOneSpectrum (𝓞 K)) = S := Subtype.range_coe
  set ι : ↥S → HeightOneSpectrum (𝓞 K) := Subtype.val with hι
  set f : Additive ↥(sUnits K (Set.range ι)) →ₗ[ℤ] (↥S → ℤ) :=
    AddMonoidHom.toIntLinearMap (sUnitsVal K ι) with hf
  have hmem : ∀ u : Additive (𝓞 K)ˣ,
      unitsToSUnits K (Set.range ι) u ∈ LinearMap.ker f := by
    intro u
    have h1 : unitsToSUnits K (Set.range ι) u ∈ (sUnitsVal K ι).ker := by
      rw [← range_unitsToSUnits (K := K) ι]
      exact ⟨u, rfl⟩
    exact LinearMap.mem_ker.2 (AddMonoidHom.mem_ker.1 h1)
  set g : Additive (𝓞 K)ˣ →ₗ[ℤ] ↥(LinearMap.ker f) :=
    LinearMap.codRestrict (LinearMap.ker f)
      (AddMonoidHom.toIntLinearMap (unitsToSUnits K (Set.range ι))) hmem with hg
  have hgsurj : Function.Surjective g := by
    intro y
    have h1 : (y : Additive ↥(sUnits K (Set.range ι))) ∈ (sUnitsVal K ι).ker :=
      AddMonoidHom.mem_ker.2 (LinearMap.mem_ker.1 y.2)
    rw [← range_unitsToSUnits (K := K) ι] at h1
    obtain ⟨u, hu⟩ := h1
    exact ⟨u, Subtype.ext hu⟩
  have ha' : Submodule.span ℤ (Set.range fun i => g (a i)) = ⊤ := by
    have h1 : Set.range (fun i => g (a i)) = Set.range (⇑g ∘ a) := rfl
    rw [h1, Set.range_comp, ← Submodule.map_span, ha, Submodule.map_top]
    exact LinearMap.range_eq_top.2 hgsurj
  obtain ⟨p, hp⟩ := exists_fin_span_pi ↥S
  obtain ⟨c, hc⟩ := exists_fin_span_submodule p hp (LinearMap.range f)
  have key := exists_fin_span_of_ker_range f (fun i => g (a i)) ha' c hc
  rwa [hrange] at key

/-- **The units for a set of primes bounded in number are spanned by a number of elements bounded
in advance.**  This is the form an ordering constraint consumes: the bound on the number of primes
is known before the primes are. -/
theorem exists_fin_span_sUnits_of_card_le (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    {d₁ c : ℕ} (a : Fin d₁ → Additive (𝓞 K)ˣ) (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (hcard : Nat.card ↥S ≤ c) :
    ∃ b : Fin (d₁ + c) → Additive ↥(sUnits K S), Submodule.span ℤ (Set.range b) = ⊤ := by
  obtain ⟨b, hb⟩ := exists_fin_span_sUnits S hS a ha
  exact exists_fin_span_of_le (Nat.add_le_add_left hcard d₁) b hb

end Gens

end InverseGalois.CFT
