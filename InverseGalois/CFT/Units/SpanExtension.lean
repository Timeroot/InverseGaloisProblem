/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.SpanSubgroup

/-!
# Spanning an extension, and padding a spanning family

A group presented as an extension is spanned by the generators of its subobject together with
lifts of the generators of its quotient: an element is congruent, modulo the lifts, to an element
of the subobject.  Reading the extension as a linear map, the subobject is the kernel and the
quotient is the range, and the count of generators simply adds.

Two smaller conveniences travel with it.  A spanning family may always be padded with zeroes up to
any larger size, which is what lets a bound on the size of a set of places be used in place of the
size itself.  And the functions from a finite set to the integers are spanned by as many elements
as the set has, namely the indicators of its points, which is the spanning family the orders at a
finite set of places are read against.

## Main results

* `InverseGalois.CFT.exists_fin_span_of_le`: a spanning family may be padded up to any larger size.
* `InverseGalois.CFT.exists_fin_span_pi`: **the functions from a finite set to the integers are
  spanned by as many elements as the set has.**
* `InverseGalois.CFT.exists_fin_span_of_ker_range`: **a module whose kernel is spanned by `d₁`
  elements and whose range is spanned by `d₂` elements is spanned by `d₁ + d₂` elements.**

## Tags

spanning family, extension, free module, generators, rank
-/

namespace InverseGalois.CFT

/-! ### Padding a spanning family -/

section Pad

variable {V : Type*} [AddCommGroup V] {d d' : ℕ}

/-- **A spanning family may be padded with zeroes up to any larger size.**  This is how a bound on
the number of generators is used where a number of generators is asked for. -/
theorem exists_fin_span_of_le (h : d ≤ d') (b : Fin d → V)
    (hb : Submodule.span ℤ (Set.range b) = ⊤) :
    ∃ c : Fin d' → V, Submodule.span ℤ (Set.range c) = ⊤ := by
  classical
  refine ⟨fun i => if hi : (i : ℕ) < d then b ⟨i, hi⟩ else 0, ?_⟩
  refine eq_top_iff.2 ?_
  rw [← hb]
  refine Submodule.span_mono ?_
  rintro y ⟨j, rfl⟩
  exact ⟨⟨(j : ℕ), lt_of_lt_of_le j.2 h⟩, by simp⟩

end Pad

/-! ### The functions from a finite set -/

section Pi

/-- **The functions from a finite set to the integers are spanned by as many elements as the set
has**, the indicators of its points. -/
theorem exists_fin_span_pi (Y : Type*) [Fintype Y] :
    ∃ b : Fin (Nat.card Y) → (Y → ℤ), Submodule.span ℤ (Set.range b) = ⊤ := by
  classical
  set e : Fin (Nat.card Y) ≃ Y :=
    (finCongr (Nat.card_eq_fintype_card (α := Y))).trans (Fintype.equivFin Y).symm with he
  refine ⟨fun i => Pi.basisFun ℤ Y (e i), ?_⟩
  have h1 : Set.range (fun i => (Pi.basisFun ℤ Y) (e i)) = Set.range ⇑(Pi.basisFun ℤ Y) :=
    e.surjective.range_comp ⇑(Pi.basisFun ℤ Y)
  rw [h1]
  exact (Pi.basisFun ℤ Y).span_eq

end Pi

/-! ### The generators of an extension -/

section Extension

variable {B C : Type*} [AddCommGroup B] [AddCommGroup C] {d₁ d₂ : ℕ}

/-- **A module whose kernel under a linear map is spanned by `d₁` elements and whose range is
spanned by `d₂` elements is spanned by `d₁ + d₂` elements.**  Lift the spanning family of the range
along the map; an element differs from a combination of the lifts by an element of the kernel. -/
theorem exists_fin_span_of_ker_range (f : B →ₗ[ℤ] C)
    (a : Fin d₁ → ↥(LinearMap.ker f)) (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (c : Fin d₂ → ↥(LinearMap.range f)) (hc : Submodule.span ℤ (Set.range c) = ⊤) :
    ∃ b : Fin (d₁ + d₂) → B, Submodule.span ℤ (Set.range b) = ⊤ := by
  classical
  choose s hs using fun j : Fin d₂ => LinearMap.mem_range.1 (c j).2
  set b : Fin (d₁ + d₂) → B := fun i =>
    Sum.elim (fun i' : Fin d₁ => ((a i' : ↥(LinearMap.ker f)) : B)) s
      (finSumFinEquiv.symm i) with hbdef
  refine ⟨b, eq_top_iff.2 fun x _ => ?_⟩
  set M : Submodule ℤ B := Submodule.span ℤ (Set.range b) with hM
  have hmemA : ∀ i' : Fin d₁, ((a i' : ↥(LinearMap.ker f)) : B) ∈ M := by
    intro i'
    refine Submodule.subset_span ⟨finSumFinEquiv (Sum.inl i'), ?_⟩
    simp [hbdef]
  have hmemS : ∀ j : Fin d₂, s j ∈ M := by
    intro j
    refine Submodule.subset_span ⟨finSumFinEquiv (Sum.inr j), ?_⟩
    simp [hbdef]
  set N : Submodule ℤ ↥(LinearMap.range f) :=
    (M.map f).comap (LinearMap.range f).subtype with hN
  have hNtop : N = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hc]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨s j, hmemS j, hs j⟩
  have hxN : (⟨f x, ⟨x, rfl⟩⟩ : ↥(LinearMap.range f)) ∈ N := hNtop ▸ Submodule.mem_top
  have hxmap : f x ∈ Submodule.map f M := hxN
  obtain ⟨z, hzM, hz⟩ := Submodule.mem_map.1 hxmap
  have hkerxz : x - z ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hz, sub_self]
  set P : Submodule ℤ ↥(LinearMap.ker f) := M.comap (LinearMap.ker f).subtype with hP
  have hPtop : P = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← ha]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i', rfl⟩
    exact hmemA i'
  have hxzP : (⟨x - z, hkerxz⟩ : ↥(LinearMap.ker f)) ∈ P := hPtop ▸ Submodule.mem_top
  have hxzM : x - z ∈ M := hxzP
  have hsum : x = (x - z) + z := by abel
  rw [hsum]
  exact M.add_mem hxzM hzM

end Extension

end InverseGalois.CFT
