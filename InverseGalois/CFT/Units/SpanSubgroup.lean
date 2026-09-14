/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A subgroup is spanned by no more elements than the group

A count of a cohomology class against its coefficients consumes the coefficients as a spanning
family of a fixed size, and the size enters the count before the class does.  The coefficients that
actually arise are subgroups of a group fixed in advance — the units for a finite set of places —
cut out by conditions which are only known once the class is.  What is needed is therefore that the
size of a spanning family may be read off the ambient group alone.

Over the integers it can.  A family of `d` elements spanning a group is a surjection onto it from
the free module on `d` letters; the preimage of a subgroup is a submodule of that free module, free
of rank at most `d` because the integers are a principal ideal domain, and a basis of it is carried
onto a spanning family of the subgroup.  Padding with zeroes brings the family back up to `d`
elements, so **every subgroup of a group spanned by `d` elements is spanned by `d` elements**.

## Main results

* `InverseGalois.CFT.exists_fin_span_submodule`: **a submodule of a module spanned by `d` elements
  is spanned by `d` elements.**
* `InverseGalois.CFT.exists_fin_span_of_injective`: the same read along an injection, which is how
  a group presented as a subgroup of another one consumes it.

## Tags

principal ideal domain, free module, spanning family, subgroup, rank
-/

namespace InverseGalois.CFT

/-! ### A submodule over the integers -/

section Span

variable {V : Type*} [AddCommGroup V] {d : ℕ}

/-- **A submodule of a module over the integers spanned by `d` elements is spanned by `d`
elements.**  The preimage of the submodule under the surjection from the free module on `d` letters
named by the spanning family is free of rank at most `d`, and a basis of it is carried onto a
spanning family of the submodule. -/
theorem exists_fin_span_submodule (b : Fin d → V) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (N : Submodule ℤ V) : ∃ c : Fin d → ↥N, Submodule.span ℤ (Set.range c) = ⊤ := by
  classical
  set p : (Fin d → ℤ) →ₗ[ℤ] V := Fintype.linearCombination ℤ b with hp
  have hsurj : Function.Surjective p :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination (R := ℤ) (v := b)).1 hb
  set P : Submodule ℤ (Fin d → ℤ) := N.comap p with hP
  set q : ↥P →ₗ[ℤ] ↥N := p.restrict (fun _ hx => hx) with hq
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (y : V)
    have hxP : x ∈ P := by
      show p x ∈ N
      rw [hx]
      exact y.2
    exact ⟨⟨x, hxP⟩, Subtype.ext hx⟩
  have hfin : Module.finrank ℤ ↥P ≤ d := by
    have h1 : Module.finrank ℤ ↥P ≤ Module.finrank ℤ (Fin d → ℤ) := Submodule.finrank_le P
    simpa using h1
  set e := Module.finBasis ℤ ↥P with he
  have key : Submodule.span ℤ (Set.range (⇑q ∘ ⇑e)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, e.span_eq, Submodule.map_top]
    exact LinearMap.range_eq_top.2 hqsurj
  refine ⟨fun i => if h : (i : ℕ) < Module.finrank ℤ ↥P then q (e ⟨i, h⟩) else 0, ?_⟩
  refine eq_top_iff.2 ?_
  rw [← key]
  refine Submodule.span_mono ?_
  rintro y ⟨j, rfl⟩
  have hj : (j : ℕ) < d := lt_of_lt_of_le j.2 hfin
  exact ⟨⟨(j : ℕ), hj⟩, by simp⟩

end Span

/-! ### The same read along an injection -/

section Injective

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W] {d : ℕ}

/-- **A group which injects into a group spanned by `d` elements is spanned by `d` elements.**  This
is the form a subgroup presented by an inclusion consumes: the range of the injection is a submodule
of the ambient group, spanned by `d` elements, and the injection identifies the group with it. -/
theorem exists_fin_span_of_injective (b : Fin d → V) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (f : W →+ V) (hf : Function.Injective f) :
    ∃ c : Fin d → W, Submodule.span ℤ (Set.range c) = ⊤ := by
  classical
  set g : W →ₗ[ℤ] V := AddMonoidHom.toIntLinearMap f with hg
  have hginj : Function.Injective g := hf
  obtain ⟨c, hc⟩ := exists_fin_span_submodule b hb (LinearMap.range g)
  set E : W ≃ₗ[ℤ] ↥(LinearMap.range g) := LinearEquiv.ofInjective g hginj with hE
  set F : ↥(LinearMap.range g) →ₗ[ℤ] W := (E.symm : ↥(LinearMap.range g) →ₗ[ℤ] W) with hF
  have hFsurj : Function.Surjective F := E.symm.surjective
  refine ⟨fun i => F (c i), ?_⟩
  have h1 : Set.range (fun i => F (c i)) = Set.range (⇑F ∘ c) := rfl
  rw [h1, Set.range_comp, ← Submodule.map_span, hc, Submodule.map_top]
  exact LinearMap.range_eq_top.2 hFsurj

end Injective

end InverseGalois.CFT
