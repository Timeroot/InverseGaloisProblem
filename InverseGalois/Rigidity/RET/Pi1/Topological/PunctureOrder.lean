/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.Braid
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureConj
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureHom
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureInertia

/-!
# Prescribing the monodromy at the punctures in a prescribed order

A system of loops of the punctured plane, one around each puncture, meets the punctures in an
order of its own — the order in which the product of the loops is read.  Prescribing the monodromy
in a *different* order is still possible, and this file proves it: the ordered product of a system
of puncture loops depends on the order only up to conjugacy of the individual factors, and the
Hurwitz moves realize every permutation of the conjugacy classes of a generating product-one tuple
(`Rigidity.exists_braidConj_perm`).  So the prescribed tuple is first reordered, within its braid
class, into the order the loops provide; the values obtained on the loops are then conjugates of
the prescribed ones, and conjugating each loop — which leaves it a loop around its puncture — makes
them equal.

The result is the classical form of the branch-cycle description: for *any* enumeration of the
punctures, a generating product-one tuple is the tuple of monodromies at the punctures, in that
order, of a surjection which is trivial at infinity.

## Main results

* `Rigidity.RET.exists_hom_punctureLoops_ordered` — the monodromy at the punctures prescribed in a
  prescribed order.
* `Rigidity.RET.exists_hom_punctureLoops_ordered_inertia` — the same, with each prescribed element
  generating the whole local monodromy at its puncture.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-- **A generating product-one tuple is the monodromy at the punctures, in any prescribed order.**

Given an enumeration `pt` of the punctures and a tuple `h` in a finite group whose ordered product
is trivial and which generates, there are loops `δᵢ`, one winding once around `pt i`, and a
surjection from the fundamental group of the punctured plane carrying `δᵢ` to `hᵢ` and a loop
supported at infinity to the identity. -/
theorem exists_hom_punctureLoops_ordered (S : Finset ℂ) {z₀ : ℂ} (hz₀ : z₀ ∈ ((S : Set ℂ))ᶜ)
    (pt : Fin S.card → ℂ) (hrange : Set.range pt = (S : Set ℂ))
    {H : Type} [Group H] [Finite H] (h : Fin S.card → H)
    (hprod : (List.ofFn h).prod = 1) (hgen : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (δ : Fin S.card → FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩)
      (loopInf : FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩)
      (φ : FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩ →* H),
      (∀ i : Fin S.card, IsPunctureLoop ((S : Set ℂ))ᶜ (pt i) hz₀ (δ i)) ∧
        IsSupportedAtInfinity ((S : Set ℂ))ᶜ hz₀ loopInf ∧
        Function.Surjective φ ∧ (∀ i : Fin S.card, φ (δ i) = h i) ∧ φ loopInf = 1 := by
  classical
  obtain ⟨r, pt', γ, hinj', hrange', hloop, hprodγ, hgenγ, hinf⟩ :=
    exists_punctureLoops_prodOne_compl S.finite_toSet hz₀
  obtain rfl : r = S.card := card_eq_of_range_eq_coe hinj' hrange'
  -- the permutation matching the enumeration carried by the loops with the prescribed one
  have hex : ∀ j : Fin S.card, ∃ i, pt i = pt' j := by
    intro j
    have hmem : pt' j ∈ Set.range pt := by rw [hrange, ← hrange']; exact ⟨j, rfl⟩
    exact hmem
  have hf : ∀ j, pt ((hex j).choose) = pt' j := fun j => (hex j).choose_spec
  have hfinj : Function.Injective fun j => (hex j).choose := by
    intro a b hab
    apply hinj'
    rw [← hf a, ← hf b]
    exact congrArg pt hab
  obtain ⟨perm, hp⟩ : ∃ perm : Equiv.Perm (Fin S.card), ∀ j, pt (perm j) = pt' j :=
    ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hfinj), hf⟩
  -- reorder the prescribed tuple, within its braid class, into the order the loops provide
  obtain ⟨k, hbc, hk⟩ := exists_braidConj_perm perm h
  have hmemh : h ∈ nielsenTuples fun i => ConjClasses.mk (h i) := ⟨⟨1, fun i => rfl⟩, hprod, hgen⟩
  obtain ⟨-, hprodk, hgenk⟩ := hbc.mem_nielsenTuples hmemh
  obtain ⟨φ, hsurj, hval, hlast⟩ :=
    exists_hom_of_generating_loops S hz₀ γ hprodγ hgenγ k hprodk hgenk
  -- conjugate each loop so that its value is the prescribed one
  have hstep : ∀ i : Fin S.card, ∃ d : FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩,
      IsPunctureLoop ((S : Set ℂ))ᶜ (pt i) hz₀ d ∧ φ d = h i := by
    intro i
    have hpt : pt' (perm.symm i) = pt i := by rw [← hp (perm.symm i), Equiv.apply_symm_apply]
    have hloopi : IsPunctureLoop ((S : Set ℂ))ᶜ (pt i) hz₀ (γ (perm.symm i).castSucc) := by
      rw [← hpt]; exact hloop (perm.symm i)
    have hconj : IsConj (h i) (k (perm.symm i)) := by
      rw [← ConjClasses.mk_eq_mk_iff_isConj, hk (perm.symm i), Equiv.apply_symm_apply]
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    obtain ⟨w, hw⟩ := hsurj c
    refine ⟨w⁻¹ * γ (perm.symm i).castSucc * w, ?_, ?_⟩
    · have hcj := hloopi.conj w⁻¹
      rwa [inv_inv] at hcj
    · rw [map_mul, map_mul, map_inv, hw, hval (perm.symm i), ← hc]
      group
  choose δ hδloop hδval using hstep
  exact ⟨δ, γ (Fin.last S.card), φ, hδloop, hinf, hsurj, hδval, hlast⟩

/-- **A generating product-one tuple is the monodromy at the punctures, in any prescribed order,
and each of its members generates the whole local monodromy at its puncture.**

The last clause is the topological form of the statement that a branch cycle *generates* the
inertia group at its branch point: a small punctured disc about `pt i` contributes to the monodromy
exactly the cyclic group generated by `h i`. -/
theorem exists_hom_punctureLoops_ordered_inertia (S : Finset ℂ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ ((S : Set ℂ))ᶜ) (pt : Fin S.card → ℂ) (hrange : Set.range pt = (S : Set ℂ))
    {H : Type} [Group H] [Finite H] (h : Fin S.card → H)
    (hprod : (List.ofFn h).prod = 1) (hgen : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (δ : Fin S.card → FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩)
      (loopInf : FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩)
      (φ : FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩ →* H),
      (∀ i : Fin S.card, IsPunctureLoop ((S : Set ℂ))ᶜ (pt i) hz₀ (δ i)) ∧
        IsSupportedAtInfinity ((S : Set ℂ))ᶜ hz₀ loopInf ∧
        Function.Surjective φ ∧ (∀ i : Fin S.card, φ (δ i) = h i) ∧ φ loopInf = 1 ∧
        ∀ i : Fin S.card, ∃ (ρ : ℝ) (hsub : puncturedDisc (pt i) ρ ⊆ ((S : Set ℂ))ᶜ)
          (b : ↥(puncturedDisc (pt i) ρ))
          (ε : Path (discIncl hsub b) (⟨z₀, hz₀⟩ : ↥((S : Set ℂ))ᶜ)),
          0 < ρ ∧ (φ.comp (localHom hsub b ε)).range = Subgroup.zpowers (h i) := by
  obtain ⟨δ, loopInf, φ, hloop, hinf, hsurj, hval, hlast⟩ :=
    exists_hom_punctureLoops_ordered S hz₀ pt hrange h hprod hgen
  refine ⟨δ, loopInf, φ, hloop, hinf, hsurj, hval, hlast, fun i => ?_⟩
  obtain ⟨ρ, hsub, b, ε, hρ, hrangeEq⟩ := (hloop i).exists_range_eq_zpowers φ
  exact ⟨ρ, hsub, b, ε, hρ, by rw [hrangeEq, hval i]⟩

end Rigidity.RET

end
