import Mathlib

/-!
# General criteria for simplicity

This file collects a few *general, reusable* criteria for a group to be simple, packaged so
that the per-group simplicity proofs of the Mathieu groups can reduce to a single, concrete
obligation.

* `isSimpleGroup_of_normalClosure_eq_top`: a nontrivial group all of whose nonidentity
  elements have full normal closure is simple.
* `isSimpleGroup_of_card_normal`: a nontrivial finite group all of whose normal subgroups have
  order `1` or `|G|` is simple.

Both are immediate, but isolating them makes the later proofs cleaner and avoids re-deriving
the same boilerplate in each `M…Simple.lean`.
-/

namespace Mathieu

open Subgroup

/-- **Normal-closure simplicity criterion.**  A nontrivial group in which the normal closure
of every nonidentity element is the whole group is simple. -/
theorem isSimpleGroup_of_normalClosure_eq_top {G : Type*} [Group G] [Nontrivial G]
    (h : ∀ g : G, g ≠ 1 → Subgroup.normalClosure {g} = ⊤) : IsSimpleGroup G := by
  constructor
  intro H hH
  rw [or_iff_not_imp_left]
  intro hbot
  obtain ⟨⟨g, hg⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hg1 : g ≠ 1 := by simpa using hne
  have hle : Subgroup.normalClosure {g} ≤ H := by
    apply Subgroup.normalClosure_le_normal
    simpa using hg
  rw [h g hg1] at hle
  exact top_le_iff.mp hle

/-- **Order simplicity criterion.**  A nontrivial finite group in which every normal subgroup
has order `1` or `Nat.card G` is simple. -/
theorem isSimpleGroup_of_card_normal {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (h : ∀ N : Subgroup G, N.Normal → Nat.card N = 1 ∨ Nat.card N = Nat.card G) :
    IsSimpleGroup G := by
  constructor
  intro H hH
  rcases h H hH with h1 | h2
  · left
    exact Subgroup.eq_bot_of_card_eq H h1
  · right
    rw [← Subgroup.card_eq_iff_eq_top]
    exact h2

end Mathieu
