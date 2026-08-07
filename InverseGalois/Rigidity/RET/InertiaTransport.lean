/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Transporting inertia along a map of rings-with-action

The inertia subgroup of an ideal `Q` of a ring `B'` carrying an action of `G'` is the subgroup of
elements acting trivially modulo `Q`.  This file records the one functoriality property of that
notion which the branch-cycle arguments use over and over.

Suppose a ring map `f : B →+* B'` intertwines an action of `G` on `B` with an action of `G'` on
`B'`, along a group homomorphism `ρ : G' →* G` — the situation of a subring, a subfield, or a
change of base ring, where `ρ` is "restrict the automorphism".  Then inertia at an ideal `Q` of
`B'` restricts to inertia at the contracted ideal `Q ∩ B`: if `σ` acts trivially modulo `Q`, then
`ρ σ` acts trivially modulo the contraction, because `f (ρ σ • x - x) = σ • f x - f x ∈ Q`.

## Main results

* `Rigidity.RET.mem_inertia_comap` — inertia restricts to inertia at the contracted ideal.
* `Rigidity.RET.inertia_comap_le` — the same statement as an inequality of subgroups.
-/

namespace Rigidity.RET

variable {B B' : Type*} [CommRing B] [CommRing B'] {G G' : Type*} [Group G] [Group G']
  [MulSemiringAction G B] [MulSemiringAction G' B']

/-- **Inertia restricts to inertia at the contracted ideal.**

If the ring map `f` intertwines the action of `G'` on `B'` with the action of `G` on `B` along
`ρ : G' →* G`, an element acting trivially modulo `Q` acts trivially modulo `Q ∩ B`. -/
theorem mem_inertia_comap (f : B →+* B') (ρ : G' →* G)
    (hρ : ∀ (σ : G') (x : B), f (ρ σ • x) = σ • f x) (Q : Ideal B') {σ : G'}
    (hσ : σ ∈ Q.inertia G') : ρ σ ∈ (Q.comap f).inertia G := by
  intro x
  have hx : σ • f x - f x ∈ Q := hσ (f x)
  have : f (ρ σ • x - x) = σ • f x - f x := by rw [map_sub, hρ σ x]
  show ρ σ • x - x ∈ Q.comap f
  rw [Ideal.mem_comap, this]
  exact hx

/-- The subgroup form of `mem_inertia_comap`: the inertia group upstairs maps into the inertia
group of the contracted ideal. -/
theorem inertia_comap_le (f : B →+* B') (ρ : G' →* G)
    (hρ : ∀ (σ : G') (x : B), f (ρ σ • x) = σ • f x) (Q : Ideal B') :
    (Q.inertia G').map ρ ≤ (Q.comap f).inertia G := by
  rw [Subgroup.map_le_iff_le_comap]
  intro σ hσ
  exact mem_inertia_comap f ρ hρ Q hσ

end Rigidity.RET
