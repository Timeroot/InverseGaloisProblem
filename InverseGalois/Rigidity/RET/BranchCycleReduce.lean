/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.Braid
import InverseGalois.Rigidity.RET.InertiaLift
import InverseGalois.Rigidity.RET.Unramified

/-!
# Cutting a system of branch cycles down to a prescribed tuple of points

A system of distinguished branch cycles is attached to an *ordered tuple* of points of the line,
while a construction of such a system produces it over whatever finite set of points the cover
happens to single out: a set which contains the branch points, may contain others, and comes in an
order dictated by the construction rather than by the tuple one is interested in.  Both
discrepancies are removed here.

Reordering is the Hurwitz action: the braid moves realize every permutation of the cycles at the
cost of replacing each by a conjugate, and a conjugate of a distinguished inertia element at a
point is again one, because the deck group permutes the places above the point transitively.
Discarding a point is possible because a distinguished inertia element at a point which is not a
branch point is trivial, and a trivial entry changes neither the ordered product of the cycles nor
the subgroup they generate.

## Main results

* `Rigidity.RET.LineCover.IsBranchCycleGenSystem.exists_comp_perm` — the points of a system of
  branch cycles may be permuted arbitrarily.
* `Rigidity.RET.LineCover.IsBranchCycleGenSystem.castSucc` — a final trivial cycle may be dropped.
* `Rigidity.RET.LineCover.exists_isBranchCycleGenSystem_of_subset` — a system of branch cycles over
  an injective tuple of points cuts down to a system over any injective sub-tuple containing the
  branch points.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open GeomAKLB

namespace LineCover

variable {L : LineCover}

/-! ### Permuting the points -/

/-- **The points of a system of branch cycles may be permuted arbitrarily.**  The Hurwitz braid
moves realize every permutation of the cycles up to conjugacy, and conjugating a cycle leaves it a
distinguished inertia element at its point. -/
theorem IsBranchCycleGenSystem.exists_comp_perm {r : ℕ} {t : Fin r → k} {g : Fin r → L.deck}
    (h : L.IsBranchCycleGenSystem t g) (σ : Equiv.Perm (Fin r)) :
    ∃ g' : Fin r → L.deck, L.IsBranchCycleGenSystem (t ∘ σ) g' := by
  obtain ⟨g', hbc, hcl⟩ := Rigidity.exists_braidConj_perm σ g
  have hmem : g ∈ Rigidity.nielsenTuples fun i => ConjClasses.mk (g i) :=
    ⟨⟨1, fun _ => rfl⟩, h.prod, h.top⟩
  obtain ⟨-, hprod, htop⟩ := hbc.mem_nielsenTuples hmem
  refine ⟨g', fun i => ?_, htop, hprod⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (hcl i))
  have hconj := (h.inertia (σ i)).conj c⁻¹
  rw [← hc] at hconj
  have heq : c⁻¹ * (c * g' i * c⁻¹) * c⁻¹⁻¹ = g' i := by group
  rwa [heq] at hconj

/-! ### Dropping a trivial cycle -/

/-- A distinguished inertia element at a point which is not a branch point is trivial. -/
theorem IsInertiaGenAt.eq_one_of_unramified {S : Set k} {u : k} {σ : L.deck}
    (h : L.IsInertiaGenAt u σ) (hunr : L.IsUnramifiedOutside S) (hu : u ∉ S) : σ = 1 :=
  hunr u hu σ h.isInertiaAt

/-- **A system of branch cycles whose last cycle is trivial is a system over the remaining
points.** -/
theorem IsBranchCycleGenSystem.castSucc {m : ℕ} {v : Fin (m + 1) → k} {g : Fin (m + 1) → L.deck}
    (h : L.IsBranchCycleGenSystem v g) (hlast : g (Fin.last m) = 1) :
    L.IsBranchCycleGenSystem (v ∘ Fin.castSucc) (g ∘ Fin.castSucc) where
  inertia i := h.inertia i.castSucc
  top := by
    refine eq_top_iff.2 ?_
    rw [← h.top]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => rw [hlast]; exact one_mem _
    | cast j => exact Subgroup.subset_closure ⟨j, rfl⟩
  prod := by
    have hp := h.prod
    rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton, hlast,
      mul_one] at hp
    exact hp

/-! ### Cutting down to the branch points -/

/-- The inductive form of `Rigidity.RET.LineCover.exists_isBranchCycleGenSystem_of_subset`: the
induction is on the length of the ambient tuple, one extraneous point being moved to the end and
dropped at each step. -/
theorem exists_isBranchCycleGenSystem_aux (L : LineCover) :
    ∀ (m : ℕ) (v : Fin m → k), Function.Injective v →
      (∃ g : Fin m → L.deck, L.IsBranchCycleGenSystem v g) →
        ∀ (r : ℕ) (t : Fin r → k), Function.Injective t → Set.range t ⊆ Set.range v →
          L.IsUnramifiedOutside (Set.range t) →
            ∃ g : Fin r → L.deck, L.IsBranchCycleGenSystem t g := by
  intro m
  induction m with
  | zero =>
      intro v _ hsys r t _ hsub _
      have hr : r = 0 := by
        by_contra hr
        have hpos : 0 < r := Nat.pos_of_ne_zero hr
        have hmem : t ⟨0, hpos⟩ ∈ Set.range v := hsub ⟨_, rfl⟩
        rw [Set.range_eq_empty v] at hmem
        simp at hmem
      subst hr
      obtain ⟨g, hg⟩ := hsys
      exact ⟨g, by rwa [show t = v from funext fun i => i.elim0]⟩
  | succ m ih =>
      intro v hv hsys r t ht hsub hunr
      obtain ⟨g, hg⟩ := hsys
      by_cases hall : ∀ j : Fin (m + 1), v j ∈ Set.range t
      · -- the two tuples have the same range, so the same length, and differ by a permutation
        have hchoice : ∀ i : Fin r, ∃ j : Fin (m + 1), v j = t i := fun i => hsub ⟨i, rfl⟩
        choose φ hφ using hchoice
        have hφinj : Function.Injective φ := fun i i' hii => ht (by rw [← hφ i, ← hφ i', hii])
        have hchoice' : ∀ j : Fin (m + 1), ∃ i : Fin r, t i = v j := fun j => hall j
        choose ψ hψ using hchoice'
        have hψinj : Function.Injective ψ := fun j j' hjj => hv (by rw [← hψ j, ← hψ j', hjj])
        have h1 : r ≤ m + 1 := by simpa using Fintype.card_le_of_injective φ hφinj
        have h2 : m + 1 ≤ r := by simpa using Fintype.card_le_of_injective ψ hψinj
        have hcard : r = m + 1 := le_antisymm h1 h2
        subst hcard
        obtain ⟨g', hg'⟩ :=
          hg.exists_comp_perm (Equiv.ofBijective φ (Finite.injective_iff_bijective.mp hφinj))
        exact ⟨g', by rwa [show v ∘ (Equiv.ofBijective φ (Finite.injective_iff_bijective.mp hφinj))
          = t from funext fun i => hφ i] at hg'⟩
      · -- an extraneous point: move it to the end, drop it, and recurse
        push_neg at hall
        obtain ⟨j, hj⟩ := hall
        obtain ⟨g', hg'⟩ := hg.exists_comp_perm (Equiv.swap j (Fin.last m))
        have hlastpt : (v ∘ (Equiv.swap j (Fin.last m))) (Fin.last m) = v j := by
          simp [Equiv.swap_apply_right]
        have hlast1 : g' (Fin.last m) = 1 :=
          (hg'.inertia (Fin.last m)).eq_one_of_unramified hunr (by rw [hlastpt]; exact hj)
        refine ih ((v ∘ (Equiv.swap j (Fin.last m))) ∘ Fin.castSucc)
          ((hv.comp (Equiv.injective _)).comp (Fin.castSucc_injective m))
          ⟨_, hg'.castSucc hlast1⟩ r t ht ?_ hunr
        rintro x ⟨i, rfl⟩
        obtain ⟨l, hl⟩ := hsub ⟨i, rfl⟩
        have hlj : l ≠ j := by
          rintro rfl
          exact hj ⟨i, hl.symm⟩
        have hσl : Equiv.swap j (Fin.last m) l ≠ Fin.last m := by
          rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
          exact hlj
        obtain ⟨i₀, hi₀⟩ := Fin.exists_castSucc_eq.2 hσl
        refine ⟨i₀, ?_⟩
        simp only [Function.comp_apply]
        rw [hi₀, Equiv.swap_apply_self, hl]

/-- **A system of branch cycles cuts down to any sub-tuple of the points containing the branch
points.**  The points which are dropped are not branch points, so their cycles are trivial, and
the remaining cycles can be brought into the prescribed order by Hurwitz moves. -/
theorem exists_isBranchCycleGenSystem_of_subset (L : LineCover) {m r : ℕ} {v : Fin m → k}
    {t : Fin r → k} (hv : Function.Injective v) (ht : Function.Injective t)
    (hsub : Set.range t ⊆ Set.range v) (hunr : L.IsUnramifiedOutside (Set.range t))
    (h : ∃ g : Fin m → L.deck, L.IsBranchCycleGenSystem v g) :
    ∃ g : Fin r → L.deck, L.IsBranchCycleGenSystem t g :=
  exists_isBranchCycleGenSystem_aux L m v hv h r t ht hsub hunr

end LineCover

end Rigidity.RET

end
