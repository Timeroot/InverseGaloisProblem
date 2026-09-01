/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Family

/-!
# Sections of a family over a free action are sums of conjugates

When a finite group acts freely on the index set of a family of modules, every section fixed by the
whole group is the sum of the conjugates of a single section.  The section to sum is supported on
one chosen point of each orbit, where it takes the value of the fixed section; summing over the
group then reproduces the fixed section, because for each index exactly one group element carries
the chosen point of its orbit to it, and the fixed section is carried along with it.

Freeness is only ever used at the indices where the fixed section does not vanish, and a fixed
section vanishes on a whole orbit as soon as it vanishes at one of its points; so it suffices that
no nontrivial group element fix an index of the support.

This is the local-to-global step for a place that splits completely: there the decomposition group
is trivial, the group acts freely on the places above, and the requirement of being a local norm
disappears altogether.  In the same way a section concentrated at the places above one such place
is a sum of conjugates, whatever the group does elsewhere.

## Main results

* `InverseGalois.CFT.FamilyAction.exists_sum_familyAut_eq_of_free_on_support`: **a fixed section
  whose support meets no nontrivial stabiliser is the sum of the conjugates of a section supported
  on one point of each orbit.**
* `InverseGalois.CFT.FamilyAction.exists_sum_familyAut_eq`: **a section fixed by a group acting
  freely on the index set is the sum of the conjugates of a section supported on one point of each
  orbit.**

## Tags

group action, family of modules, sections, free action, norm, orbit
-/

namespace InverseGalois.CFT

open MulAction

namespace FamilyAction

variable {X : Type*} {M : X → Type*} [∀ x, AddCommGroup (M x)] {G : Type*} [Group G] [Fintype G]
  [MulAction G X] (F : FamilyAction M G)

/-- **A fixed section whose support meets no nontrivial stabiliser is the sum of the conjugates of
a section supported on one point of each orbit**, and that section takes at each index either the
value of the fixed section or zero.  Over an orbit where the section does not vanish exactly one
group element carries the chosen point to a given index, so exactly one summand survives; over an
orbit where it does vanish every summand vanishes too. -/
theorem exists_sum_familyAut_eq_of_free_on_support {s : ∀ x, M x}
    (hs : ∀ g : G, F.familyAut g s = s)
    (hfree : ∀ (g : G) (x : X), s x ≠ 0 → g • x = x → g = 1) :
    ∃ t : ∀ x, M x, (∀ x, t x = s x ∨ t x = 0) ∧ ∑ g : G, F.familyAut g t = s := by
  classical
  set r : X → X := fun x => (Quotient.mk (orbitRel G X) x).out with hrdef
  have hsmul : ∀ (g : G) (x : X), r (g • x) = r x := by
    intro g x
    rw [hrdef]
    exact congrArg Quotient.out (Quotient.sound (mem_orbit x g))
  have hidem : ∀ x : X, r (r x) = r x := by
    intro x
    rw [hrdef]
    exact congrArg Quotient.out (Quotient.out_eq (Quotient.mk (orbitRel G X) x))
  have hreach : ∀ x : X, ∃ g : G, g • x = r x := by
    intro x
    rw [hrdef]
    exact Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel G X) x))
  obtain ⟨t, ht⟩ : ∃ t : ∀ x, M x, ∀ x, t x = if r x = x then s x else 0 :=
    ⟨fun x => if r x = x then s x else 0, fun _ => rfl⟩
  refine ⟨t, fun x => ?_, funext fun x => ?_⟩
  · rcases eq_or_ne (r x) x with h | h
    · exact Or.inl (by rw [ht, if_pos h])
    · exact Or.inr (by rw [ht, if_neg h])
  · obtain ⟨g₁, hg₁⟩ := hreach x
    have hinv : g₁⁻¹ • r x = x := by rw [← hg₁, inv_smul_smul]
    have hsx : s x = F.transport hinv (s (r x)) := by
      have h := F.familyAut_apply_eq_transport hinv s
      rwa [hs g₁⁻¹] at h
    rcases eq_or_ne (s (r x)) 0 with h0 | h0
    · rw [Finset.sum_apply, hsx, h0, map_zero]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [F.familyAut_apply_eq_transport (smul_inv_smul b x) t, ht]
      rcases eq_or_ne (r (b⁻¹ • x)) (b⁻¹ • x) with hb | hb
      · have hbx : s (b⁻¹ • x) = 0 := by
          rw [show b⁻¹ • x = r x from by rw [← hb, hsmul]]
          exact h0
        rw [if_pos hb, hbx, map_zero]
      · rw [if_neg hb, map_zero]
    · have hzero : ∀ b ∈ (Finset.univ : Finset G), b ≠ g₁⁻¹ → F.familyAut b t x = 0 := by
        intro b _ hb
        have hne : ¬ r (b⁻¹ • x) = b⁻¹ • x := by
          rw [hsmul]
          intro hcon
          refine hb (inv_mul_eq_one.mp (hfree (b⁻¹ * g₁⁻¹) (r x) h0 ?_))
          rw [mul_smul, hinv, ← hcon]
        rw [F.familyAut_apply_eq_transport (smul_inv_smul b x) t, ht, if_neg hne]
        exact map_zero _
      rw [Finset.sum_apply,
        Finset.sum_eq_single g₁⁻¹ hzero fun hb => absurd (Finset.mem_univ g₁⁻¹) hb,
        F.familyAut_apply_eq_transport hinv t, ht, if_pos (hidem x), hsx]

/-- **A section fixed by a group acting freely on the index set is the sum of the conjugates of a
section supported on one point of each orbit**, and that section takes at each index either the
value of the fixed section or zero.  For a given index exactly one group element carries the chosen
point of its orbit to it, so exactly one summand survives, and it is the value of the fixed section
there. -/
theorem exists_sum_familyAut_eq (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) {s : ∀ x, M x}
    (hs : ∀ g : G, F.familyAut g s = s) :
    ∃ t : ∀ x, M x, (∀ x, t x = s x ∨ t x = 0) ∧ ∑ g : G, F.familyAut g t = s :=
  F.exists_sum_familyAut_eq_of_free_on_support hs fun g x _ h => hfree g x h

end FamilyAction

end InverseGalois.CFT
