/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.ExistenceAbelian

/-!
# Monodromy tuples push forward along surjections

A cover realizing a branch-cycle tuple in a group has, inside it, a cover realizing the image of
that tuple in any quotient of the group: take the subcover cut out by the kernel.  The deck group of
the subcover is the quotient (`descentEquiv`), the distinguished inertia generators restrict to
distinguished inertia generators (`LineCover.IsInertiaGenAt.restrict`), and both unramifiedness
clauses are inherited.

So over a fixed set of branch points the realizable branch-cycle tuples are closed under images:
the collection of pairs (group, tuple) that occur is a *quotient-closed* class, and in particular an
isomorphism of groups carries realizations to realizations.

## Main results

* `Rigidity.RET.IsMonodromyOver.map` — a monodromy tuple pushes forward along a surjection of
  groups.
* `Rigidity.RET.IsMonodromyOver.congr` — a monodromy tuple transports along an isomorphism of
  groups.
* `Rigidity.RET.IsMonodromyOver.conj` — a monodromy tuple may be conjugated.
-/

open Polynomial IntermediateField

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-! ## Pushing a monodromy tuple forward -/

/-- **A monodromy tuple pushes forward along a surjection of groups.**  The cover realizing the
image tuple is the subcover cut out by the kernel of the surjection, read through the deck group. -/
theorem IsMonodromyOver.map {G H : Type} [Group G] [Finite G] [Group H] [Finite H] {r : ℕ}
    {h : Fin r → G} {t : Fin r → k} (H₀ : IsMonodromyOver h t) (π : G →* H)
    (hπ : Function.Surjective π) : IsMonodromyOver (fun i => π (h i)) t := by
  obtain ⟨L, e, hout, hinf, hin⟩ := H₀
  let f : L.deck →* H := π.comp e.toMonoidHom
  have hfsurj : Function.Surjective f := hπ.comp e.surjective
  have hkey : ∀ i, (descentEquiv f hfsurj).symm (π (h i))
      = L.subHom (fixedField f.ker) (e.symm (h i)) := by
    intro i
    rw [MulEquiv.symm_apply_eq, descentEquiv_apply]
    show π (h i) = π (e (e.symm (h i)))
    rw [e.apply_symm_apply]
  refine ⟨L.sub (fixedField f.ker), descentEquiv f hfsurj, hout.sub _, hinf.sub _, fun i => ?_⟩
  rw [hkey i]
  exact LineCover.IsInertiaGenAt.restrict L (hin i)

/-- **A monodromy tuple transports along an isomorphism of groups.** -/
theorem IsMonodromyOver.congr {G H : Type} [Group G] [Finite G] [Group H] [Finite H] {r : ℕ}
    {h : Fin r → G} {t : Fin r → k} (H₀ : IsMonodromyOver h t) (φ : G ≃* H) :
    IsMonodromyOver (fun i => φ (h i)) t :=
  H₀.map φ.toMonoidHom φ.surjective

/-- **A monodromy tuple may be conjugated.**  Conjugation is an automorphism of the group, and the
correspondence sees a tuple only up to isomorphism. -/
theorem IsMonodromyOver.conj {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    {t : Fin r → k} (H₀ : IsMonodromyOver h t) (g : G) :
    IsMonodromyOver (fun i => g * h i * g⁻¹) t :=
  H₀.congr (MulAut.conj g)

end Rigidity.RET
