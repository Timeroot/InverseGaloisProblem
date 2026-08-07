/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.GeomAKLB

/-!
# Covers of the line over `ℚ̄` and their branch cycles

A finite Galois cover of the projective line over the algebraically closed constant field `ℚ̄` is
recorded here by its function field: a finite Galois extension `M / ℚ̄(T)`, carried together with
the integral model `ℚ̄[X] ⊆ M` through which the places of the line are addressed
(`Descent.GeomAKLB`).  Over each point `t` of the line sits a set of places of `M`, and the inertia
group at such a place measures how the cover ramifies there; an element of the deck group lying in
one of those inertia groups is an *inertia element at `t`*.

A **system of branch cycles** over points `t₀, …, t_{r-1}` is a tuple of deck transformations, one
an inertia element at each point, which generate the deck group and multiply to `1` in order.  This
is the algebraic shadow of a loop system on the punctured sphere: the `i`-th cycle is the monodromy
of a small loop around `tᵢ`, the product-one relation is the fact that the composite loop is
contractible, and generation is connectedness of the cover.

## Main definitions

* `Rigidity.RET.LineCover` — a finite Galois cover of the line, as its function field with the
  integral model.
* `Rigidity.RET.LineCover.deck` — the deck group `Gal(M / ℚ̄(T))`.
* `Rigidity.RET.LineCover.IsInertiaAt` — a deck transformation is an inertia element at a point.
* `Rigidity.RET.LineCover.IsBranchCycleSystem` — a tuple of inertia elements, one over each of the
  given points, generating the deck group and with product `1`.

## Main results

* `Rigidity.RET.LineCover.isInertiaAt_one` — the identity is an inertia element at every point.
-/

open Polynomial

namespace Rigidity.RET

open GeomAKLB

/-- A **finite Galois cover of the line** over the algebraically closed constant field `ℚ̄`, given
by its function field: a finite Galois extension `M / ℚ̄(T)`, together with the integral model
`ℚ̄[X] ⊆ M` through which the places of the line above a point are addressed. -/
structure LineCover where
  /-- the function field of the cover. -/
  M : Type
  [field : Field M]
  [alg : Algebra (RatFunc k) M]
  [algPoly : Algebra (Polynomial k) M]
  [tower : IsScalarTower (Polynomial k) (RatFunc k) M]
  [findim : FiniteDimensional (RatFunc k) M]
  [isGalois : IsGalois (RatFunc k) M]

namespace LineCover

attribute [instance] LineCover.field LineCover.alg LineCover.algPoly LineCover.tower
  LineCover.findim LineCover.isGalois

/-- The **deck group** `Gal(M / ℚ̄(T))` of a cover of the line. -/
abbrev deck (L : LineCover) : Type := L.M ≃ₐ[RatFunc k] L.M

/-- Package a finite Galois extension of `ℚ̄(T)` as a cover of the line, taking for the integral
model the composite `ℚ̄[X] → ℚ̄(T) → M`.  The packaging is transparent, so that the field structure
of a cover built this way is the field structure it was built from, and instances stated for the
one are found for the other. -/
@[reducible] noncomputable def of (M : Type) [Field M] [Algebra (RatFunc k) M] [FiniteDimensional (RatFunc k) M]
    [IsGalois (RatFunc k) M] : LineCover :=
  letI : Algebra (Polynomial k) M :=
    ((algebraMap (RatFunc k) M).comp (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  haveI : IsScalarTower (Polynomial k) (RatFunc k) M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  { M := M }

@[simp] theorem of_M (M : Type) [Field M] [Algebra (RatFunc k) M] [FiniteDimensional (RatFunc k) M]
    [IsGalois (RatFunc k) M] : (LineCover.of M).M = M := rfl

/-- A deck transformation is an **inertia element at the point `t`** if it lies in the inertia group
of some place of the cover above the place `X - t` of the line. -/
def IsInertiaAt (L : LineCover) (t : k) (σ : L.deck) : Prop :=
  ∃ Q : Ideal (Bring L.M), Q.IsMaximal ∧ Q.LiesOver (placeP t) ∧ σ ∈ geomInertia L.M Q

/-- The identity is an inertia element at every point: the inertia groups are subgroups, and there
is always a place above a point of the line. -/
theorem isInertiaAt_one (L : LineCover) (t : k) : L.IsInertiaAt t 1 := by
  obtain ⟨Q, hQmax, hQover⟩ := exists_Q_over_placeP L.M t
  exact ⟨Q, hQmax, hQover, one_mem _⟩

/-- A tuple `g` of deck transformations is a **system of branch cycles** for the cover over the
points `t` if each `gᵢ` is an inertia element at `tᵢ`, the tuple generates the deck group, and the
ordered product of the tuple is `1`. -/
structure IsBranchCycleSystem (L : LineCover) {r : ℕ} (t : Fin r → k) (g : Fin r → L.deck) :
    Prop where
  /-- the `i`-th branch cycle is an inertia element at the `i`-th point. -/
  inertia : ∀ i, L.IsInertiaAt (t i) (g i)
  /-- the branch cycles generate the deck group: the cover is connected. -/
  top : Subgroup.closure (Set.range g) = ⊤
  /-- the branch cycles multiply to `1`: the composite of the loops is contractible. -/
  prod : (List.ofFn g).prod = 1

end LineCover

end Rigidity.RET
