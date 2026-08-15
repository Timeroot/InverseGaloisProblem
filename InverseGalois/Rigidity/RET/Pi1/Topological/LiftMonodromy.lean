/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.Monodromy

/-!
# Reading the monodromy off an explicit lift

The monodromy of a loop is defined through the lift produced by the path-lifting property, which
is of no use when the lift is already known by a formula.  Uniqueness of path lifting repairs
that: any continuous path upstairs lying over the loop *is* the lift, so the monodromy of the loop
at the starting point of that path is simply its endpoint.

The second half of the file records a purely group-theoretic companion.  Two generators of the
same group have images of the same order under any homomorphism, because the image of a generator
generates the image of the whole group.  It is what lets an abstract generator of a fundamental
group be replaced by an explicit one without changing the order of the monodromy it names.

## Main results

* `IsCoveringMap.monodromy_of_lift` — the monodromy of a loop along an explicit lift is the
  endpoint of that lift.
* `orderOf_map_eq_of_zpowers_eq_top` — a homomorphism sends any two generators to elements of the
  same order.
-/

open Topology unitInterval

noncomputable section

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (cov : IsCoveringMap p)

/-- **The monodromy of a loop along an explicit lift is the endpoint of that lift.**  A continuous
path upstairs lying over the loop is *the* lift of the loop starting where it starts, by uniqueness
of path lifting, so the monodromy reads off its endpoint. -/
theorem monodromy_of_lift {x y : X} (q : Path x y) (Γ : C(I, E)) (hΓ : ∀ t, p (Γ t) = q t)
    (e : p ⁻¹' {x}) (he : (e : E) = Γ 0) :
    (cov.monodromy (Path.Homotopic.Quotient.mk q) e : E) = Γ 1 := by
  have hlift : Γ = cov.liftPath q e.val (q.source.trans e.2.symm) :=
    (cov.eq_liftPath_iff' _).mpr ⟨funext hΓ, he.symm⟩
  rw [cov.monodromy_mk_val, ← hlift]

end IsCoveringMap

/-- **A homomorphism sends any two generators to elements of the same order.**  The image of a
generator generates the image of the whole group, so both images generate the same subgroup. -/
theorem orderOf_map_eq_of_zpowers_eq_top {G H : Type*} [Group G] [Group H] (f : G →* H) {a b : G}
    (ha : Subgroup.zpowers a = ⊤) (hb : Subgroup.zpowers b = ⊤) : orderOf (f a) = orderOf (f b) := by
  rw [← Nat.card_zpowers, ← Nat.card_zpowers, ← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers,
    ha, hb]

end
