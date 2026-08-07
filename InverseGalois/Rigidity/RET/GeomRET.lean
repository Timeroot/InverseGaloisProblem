/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.InertiaGen
import InverseGalois.Rigidity.RET.Twist

/-!
# The Riemann Existence Theorem for the line, at the branch-cycle interface

Fix `r` distinct points `t₀, …, t_{r-1}` of the line over `ℚ̄`.  Covers of the line unramified
outside those points and infinity are, classically, the same thing as finite quotients of the
fundamental group of the `r`-punctured sphere, which is the sphere group
`Γ_r = ⟨x₀,…,x_{r-1} | x₀⋯x_{r-1} = 1⟩`: the cover is reconstructed analytically from its monodromy
(Riemann Existence / Grauert–Remmert), and conversely the monodromy of a cover is read off from
loops around the punctures.  `GeomRET t` is that correspondence, written out in the two directions
that the rigidity method consumes, and written in terms of the data the rest of the development
uses — an algebraic cover `L` of the line, inertia at the places of its integral model over the
`tᵢ`, and unramifiedness elsewhere.

Both directions are needed, and neither follows from the other by algebra:

* **existence** builds a cover out of a generating product-one tuple.  This is the direction the
  realization of a group as a Galois group over `ℚ̄(T)` rests on;
* **completeness** reads branch cycles off an arbitrary cover with the prescribed branch locus.
  This is the direction the *descent* rests on: the Galois closure over `ℚ(T)` of a cover built by
  the first direction is a bigger cover, with the same branch locus, whose branch cycles must be
  produced before the arithmetic of the descent can begin.

The topological half of the correspondence is not assumed: `π₁` of the punctured plane is free on
the loops around the punctures and the sphere relation is the product of those loops
(`Rigidity.RET.pi1_compl_mulEquiv_sphereGroup`, `RET/Pi1/Topological/PuncturedPlane.lean`).  What is
assumed here is the comparison between that topological picture and the algebra of the function
field: the analytic passage from a topological cover to an algebraic one (Grauert–Remmert / GAGA)
and the passage between `ℂ` and `ℚ̄` (Lefschetz).

## Main definitions

* `Rigidity.RET.GeomRET` — the two directions of the correspondence over a fixed branch locus.

## Main results

* `Rigidity.RET.geomRET` — the correspondence holds for any injective tuple of points.
* `Rigidity.RET.lineCover_exists_of_branchCycles` — the existence direction, packaged as a system
  of branch cycles.
* `Rigidity.RET.exists_branchCycleSystem` — the completeness direction.
* `Rigidity.RET.exists_branchCycleGenSystem` — the completeness direction with the branch cycles
  generating the local inertia groups.
-/

open Polynomial

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

namespace Rigidity.RET

open GeomAKLB

/-- **Covers of the line with branch locus in `{t₀,…,t_{r-1}}` are the finite quotients of the
sphere group**, in the two directions in which the correspondence is used.

* `exists_cover`: a tuple `h` in a finite group `H` which generates `H` and has product `1` — the
  same thing as a surjection `Γ_r ↠ H` — is the monodromy of a cover of the line with deck group
  `H`, unramified outside the `tᵢ` and infinity, in which `hᵢ` generates an inertia group at `tᵢ`.
* `exists_cycles`: conversely, a cover of the line unramified outside the `tᵢ` and infinity carries
  a system of branch cycles over those points: inertia generators, one at each `tᵢ`, generating the
  deck group, with product `1` in the given order.

The inertia clauses are the *distinguished* ones (`LineCover.IsInertiaGenAt`): the monodromy of a
small loop around a puncture does not merely lie in the local inertia group, it generates it.  That
is what makes the local data comparable with a prescribed conjugacy class, since two generators of
the same cyclic group differ by a power with exponent coprime to the order. -/
structure GeomRET {r : ℕ} (t : Fin r → k) : Prop where
  /-- a generating product-one tuple in a finite group is the monodromy of a cover branched over
  the given points. -/
  exists_cover : ∀ {H : Type} [Group H] [Finite H] (h : Fin r → H),
      (List.ofFn h).prod = 1 → Subgroup.closure (Set.range h) = ⊤ →
      ∃ (L : LineCover) (e : L.deck ≃* H),
        L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
        ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i))
  /-- a cover branched only over the given points and infinity has a system of branch cycles over
  those points. -/
  exists_cycles : ∀ L : LineCover, L.IsUnramifiedOutside (Set.range t) →
      L.IsUnramifiedAtInfinity → ∃ g : Fin r → L.deck, L.IsBranchCycleGenSystem t g

/-- **The Riemann Existence Theorem for the line over `ℚ̄`.**

For `r` distinct points of the line, covers of the line unramified outside those points and
infinity correspond to finite quotients of the fundamental group of the `r`-punctured sphere, the
sphere group `Γ_r = ⟨x₀,…,x_{r-1} | x₀⋯x_{r-1} = 1⟩`: a generating product-one tuple in a finite
group `H` is the tuple of branch cycles of a cover with deck group `H`, and every cover with that
branch locus has such a tuple of branch cycles.

The two hypotheses on the tuple are not decoration: they are exactly the two relations that hold
among the loops on the punctured sphere — the loops generate, because the cover is connected, and
their ordered product is contractible.  A tuple violating either is the branch-cycle system of no
cover.

Over `ℂ` this is covering-space theory plus the theorem of Grauert–Remmert that a finite
topological cover of a punctured Riemann surface, tame at the punctures, is the analytification of
an algebraic one; the constant field `ℚ̄` is reached from `ℂ` by the Lefschetz principle.  See
Grothendieck, *SGA 1*, Exp. XIII; Völklein, *Groups as Galois Groups*, Thm 2.13 and §4; Serre,
*Topics in Galois Theory*, §6. -/
theorem geomRET {r : ℕ} (t : Fin r → k) (ht : Function.Injective t) : GeomRET t :=
  sorry

/-- **Prescribed branch cycles are realized by a cover of the line.**

Given `r` distinct points `t₀, …, t_{r-1}` of the line over `ℚ̄` and a tuple `h₀, …, h_{r-1}` of
elements of a finite group `H` which generate `H` and multiply to `1`, there is a finite Galois
cover of the line with deck group `H`, unramified outside the given points and infinity, in which
`hᵢ` is an inertia element at `tᵢ`. -/
theorem lineCover_exists_of_branchCycles {r : ℕ} (t : Fin r → k) (ht : Function.Injective t)
    {H : Type} [Group H] [Finite H] (h : Fin r → H)
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : LineCover) (e : L.deck ≃* H), ∀ i, L.IsInertiaAt (t i) (e.symm (h i)) := by
  obtain ⟨L, e, -, -, hin⟩ := (geomRET t ht).exists_cover h hprod htop
  exact ⟨L, e, fun i => (hin i).isInertiaAt⟩

/-- **A cover branched only over the given points has branch cycles there.** -/
theorem exists_branchCycleSystem {r : ℕ} (t : Fin r → k) (ht : Function.Injective t)
    (L : LineCover) (hS : L.IsUnramifiedOutside (Set.range t)) (hinf : L.IsUnramifiedAtInfinity) :
    ∃ g : Fin r → L.deck, L.IsBranchCycleSystem t g :=
  ((geomRET t ht).exists_cycles L hS hinf).imp fun _ h => h.toIsBranchCycleSystem

/-- **A cover branched only over the given points has distinguished branch cycles there**: the
branch cycles can be taken to *generate* the local inertia groups, not merely to lie in them. -/
theorem exists_branchCycleGenSystem {r : ℕ} (t : Fin r → k) (ht : Function.Injective t)
    (L : LineCover) (hS : L.IsUnramifiedOutside (Set.range t)) (hinf : L.IsUnramifiedAtInfinity) :
    ∃ g : Fin r → L.deck, L.IsBranchCycleGenSystem t g :=
  (geomRET t ht).exists_cycles L hS hinf

/-! ## Two transport lemmas for tuples along a group isomorphism -/

section Transport

variable {G H : Type*} [Group G] [Group H] (e : G ≃* H) {r : ℕ} {h : Fin r → H}

/-- A generating tuple stays generating under an isomorphism. -/
theorem closure_range_symm_eq_top (htop : Subgroup.closure (Set.range h) = ⊤) :
    Subgroup.closure (Set.range fun i => e.symm (h i)) = ⊤ := by
  have hrange : (Set.range fun i => e.symm (h i)) = (e.symm : H →* G) '' Set.range h :=
    Set.range_comp _ _
  rw [hrange, show Subgroup.closure ((e.symm : H →* G) '' Set.range h)
      = (Subgroup.closure (Set.range h)).map (e.symm : H →* G) from
    (MonoidHom.map_closure _ _).symm, htop, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact e.symm.surjective

/-- A product-one tuple stays product-one under an isomorphism. -/
theorem prod_ofFn_symm_eq_one (hprod : (List.ofFn h).prod = 1) :
    (List.ofFn fun i => e.symm (h i)).prod = 1 := by
  rw [show List.ofFn (fun i => e.symm (h i)) = (List.ofFn h).map (e.symm : H →* G) by
    rw [List.map_ofFn]; rfl]
  rw [← map_list_prod, hprod, map_one]

end Transport

/-- The cover produced by the existence direction carries the prescribed tuple as a genuine system
of distinguished branch cycles: the tuple generates the deck group and has product one, and those
two properties travel along the identification of the deck group with `H`. -/
theorem exists_lineCover_isBranchCycleSystem {r : ℕ} (t : Fin r → k) (ht : Function.Injective t)
    {H : Type} [Group H] [Finite H] (h : Fin r → H)
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : LineCover) (e : L.deck ≃* H), L.IsBranchCycleGenSystem t (fun i => e.symm (h i)) := by
  obtain ⟨L, e, -, -, hin⟩ := (geomRET t ht).exists_cover h hprod htop
  exact ⟨L, e, ⟨hin, closure_range_symm_eq_top e htop, prod_ofFn_symm_eq_one e hprod⟩⟩

end Rigidity.RET
