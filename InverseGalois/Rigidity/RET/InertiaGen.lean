/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.TamePi1

/-!
# Distinguished inertia generators at a point of the line

The inertia group of a cover of the line at a place above a point `t` is cyclic
(`GeomAKLB.isCyclic_geomInertia`); a deck transformation which *generates* it is a **distinguished
inertia element** at `t`.  This is the form in which the branch cycles of a topological loop system
arrive: the monodromy of a small loop around `tᵢ` does not merely lie in the local inertia group, it
generates it.  Recording the generation is what makes the local data rigid enough to be compared
with a prescribed conjugacy class, since two generators of the same cyclic group differ by a power
with exponent coprime to the order, and a rational class is closed under exactly those powers.

The comparison between two distinguished inertia elements at the *same* point rests on two facts
proved here about the geometric places, both of which fail over a non-closed constant field:

* the inertia group at a geometric place is the whole decomposition group
  (`geomInertia_eq_stabilizer`) — the residue field extension is trivial because every residue is a
  constant and the constants are algebraically closed;
* the deck group permutes the places above a point transitively (`exists_smul_eq_of_liesOver`).

Together they give that any two distinguished inertia elements at a point generate conjugate cyclic
subgroups (`LineCover.IsInertiaGenAt.exists_conj`).

## Main definitions

* `Rigidity.RET.LineCover.IsInertiaGenAt` — a deck transformation generates the inertia group of
  some place above the point.
* `Rigidity.RET.LineCover.IsBranchCycleGenSystem` — a system of branch cycles whose entries are
  distinguished inertia elements.

## Main results

* `Rigidity.RET.exists_poly_sub_mem` — every element of the geometric model is congruent to a
  constant at a geometric place.
* `Rigidity.RET.geomInertia_eq_stabilizer` — inertia equals decomposition at a geometric place.
* `Rigidity.RET.exists_smul_eq_of_liesOver` — the deck group is transitive on the places above a
  point.
* `Rigidity.RET.geomInertia_smul` — inertia groups transform by conjugation along the action on
  places.
* `Rigidity.RET.LineCover.IsInertiaGenAt.exists_conj` — two distinguished inertia elements at a
  point generate conjugate cyclic subgroups.
-/

open Polynomial
open scoped Pointwise

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

section Geom

variable {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω]
  [IsGalois (RatFunc k) Ω]
  [Algebra (Polynomial k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω]

/-- The deck group fixes the constants of the integral model: it acts by `ℚ̄[X]`-algebra maps. -/
theorem smul_algebraMap_poly (g : Ω ≃ₐ[RatFunc k] Ω) (f : Polynomial k) :
    g • (algebraMap (Polynomial k) (Bring Ω) f) = algebraMap (Polynomial k) (Bring Ω) f := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

omit [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- **Every element of the geometric model is congruent to a constant at a geometric place.**

The residue field at a place above `X - t` is integral over the residue field `ℚ̄` of the point, and
`ℚ̄` is algebraically closed, so the residue extension is trivial. -/
theorem exists_poly_sub_mem (t : k) (Q : Ideal (Bring Ω)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] (x : Bring Ω) :
    ∃ f : Polynomial k, x - algebraMap (Polynomial k) (Bring Ω) f ∈ Q := by
  haveI : Algebra.IsIntegral (Polynomial k ⧸ placeP t) (Bring Ω ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := Polynomial k)
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := Polynomial k ⧸ placeP t) (K := Bring Ω ⧸ Q)).2 (Ideal.Quotient.mk Q x)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨f, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc]
  rfl

/-- **Inertia is the whole decomposition group at a geometric place.**

An element stabilizing the place acts trivially on the residue field, because every residue is a
constant and the constants are fixed; so it lies in the inertia group. -/
theorem geomInertia_eq_stabilizer (t : k) (Q : Ideal (Bring Ω)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] :
    geomInertia Ω Q = MulAction.stabilizer (Ω ≃ₐ[RatFunc k] Ω) Q := by
  refine le_antisymm (Ideal.inertia_le_stabilizer Q) fun σ hσ => ?_
  have hQ : σ • Q = Q := hσ
  refine AddSubgroup.mem_inertia.mpr fun x => ?_
  obtain ⟨f, hf⟩ := exists_poly_sub_mem t Q x
  have h1 : σ • x - x
      = σ • (x - algebraMap (Polynomial k) (Bring Ω) f)
        - (x - algebraMap (Polynomial k) (Bring Ω) f) := by
    rw [smul_sub, smul_algebraMap_poly]
    abel
  rw [Submodule.mem_toAddSubgroup, h1]
  refine Q.sub_mem ?_ hf
  rw [← hQ]
  exact Ideal.smul_mem_pointwise_smul _ _ _ hf

/-- **The deck group is transitive on the places above a point of the line.** -/
theorem exists_smul_eq_of_liesOver (t : k) (Q Q' : Ideal (Bring Ω)) [Q.IsPrime] [Q'.IsPrime]
    [hQ : Q.LiesOver (placeP t)] [hQ' : Q'.LiesOver (placeP t)] :
    ∃ g : Ω ≃ₐ[RatFunc k] Ω, Q' = g • Q := by
  haveI : Algebra.IsInvariant (Polynomial k) (Bring Ω) (Ω ≃ₐ[RatFunc k] Ω) :=
    Algebra.isInvariant_of_isGalois (Polynomial k) (RatFunc k) Ω (Bring Ω)
  exact Algebra.IsInvariant.exists_smul_of_under_eq (Polynomial k) (Bring Ω)
    (Ω ≃ₐ[RatFunc k] Ω) Q Q' (hQ.over.symm.trans hQ'.over)

omit [FiniteDimensional (RatFunc k) Ω] in
/-- Inertia groups transform by conjugation along the action of the deck group on places. -/
theorem geomInertia_smul (g : Ω ≃ₐ[RatFunc k] Ω) (Q : Ideal (Bring Ω)) :
    geomInertia Ω (g • Q) = (geomInertia Ω Q).map (MulAut.conj g).toMonoidHom := by
  ext σ
  rw [geom_mem_inertia_smul_iff]
  constructor
  · intro h
    refine ⟨g⁻¹ * σ * g, h, ?_⟩
    show g * (g⁻¹ * σ * g) * g⁻¹ = σ
    group
  · rintro ⟨x, hx, rfl⟩
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom x) * g = x := by
      show g⁻¹ * (g * x * g⁻¹) * g = x
      group
    rwa [this]

omit [FiniteDimensional (RatFunc k) Ω] in
/-- A generator of the inertia group at `Q` conjugates to a generator of the inertia group at
`g • Q`. -/
theorem geomInertia_eq_zpowers_smul {σ : Ω ≃ₐ[RatFunc k] Ω} (g : Ω ≃ₐ[RatFunc k] Ω)
    (Q : Ideal (Bring Ω)) (h : geomInertia Ω Q = Subgroup.zpowers σ) :
    geomInertia Ω (g • Q) = Subgroup.zpowers (g * σ * g⁻¹) := by
  rw [geomInertia_smul, h, MonoidHom.map_zpowers]
  rfl

end Geom

namespace LineCover

/-- A deck transformation is a **distinguished inertia element at the point `t`** if it *generates*
the inertia group of some place of the cover above the place `X - t` of the line. -/
def IsInertiaGenAt (L : LineCover) (t : k) (σ : L.deck) : Prop :=
  ∃ Q : Ideal (Bring L.M), Q.IsMaximal ∧ Q.LiesOver (placeP t) ∧
    geomInertia L.M Q = Subgroup.zpowers σ

variable {L : LineCover} {t : k} {σ τ : L.deck}

/-- A distinguished inertia element is in particular an inertia element. -/
theorem IsInertiaGenAt.isInertiaAt (h : L.IsInertiaGenAt t σ) : L.IsInertiaAt t σ := by
  obtain ⟨Q, hmax, hover, hI⟩ := h
  exact ⟨Q, hmax, hover, hI ▸ Subgroup.mem_zpowers σ⟩

/-- **Two distinguished inertia elements at the same point generate conjugate cyclic subgroups.**

The deck group is transitive on the places above the point, and conjugating by an element carrying
one place to the other carries one inertia group onto the other. -/
theorem IsInertiaGenAt.exists_conj (hσ : L.IsInertiaGenAt t σ) (hτ : L.IsInertiaGenAt t τ) :
    ∃ c : L.deck, Subgroup.zpowers τ = Subgroup.zpowers (c * σ * c⁻¹) := by
  obtain ⟨Q, hmax, hover, hI⟩ := hσ
  obtain ⟨Q', hmax', hover', hI'⟩ := hτ
  haveI := hmax.isPrime
  haveI := hmax'.isPrime
  haveI := hover
  haveI := hover'
  obtain ⟨c, hc⟩ := exists_smul_eq_of_liesOver t Q Q'
  exact ⟨c, by rw [← hI', hc, geomInertia_eq_zpowers_smul c Q hI]⟩

/-- A tuple `g` of deck transformations is a **system of distinguished branch cycles** for the cover
over the points `t` if each `gᵢ` generates an inertia group at `tᵢ`, the tuple generates the deck
group, and the ordered product of the tuple is `1`. -/
structure IsBranchCycleGenSystem (L : LineCover) {r : ℕ} (t : Fin r → k) (g : Fin r → L.deck) :
    Prop where
  /-- the `i`-th branch cycle generates an inertia group at the `i`-th point. -/
  inertia : ∀ i, L.IsInertiaGenAt (t i) (g i)
  /-- the branch cycles generate the deck group: the cover is connected. -/
  top : Subgroup.closure (Set.range g) = ⊤
  /-- the branch cycles multiply to `1`: the composite of the loops is contractible. -/
  prod : (List.ofFn g).prod = 1

/-- A system of distinguished branch cycles is a system of branch cycles. -/
theorem IsBranchCycleGenSystem.toIsBranchCycleSystem {r : ℕ} {t : Fin r → k} {g : Fin r → L.deck}
    (h : L.IsBranchCycleGenSystem t g) : L.IsBranchCycleSystem t g where
  inertia i := (h.inertia i).isInertiaAt
  top := h.top
  prod := h.prod

end LineCover

end Rigidity.RET
