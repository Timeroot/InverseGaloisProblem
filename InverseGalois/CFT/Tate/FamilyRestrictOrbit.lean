/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyOrbits
import InverseGalois.CFT.Tate.FamilyRestrict

/-!
# A restricted family of modules over a single orbit

The ideles of a number field that are units outside a finite set of places are the sections of a
family of subgroups of the family of local factors: the whole multiplicative group at the places in
the set and the units of the valuation ring at the others.  The contribution of one orbit of the
Galois group to the Herbrand quotient of that group of sections is computed exactly as for the
ambient family, through the action of the stabiliser of a point of the orbit on the subgroup there.

That action is the restriction of the action on the ambient module, which is the only thing this
file proves; everything else follows by comparing Herbrand quotients along the identification of the
subgroup at the base point with whatever group it is declared to be.  Two cases are singled out:
when the subgroup is everything the contribution of the orbit is unchanged, and when the action on
the subgroup is a known one whose Tate groups vanish the orbit contributes nothing at all.

## Main results

* `InverseGalois.CFT.coe_stabAut_orbitFamily_restrict`: **the action of the stabiliser of a point of
  an orbit on a restricted family is the restriction of its action on the ambient family.**
* `InverseGalois.CFT.herbrand_orbitFamily_restrict_top`: an orbit on which the family of subgroups
  is everything contributes what it contributes to the ambient family.
* `InverseGalois.CFT.subsingleton_tateH0_orbitFamily_restrict`,
  `InverseGalois.CFT.subsingleton_tateHm1_orbitFamily_restrict`: **an orbit contributes nothing when
  the action on the subgroup at a point of it has vanishing Tate groups.**

## Tags

Tate cohomology, Herbrand quotient, orbit, family of modules, subgroup, idele
-/

namespace InverseGalois.CFT

open MulAction

variable {G X : Type*} [Group G] [MulAction G X] {σ : G}
  {M : X → Type*} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G) (N : ∀ x, AddSubgroup (M x))
  (hN : ∀ (g : G) (x : X), (N x).map (F.map g x).toAddMonoidHom = N (g • x))

/-! ### The action of the stabiliser on a restricted family -/

/-- **The action of the stabiliser of a point of an orbit on a restricted family is the restriction
of its action on the ambient family.** -/
theorem coe_stabAut_orbitFamily_restrict {ω : orbitRel.Quotient G X} (x₀ : ω.orbit)
    {H : Subgroup G} (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀)
    (hH'' : ∀ g : ↥H, (g : G) • (x₀ : X) = (x₀ : X)) (g : ↥H) (a : ↥(N (x₀ : X))) :
    ((stabAut x₀ hH' (orbitFamily (F.restrict N hN) ω) g a : ↥(N (x₀ : X))) : M (x₀ : X))
      = stabAut x₀ hH' (orbitFamily F ω) g ((a : M (x₀ : X))) := by
  rw [stabAut_orbitFamily (F.restrict N hN) x₀ hH' hH'' g a,
    FamilyAction.coe_restrict_transport, stabAut_orbitFamily F x₀ hH' hH'' g (a : M (x₀ : X))]

/-! ### Comparison with a known action on the subgroup -/

section Congr

variable {ω : orbitRel.Quotient G X} (x₀ : ω.orbit) {H : Subgroup G}
  (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀) (hH'' : ∀ g : ↥H, (g : G) • (x₀ : X) = (x₀ : X)) (g : ↥H)
  {P : AddSubgroup (M (x₀ : X))} (hNP : N (x₀ : X) = P) (τ : ↥P ≃+ ↥P)
  (hτ : ∀ a : ↥P, ((τ a : ↥P) : M (x₀ : X))
    = stabAut x₀ hH' (orbitFamily F ω) g ((a : ↥P) : M (x₀ : X)))

include hN hH'' hNP hτ

/-- The identification of the subgroup at the base point with the group it is declared to be
carries the action of the stabiliser to the given one. -/
theorem addSubgroupCongr_stabAut_orbitFamily_restrict (a : ↥(N (x₀ : X))) :
    AddEquiv.addSubgroupCongr hNP (stabAut x₀ hH' (orbitFamily (F.restrict N hN) ω) g a)
      = τ (AddEquiv.addSubgroupCongr hNP a) := by
  refine Subtype.ext ?_
  rw [AddEquiv.addSubgroupCongr_apply, coe_stabAut_orbitFamily_restrict F N hN x₀ hH' hH'' g a,
    hτ, AddEquiv.addSubgroupCongr_apply]

/-- The stabiliser acts on the subgroup at the base point with the Herbrand quotient of the given
action. -/
theorem herbrand_stabAut_orbitFamily_restrict (m : ℕ) :
    herbrand (stabAut x₀ hH' (orbitFamily (F.restrict N hN) ω) g) m = herbrand τ m :=
  herbrand_congr (AddEquiv.addSubgroupCongr hNP)
    (addSubgroupCongr_stabAut_orbitFamily_restrict F N hN x₀ hH' hH'' g hNP τ hτ) m

/-- The upper Tate group of the subgroup at the base point vanishes as soon as it vanishes for the
given action. -/
theorem subsingleton_tateH0_stabAut_orbitFamily_restrict (m : ℕ)
    (h : Subsingleton (tateH0 τ m)) :
    Subsingleton (tateH0 (stabAut x₀ hH' (orbitFamily (F.restrict N hN) ω) g) m) :=
  ⟨fun _ _ => (tateH0Congr (AddEquiv.addSubgroupCongr hNP)
    (addSubgroupCongr_stabAut_orbitFamily_restrict F N hN x₀ hH' hH'' g hNP τ hτ) m).injective
      (h.elim _ _)⟩

/-- The lower Tate group of the subgroup at the base point vanishes as soon as it vanishes for the
given action. -/
theorem subsingleton_tateHm1_stabAut_orbitFamily_restrict (m : ℕ)
    (h : Subsingleton (tateHm1 τ m)) :
    Subsingleton (tateHm1 (stabAut x₀ hH' (orbitFamily (F.restrict N hN) ω) g) m) :=
  ⟨fun _ _ => (tateHm1Congr (AddEquiv.addSubgroupCongr hNP)
    (addSubgroupCongr_stabAut_orbitFamily_restrict F N hN x₀ hH' hH'' g hNP τ hτ) m).injective
      (h.elim _ _)⟩

end Congr

/-! ### The subgroup at the base point is everything -/

section Top

variable {ω : orbitRel.Quotient G X} (x₀ : ω.orbit) {H : Subgroup G}
  (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀) (hH'' : ∀ g : ↥H, (g : G) • (x₀ : X) = (x₀ : X)) (g : ↥H)
  (hNtop : N (x₀ : X) = ⊤)

include hN hH'' hNtop

/-- The stabiliser acts on a subgroup that is everything as it acts on the ambient module. -/
theorem herbrand_stabAut_orbitFamily_restrict_top (m : ℕ) :
    herbrand (stabAut x₀ hH' (orbitFamily (F.restrict N hN) ω) g) m
      = herbrand (stabAut x₀ hH' (orbitFamily F ω) g) m :=
  herbrand_congr ((AddEquiv.addSubgroupCongr hNtop).trans AddSubgroup.topEquiv)
    (coe_stabAut_orbitFamily_restrict F N hN x₀ hH' hH'' g) m

end Top

/-! ### The contribution of one orbit -/

section Orbit

variable [Finite G] {ω : orbitRel.Quotient G X} [Fintype ω.orbit] (x₀ : ω.orbit)

omit [Finite G] [Fintype ↥ω.orbit] in
/-- A full turn of an orbit has order the order of the stabiliser of the base point. -/
theorem orbitTurn_pow_card {H : Subgroup G} (hH : ∀ g : G, g • x₀ = x₀ → g ∈ H) {m : ℕ}
    (hm : Nat.card ↥H = m) : (orbitTurn σ x₀ hH) ^ m = 1 := by
  rw [← hm]
  exact pow_card_eq_one'

/-- The length of an orbit times the order of the stabiliser of a point of it is the order of the
group. -/
theorem period_orbitShift_mul_card (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {n m : ℕ}
    (hn : Nat.card G = n) (hm : Nat.card ↥(stabilizer G x₀) = m) :
    period (orbitShift ↥ω.orbit σ) x₀ * m = n := by
  have hgen' : ∀ g : G, g ∈ Subgroup.zpowers σ⁻¹ := fun g => by
    rw [Subgroup.zpowers_inv]
    exact hgen g
  rw [show orbitShift (↥ω.orbit) σ = (toPerm σ⁻¹ : Equiv.Perm ↥ω.orbit) from rfl,
    period_eq_card_orbit hgen' x₀, ← hm, card_orbit_mul_card_stabilizer, hn]

end Orbit

/-! ### The Herbrand quotient of one orbit of a restricted family -/

section Contribution

variable {ω : orbitRel.Quotient G X} [Fintype ω.orbit] (x₀ : ω.orbit)
  (htrans : ∀ y : ω.orbit, ∃ j : ℕ, ((orbitShift ↥ω.orbit σ) ^ j) x₀ = y)
  {H : Subgroup G} (hH : ∀ g : G, g • x₀ = x₀ → g ∈ H)
  (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀) (hH'' : ∀ g : ↥H, (g : G) • (x₀ : X) = (x₀ : X))
  {m n : ℕ} (hz : (orbitTurn σ x₀ hH) ^ m = 1)
  (hdm : period (orbitShift ↥ω.orbit σ) x₀ * m = n)

include hN htrans hH hH' hH'' hz hdm

/-- **An orbit on which the family of subgroups is everything contributes to the restricted family
what it contributes to the ambient family.** -/
theorem herbrand_orbitFamily_restrict_top (hNtop : N (x₀ : X) = ⊤) :
    herbrand ((orbitFamily (F.restrict N hN) ω).familyAut σ) n
      = herbrand ((orbitFamily F ω).familyAut σ) n := by
  rw [herbrand_familyAut_orbit x₀ htrans hH hH' (orbitFamily (F.restrict N hN) ω) hz hdm,
    herbrand_familyAut_orbit x₀ htrans hH hH' (orbitFamily F ω) hz hdm]
  exact herbrand_stabAut_orbitFamily_restrict_top F N hN x₀ hH' hH'' _ hNtop m

section Vanishing

variable {P : AddSubgroup (M (x₀ : X))} (hNP : N (x₀ : X) = P) (τ : ↥P ≃+ ↥P)
  (hτ : ∀ a : ↥P, ((τ a : ↥P) : M (x₀ : X))
    = stabAut x₀ hH' (orbitFamily F ω) (orbitTurn σ x₀ hH) ((a : ↥P) : M (x₀ : X)))

include hNP hτ

/-- **An orbit contributes nothing to the upper Tate group of the restricted family** when the
action on the subgroup at a point of it has vanishing upper Tate group. -/
theorem subsingleton_tateH0_orbitFamily_restrict (h : Subsingleton (tateH0 τ m)) :
    Subsingleton (tateH0 ((orbitFamily (F.restrict N hN) ω).familyAut σ) n) :=
  subsingleton_tateH0_familyAut_orbit x₀ htrans hH hH' (orbitFamily (F.restrict N hN) ω) hz hdm
    (subsingleton_tateH0_stabAut_orbitFamily_restrict F N hN x₀ hH' hH'' _ hNP τ hτ m h)

/-- **An orbit contributes nothing to the lower Tate group of the restricted family** when the
action on the subgroup at a point of it has vanishing lower Tate group. -/
theorem subsingleton_tateHm1_orbitFamily_restrict (h : Subsingleton (tateHm1 τ m)) :
    Subsingleton (tateHm1 ((orbitFamily (F.restrict N hN) ω).familyAut σ) n) :=
  subsingleton_tateHm1_familyAut_orbit x₀ htrans hH hH' (orbitFamily (F.restrict N hN) ω) hz hdm
    (subsingleton_tateHm1_stabAut_orbitFamily_restrict F N hN x₀ hH' hH'' _ hNP τ hτ m h)

end Vanishing

end Contribution

end InverseGalois.CFT
