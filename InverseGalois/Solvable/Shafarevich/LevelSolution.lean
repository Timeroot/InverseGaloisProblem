/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Realize
import InverseGalois.Solvable.Shafarevich.LayerTower

/-!
# Climbing the filtration with the local conditions carried along

The tower of the descending `p`-central series presents the group a split embedding problem asks
for as the top of a finite ladder, and what is left is the step from one layer to the next.  Stated
between bare realizations that step cannot be proved, and the reason is a matter of order: making
the class of the next layer die costs letters, the number of letters is settled only once the
subgroups it has to die on are known, and those subgroups come from the places of the base field at
which the realization already reached must be locally trivial.  A realization which is only known
to exist gives no such places, since the field it names may change with the number of letters.

The remedy is to fix the base realization once and to carry the local conditions up the ladder.  A
*solution at one level* is therefore a smooth surjection of the Galois group of a fixed
algebraically closed extension onto the group at that level which projects onto the given base
realization and is trivial on a prescribed family of subgroups wherever the base realization is;
this last clause is the group theoretic reading of a place being completely decomposed in the field
the level cuts out over the field the base realization cuts out.  Both ends of the ladder are
unaffected by the extra clause: at the bottom the group at the level is the base group itself and
the base realization does the work, at the top the group at the level covers the group asked for
and the clause is discarded.

A solution is also asked to carry a property fixed in advance, which the ladder transports from one
level to the next.  Nothing here says what the property is: it is a parameter, and the ladder is
indifferent to it, both ends of it discarding the clause exactly as they discard the clause about
the family.  In the arithmetic the property is the second half of the local prescription — that a
place ramifying in the field the level cuts out over the field the base realization cuts out splits
completely in the latter and is there totally ramified — which the local solvability of the next
step consumes and which no amount of group theory can supply.

## Main definitions

* `InverseGalois.Shafarevich.LevelProperty` — a property a solution at a level may be asked to
  carry.
* `InverseGalois.Shafarevich.LevelSolution` — a solution at one level of the filtration, projecting
  onto a fixed base realization, completely decomposed along a prescribed family of subgroups and
  carrying a prescribed property.
* `Shafarevich.GenericLevelStepEP` — **one step of the ladder**, with the family of subgroups and
  the property chosen once from the base realization and then held fixed.

## Main results

* `InverseGalois.Shafarevich.levelSolution_zero` — the bottom of the ladder is the base realization.
* `InverseGalois.Shafarevich.isInverseGalois_of_levelSolution` — the top of the ladder realizes the
  group the split embedding problem asks for.
* `Shafarevich.genericSplitEP_of_genericLevelStepEP` — **climbing the ladder one layer at a time
  solves the generic split embedding problem.**
* `Shafarevich.splitPrimePowerEP_of_genericLevelStepEP` — **and hence every split embedding problem
  with a kernel of prime power order.**

## Tags

Shafarevich's theorem, embedding problem, p-central series, decomposition group, local conditions
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

/-! ### A property carried up the ladder -/

/-- **A property a solution at a level may be asked to carry**, over and above being a smooth
surjection over the base realization which is trivial along the family.

The property is indexed by the number of letters and by the level, since a solution at a level is,
and it is a parameter of everything below: no statement of the ladder inspects it, and only the
arithmetic that feeds the ladder ever chooses it. -/
abbrev LevelProperty (ℓ : ℕ) (U : Type) [Group U] (S : Type) [Group S] (k Ω : Type*) [Field k]
    [Field Ω] [Algebra k Ω] :=
  ∀ m j : ℕ, (Gal(Ω/k) →* GenericQuot ℓ U m S j) → Prop

/-! ### A solution at one level -/

/-- **A solution at one level of the filtration.**  A smooth surjection of the Galois group onto the
group at that level which projects onto the given base realization, which is trivial on each of
a prescribed family of subgroups wherever the base realization is, and which carries a prescribed
property.

The clause about the family says that the places it names are completely decomposed in the field the
level cuts out over the field the base realization cuts out: a decomposition subgroup meets the
kernel of the base realization exactly in the inertia and decomposition data of the smaller field,
and asking it to lie in the kernel of the solution is asking the local degree of the bigger field
over the smaller one to be one.  The clause about the property is what carries the rest of the local
prescription up the ladder; the group theory never reads it. -/
def LevelSolution (ℓ : ℕ) (U : Type) [Group U] (S : Type) [Group S] {k Ω : Type*} [Field k]
    [Field Ω] [Algebra k Ω] (φ : Gal(Ω/k) →* U) (T : Set (Subgroup Gal(Ω/k)))
    (P : LevelProperty ℓ U S k Ω) (m j : ℕ) : Prop :=
  ∃ Φ : Gal(Ω/k) →* GenericQuot ℓ U m S j, Function.Surjective Φ ∧ IsSmoothHom Φ ∧
    (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) ∧
      (∀ D ∈ T, ∀ x ∈ D, φ x = 1 → Φ x = 1) ∧ P m j Φ

/-! ### The bottom of the ladder -/

/-- **At the bottom of the filtration a solution is the base realization itself.**  The group at the
zeroth level is the base group, so the base realization is a solution there, and it is trivially
completely decomposed everywhere over itself. -/
theorem levelSolution_zero (ℓ : ℕ) (U : Type) [Group U] [TopologicalSpace U] [DiscreteTopology U]
    (S : Type) [Group S] {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (φ : Gal(Ω/k) →* U)
    (hsurj : Function.Surjective φ) (hsm : IsSmoothHom φ) (T : Set (Subgroup Gal(Ω/k)))
    (P : LevelProperty ℓ U S k Ω) (m : ℕ)
    (hP : P m 0 ((pCentralZeroEquiv ℓ (genericAut U m S)).symm.toMonoidHom.comp φ)) :
    LevelSolution ℓ U S φ T P m 0 := by
  refine ⟨(pCentralZeroEquiv ℓ (genericAut U m S)).symm.toMonoidHom.comp φ,
    (pCentralZeroEquiv ℓ (genericAut U m S)).symm.surjective.comp hsurj,
    isSmoothHom_comp hsm (isSmoothHom_of_continuous continuous_of_discreteTopology),
    fun x => rfl, fun D _ x _ hx => ?_, hP⟩
  show (pCentralZeroEquiv ℓ (genericAut U m S)).symm (φ x) = 1
  rw [hx, _root_.map_one]

/-! ### The top of the ladder -/

/-- **At the top of the filtration a solution realizes the group the split embedding problem asks
for.**  When a term of the descending `ℓ`-central series is trivial the group at that level covers
the semidirect product wanted, and a smooth surjection composed with that covering is again a
smooth surjection. -/
theorem isInverseGalois_of_levelSolution {ℓ : ℕ} (U : Type) [Group U] (S : Type) [Group S]
    {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω] {φ : Gal(Ω/ℚ) →* U}
    {T : Set (Subgroup Gal(Ω/ℚ))} {P : LevelProperty ℓ U S ℚ Ω} {m j : ℕ}
    (hj : pCentral ℓ (Generic U m S) j = ⊥) (h : LevelSolution ℓ U S φ T P m j) :
    IsInverseGalois (Generic U m S ⋊[genericAut U m S] U) := by
  obtain ⟨Φ, hsurj, hsm, -, -, -⟩ := h
  letI : TopologicalSpace (Generic U m S ⋊[genericAut U m S] U) := ⊥
  haveI : DiscreteTopology (Generic U m S ⋊[genericAut U m S] U) := ⟨rfl⟩
  exact isInverseGalois_of_smooth_surjective
    ((pCentralBotSemidirectHom (genericAut U m S) hj).comp Φ)
    (isSmoothHom_comp hsm (isSmoothHom_of_continuous continuous_of_discreteTopology))
    ((pCentralBotSemidirectHom_surjective _ hj).comp hsurj)

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

/-! ### One step of the ladder -/

/-- **One step of the ladder of the descending `ℓ`-central series, with the local conditions carried
along.**

Given a base realization, a family of subgroups is chosen once and for all — in the arithmetic it is
the family of decomposition subgroups at the places which ramify in the field the base realization
cuts out, at the places above `ℓ` and at the infinite places — and then, for every term of the
series, solving at that term for *every* number of letters solves at the next term.

The solution at the previous term is required for every number of letters because the step is
allowed to shrink: making the class of the extension die on the prescribed subgroups costs letters,
and how many it costs is settled only once those subgroups are known.  The family being chosen
before the induction begins is what makes that order of quantifiers consistent.  The property the
solutions carry is chosen at the same moment and for the same reason, and the bottom of the ladder
is asked for outright, since a property no statement of the ladder inspects cannot be produced by
one. -/
def GenericLevelStepEP (ℓ : ℕ) : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] [TopologicalSpace U]
      [DiscreteTopology U] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (φ : Gal(Ω/ℚ) →* U), IsPGroup ℓ S → Function.Surjective φ → IsSmoothHom φ →
    ∃ (T : Set (Subgroup Gal(Ω/ℚ))) (P : LevelProperty ℓ U S ℚ Ω),
      (∀ m : ℕ, LevelSolution ℓ U S φ T P m 0) ∧ ∀ j : ℕ,
        (∀ m : ℕ, LevelSolution ℓ U S φ T P m j) → ∀ n : ℕ, LevelSolution ℓ U S φ T P n (j + 1)

/-- **Climbing the ladder**: one step at a time solves the problem at every term of the descending
`ℓ`-central series, for every number of letters. -/
theorem forall_levelSolution {ℓ : ℕ} (U : Type) [Group U] (S : Type) [Group S] {Ω : Type}
    [Field Ω] [Algebra ℚ Ω] {φ : Gal(Ω/ℚ) →* U} {T : Set (Subgroup Gal(Ω/ℚ))}
    {P : LevelProperty ℓ U S ℚ Ω} (hbase : ∀ m : ℕ, LevelSolution ℓ U S φ T P m 0)
    (hstep : ∀ j : ℕ, (∀ m : ℕ, LevelSolution ℓ U S φ T P m j) →
      ∀ n : ℕ, LevelSolution ℓ U S φ T P n (j + 1)) (j : ℕ) :
    ∀ m : ℕ, LevelSolution ℓ U S φ T P m j := by
  induction j with
  | zero => exact hbase
  | succ j ih => exact fun n => hstep j ih n

/-- **One layer at a time solves the generic split embedding problem.** -/
theorem genericSplitEP_of_genericLevelStepEP {ℓ : ℕ} [Fact ℓ.Prime] (h : GenericLevelStepEP ℓ) :
    GenericSplitEP ℓ := by
  intro S U _ _ _ _ n hS hU
  letI : TopologicalSpace U := ⊥
  haveI : DiscreteTopology U := ⟨rfl⟩
  obtain ⟨φ, hφsurj, hφsm⟩ :=
    (isInverseGalois_iff_exists_smooth_surjective (Ω := AlgebraicClosure ℚ)).1 hU
  obtain ⟨T, P, hbase, hstep⟩ := h S U (AlgebraicClosure ℚ) φ hS hφsurj hφsm
  obtain ⟨j, hj⟩ := exists_pCentral_eq_bot ℓ (isPGroup_generic U n S hS)
  exact isInverseGalois_of_levelSolution U S hj (forall_levelSolution U S hbase hstep j n)

/-- **One layer at a time solves every split embedding problem with a kernel of prime power
order.** -/
theorem splitPrimePowerEP_of_genericLevelStepEP
    (h : ∀ ℓ : ℕ, ℓ.Prime → GenericLevelStepEP ℓ) : SplitPrimePowerEP := by
  intro H U _ _ _ _ p hp hH φ hU
  exact isInverseGalois_semidirectProduct_of_generic φ
    (genericSplitEP_of_genericLevelStepEP (h p hp.out) H U (Nat.card H) hH hU)

end Shafarevich
