/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Rigidity.RET.Descent.TameRamification
import InverseGalois.Rigidity.RET.Descent.WildInertia

/-!
# Ramification of a cover of the line over an arbitrary algebraically closed constant field

A finite Galois extension `Ω` of `κ(T)`, with `κ` algebraically closed of characteristic zero, has
an integral model over `κ[X]`: the integral closure of `κ[X]` in `Ω`.  It is a Dedekind domain, the
deck group acts on it, and the pair `κ[X] ⊆ Ω` is an AKLB situation whose Galois group is the deck
group.  This file assembles that instance stack once and derives the two facts about ramification at
a point `t` of the line that the geometry needs.

Both rest on the residue fields being trivial extensions of `κ`: the residue field of `κ[X]` at
`X - t` is `κ` itself, which is algebraically closed, so every residue upstairs is a constant.
Consequently the inertia group at a place is its whole stabilizer, and — by the AKLB counting
theorem — has order the ramification index at that place.  Over a non-closed constant field neither
statement holds: the residue extension carries the difference.

The constant field is left general because the same statements are needed both over `ℚ̄`, where the
descent to a number field takes place, and over `ℂ`, where the analytic branches live.

## Main definitions

* `Rigidity.RET.AKLBGen.Bring` — the integral model of `Ω` over `κ[X]`.
* `Rigidity.RET.AKLBGen.placeP` — the place `X - t` of `κ[X]`.

## Main results

* `Rigidity.RET.AKLBGen.exists_poly_sub_mem` — every element of the integral model is congruent to a
  constant at a place over `t`.
* `Rigidity.RET.AKLBGen.inertia_eq_stabilizer` — inertia is the whole decomposition group.
* `Rigidity.RET.AKLBGen.card_inertia` — the inertia group has order the ramification index.
-/

open Polynomial
open scoped Pointwise

noncomputable section

namespace Rigidity.RET.AKLBGen

attribute [local instance] Ideal.Quotient.field

variable (κ : Type*) [Field κ] [CharZero κ] [IsAlgClosed κ]
  (Ω : Type*) [Field Ω] [Algebra (RatFunc κ) Ω] [FiniteDimensional (RatFunc κ) Ω]
  [IsGalois (RatFunc κ) Ω] [Algebra (Polynomial κ) Ω]
  [IsScalarTower (Polynomial κ) (RatFunc κ) Ω]

/-- **The integral model of a cover of the line**: the integral closure of `κ[X]` in `Ω`. -/
abbrev Bring : Type _ := integralClosure (Polynomial κ) Ω

local instance instMSA : MulSemiringAction (Ω ≃ₐ[RatFunc κ] Ω) (Bring κ Ω) :=
  IsIntegralClosure.MulSemiringAction (Polynomial κ) (RatFunc κ) Ω (Bring κ Ω)

local instance instIsFrac : IsFractionRing (Bring κ Ω) Ω :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial κ) (RatFunc κ) Ω (Bring κ Ω)

local instance instIGG : IsGaloisGroup (Ω ≃ₐ[RatFunc κ] Ω) (Polynomial κ) (Bring κ Ω) :=
  IsGaloisGroup.of_isFractionRing (Ω ≃ₐ[RatFunc κ] Ω) (Polynomial κ) (Bring κ Ω) (RatFunc κ) Ω

local instance instFinite : Module.Finite (Polynomial κ) (Bring κ Ω) :=
  IsIntegralClosure.finite (Polynomial κ) (RatFunc κ) Ω (Bring κ Ω)

local instance instIntegral : Algebra.IsIntegral (Polynomial κ) (Bring κ Ω) :=
  IsIntegralClosure.isIntegral_algebra (Polynomial κ) Ω

local instance instFaithful : FaithfulSMul (Polynomial κ) (Bring κ Ω) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have hAL : Function.Injective (algebraMap (Polynomial κ) Ω) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial κ) (RatFunc κ) Ω]
    exact (algebraMap (RatFunc κ) Ω).injective.comp
      (IsFractionRing.injective (Polynomial κ) (RatFunc κ))
  intro x y hxy
  apply hAL
  rw [IsScalarTower.algebraMap_apply (Polynomial κ) (Bring κ Ω) Ω,
    IsScalarTower.algebraMap_apply (Polynomial κ) (Bring κ Ω) Ω, hxy]

local instance instDedekindB : IsDedekindDomain (Bring κ Ω) :=
  integralClosure.isDedekindDomain (Polynomial κ) (RatFunc κ) Ω

set_option synthInstance.maxHeartbeats 400000 in
local instance (priority := high) instTorsionFree :
    Module.IsTorsionFree (Polynomial κ) (Bring κ Ω) := inferInstance

local instance instFiniteGal : Finite (Ω ≃ₐ[RatFunc κ] Ω) := inferInstance

/-- The place `X - t` of `κ[X]`, that is, the point `t` of the line. -/
abbrev placeP (t : κ) : Ideal (Polynomial κ) := Ideal.span {(X - C t : Polynomial κ)}

instance placeP_max (t : κ) : (placeP κ t).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C _)

omit [CharZero κ] [IsAlgClosed κ] in
theorem placeP_ne_bot (t : κ) : placeP κ t ≠ ⊥ := by
  rw [placeP, Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero _

instance instCharZeroResidue (t : κ) : CharZero (Polynomial κ ⧸ placeP κ t) :=
  charZero_of_injective_algebraMap (algebraMap κ (Polynomial κ ⧸ placeP κ t)).injective

/-- The residue field at a point of the line is the constant field. -/
instance instIsAlgClosedResidue (t : κ) : IsAlgClosed (Polynomial κ ⧸ placeP κ t) :=
  IsAlgClosed.of_ringEquiv κ _ (Polynomial.quotientSpanXSubCAlgEquiv t).symm.toRingEquiv

omit [Algebra (RatFunc κ) Ω] [FiniteDimensional (RatFunc κ) Ω] [IsGalois (RatFunc κ) Ω]
  [IsAlgClosed κ] in
theorem residue_isSeparable (t : κ) (Q : Ideal (Bring κ Ω)) [Q.IsMaximal]
    [Q.LiesOver (placeP κ t)] :
    Algebra.IsSeparable (Polynomial κ ⧸ placeP κ t) (Bring κ Ω ⧸ Q) := by
  haveI : Q.IsPrime := ‹Q.IsMaximal›.isPrime
  infer_instance

omit [FiniteDimensional (RatFunc κ) Ω] [CharZero κ] [IsAlgClosed κ] in
/-- The action of the deck group on the integral model is the restriction of its action on `Ω`. -/
theorem coe_smul (σ : Ω ≃ₐ[RatFunc κ] Ω) (x : Bring κ Ω) : ((σ • x : Bring κ Ω) : Ω) = σ x :=
  algebraMap_galRestrict_apply (Polynomial κ) σ x

set_option synthInstance.maxHeartbeats 400000 in
omit [IsAlgClosed κ] in
/-- A place lying over a point of the line is nonzero. -/
theorem ne_bot_of_liesOver (t : κ) (Q : Ideal (Bring κ Ω)) [Q.LiesOver (placeP κ t)] : Q ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (placeP_ne_bot κ t) Q

omit [CharZero κ] [IsAlgClosed κ] in
/-- The deck group fixes the constants of the integral model: it acts by `κ[X]`-algebra maps. -/
theorem smul_algebraMap_poly (g : Ω ≃ₐ[RatFunc κ] Ω) (f : Polynomial κ) :
    g • (algebraMap (Polynomial κ) (Bring κ Ω) f) = algebraMap (Polynomial κ) (Bring κ Ω) f := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

omit [Algebra (RatFunc κ) Ω] [FiniteDimensional (RatFunc κ) Ω] [IsGalois (RatFunc κ) Ω]
  [IsScalarTower (Polynomial κ) (RatFunc κ) Ω] [CharZero κ] in
/-- **Every element of the integral model is congruent to a constant at a place over `t`.**

The residue field at a place above `X - t` is integral over the residue field `κ` of the point, and
`κ` is algebraically closed, so the residue extension is trivial. -/
theorem exists_poly_sub_mem (t : κ) (Q : Ideal (Bring κ Ω)) [Q.IsMaximal]
    [Q.LiesOver (placeP κ t)] (x : Bring κ Ω) :
    ∃ f : Polynomial κ, x - algebraMap (Polynomial κ) (Bring κ Ω) f ∈ Q := by
  haveI : Algebra.IsIntegral (Polynomial κ ⧸ placeP κ t) (Bring κ Ω ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := Polynomial κ)
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := Polynomial κ ⧸ placeP κ t) (K := Bring κ Ω ⧸ Q)).2 (Ideal.Quotient.mk Q x)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨f, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
omit [CharZero κ] in
/-- **Inertia is the whole decomposition group at a place over a point of the line.**

An element stabilizing the place acts trivially on the residue field, because every residue is a
constant and the constants are fixed; so it lies in the inertia group. -/
theorem inertia_eq_stabilizer (t : κ) (Q : Ideal (Bring κ Ω)) [Q.IsMaximal]
    [Q.LiesOver (placeP κ t)] :
    Q.inertia (Ω ≃ₐ[RatFunc κ] Ω) = MulAction.stabilizer (Ω ≃ₐ[RatFunc κ] Ω) Q := by
  refine le_antisymm (Ideal.inertia_le_stabilizer Q) fun σ hσ => ?_
  have hQ : σ • Q = Q := hσ
  refine AddSubgroup.mem_inertia.mpr fun x => ?_
  obtain ⟨f, hf⟩ := exists_poly_sub_mem κ Ω t Q x
  have h1 : σ • x - x
      = σ • (x - algebraMap (Polynomial κ) (Bring κ Ω) f)
        - (x - algebraMap (Polynomial κ) (Bring κ Ω) f) := by
    rw [smul_sub, smul_algebraMap_poly]
    abel
  rw [Submodule.mem_toAddSubgroup, h1]
  refine Q.sub_mem ?_ hf
  rw [← hQ]
  exact Ideal.smul_mem_pointwise_smul _ _ _ hf

set_option synthInstance.maxHeartbeats 400000 in
omit [IsAlgClosed κ] in
/-- **The inertia group at a place over `t` has order the ramification index there.** -/
theorem card_inertia (t : κ) (Q : Ideal (Bring κ Ω)) [Q.IsMaximal] [Q.LiesOver (placeP κ t)] :
    Nat.card (Q.inertia (Ω ≃ₐ[RatFunc κ] Ω)) = Ideal.ramificationIdxIn (placeP κ t) (Bring κ Ω) := by
  haveI := residue_isSeparable κ Ω t Q
  exact Ideal.card_inertia_eq_ramificationIdxIn (placeP κ t) (placeP_ne_bot κ t) Q

end Rigidity.RET.AKLBGen

end
