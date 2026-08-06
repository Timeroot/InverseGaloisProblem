/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.TameRamification
import InverseGalois.Rigidity.RET.Descent.WildInertia

/-!
# The geometric AKLB ramification scaffold over the algebraically closed constant field

For a finite Galois extension `Ω` of `k(T) = RatFunc k` with `k := AlgebraicClosure ℚ` the
algebraically closed constant field, this module builds the integral model `k[X] ⊆ B` where
`B := integralClosure (Polynomial k) Ω`, together with the full ramification-theoretic instance
stack: the Galois action of `Ω ≃ₐ[k(T)] Ω` on `B`, the fraction-field identifications, the Galois
group structure, Dedekind-domain and finiteness instances, and the geometric places
`P = (X - t)` for points `t : k`.

Because the constant field `k` has characteristic zero, the residue extensions are automatically
separable, so the ramification lemmas of `TameRamification` apply with all hypotheses discharged:
an inertia element's order divides the ramification index, and inertia transports along the Galois
action on primes.

## Main results

* `Bring Ω` — the geometric integral-closure ring `B`, with its instance stack.
* `placeP t` — the geometric place `(X - t)` of `k[X]`.
* `exists_Q_over_placeP` — a maximal prime `Q` of `B` lying over `P = (X - t)`.
* `residue_isSeparable` — the residue extension `B/Q` over `k[X]/(X - t)` is separable.
* `geom_orderOf_dvd_ramificationIdxIn` — an inertia element's order divides the ramification index.
* `geom_mem_inertia_smul_iff` — inertia transports along the Galois action on primes.
-/

open Polynomial
open scoped Pointwise

noncomputable section

namespace GeomAKLB

/-- The algebraically closed constant field. -/
abbrev k : Type := AlgebraicClosure ℚ

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

attribute [local instance] Ideal.Quotient.field

variable
  (Ω : Type) [Field Ω] [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω]
  [IsGalois (RatFunc k) Ω]
  [Algebra (Polynomial k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω]

/-! ## Integral model `A = k[X] ⊆ B = integralClosure A Ω`, and the place `P = (X - t)`. -/

/-- Integral closure of `k[X]` in `Ω`; the geometric ring `B`. -/
abbrev Bring : Type := integralClosure (Polynomial k) Ω

noncomputable local instance instMSA :
    MulSemiringAction (Ω ≃ₐ[RatFunc k] Ω) (Bring Ω) :=
  IsIntegralClosure.MulSemiringAction (Polynomial k) (RatFunc k) Ω (Bring Ω)

local instance instIsFrac : IsFractionRing (Bring Ω) Ω :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial k) (RatFunc k) Ω (Bring Ω)

local instance instIGG : IsGaloisGroup (Ω ≃ₐ[RatFunc k] Ω) (Polynomial k) (Bring Ω) :=
  IsGaloisGroup.of_isFractionRing (Ω ≃ₐ[RatFunc k] Ω) (Polynomial k) (Bring Ω) (RatFunc k) Ω

local instance instFinite : Module.Finite (Polynomial k) (Bring Ω) :=
  IsIntegralClosure.finite (Polynomial k) (RatFunc k) Ω (Bring Ω)

local instance instIntegral : Algebra.IsIntegral (Polynomial k) (Bring Ω) :=
  IsIntegralClosure.isIntegral_algebra (Polynomial k) Ω

local instance instFaithful : FaithfulSMul (Polynomial k) (Bring Ω) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have hAL : Function.Injective (algebraMap (Polynomial k) Ω) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial k) (RatFunc k) Ω]
    exact (algebraMap (RatFunc k) Ω).injective.comp
      (IsFractionRing.injective (Polynomial k) (RatFunc k))
  intro x y hxy
  apply hAL
  rw [IsScalarTower.algebraMap_apply (Polynomial k) (Bring Ω) Ω,
    IsScalarTower.algebraMap_apply (Polynomial k) (Bring Ω) Ω, hxy]

local instance instDedekindB : IsDedekindDomain (Bring Ω) :=
  integralClosure.isDedekindDomain (Polynomial k) (RatFunc k) Ω

local instance instTorsionFree : Module.IsTorsionFree (Polynomial k) (Bring Ω) := inferInstance

local instance instFiniteGal : Finite (Ω ≃ₐ[RatFunc k] Ω) := inferInstance

/-- The geometric place `P = (X - t)` of `k[X]`, for a point `t : k`. -/
abbrev placeP (t : k) : Ideal (Polynomial k) := Ideal.span {(X - C t : Polynomial k)}

instance placeP_max (t : k) : (placeP t).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C _)

theorem placeP_ne_bot (t : k) : placeP t ≠ ⊥ := by
  rw [placeP, Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero _

/-! ## A prime `Q` of `B` lying over the place, obtained by going-up. -/

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] in
/-- There is a maximal ideal `Q` of `B` lying over the geometric place `P = (X - t)`. -/
theorem exists_Q_over_placeP (t : k) :
    ∃ Q : Ideal (Bring Ω), Q.IsMaximal ∧ Q.LiesOver (placeP t) := by
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := Polynomial k) (S := Bring Ω)
      (placeP t)
  exact ⟨Q, hQmax, hQover⟩

/-! ## Char-0 separability of the residue extension is automatic. -/

/-- The base residue field `k[X]/(X - t)` has characteristic zero (it is a `k`-algebra and `k`
has characteristic zero). -/
instance instCharZeroResidue (t : k) : CharZero (Polynomial k ⧸ placeP t) :=
  charZero_of_injective_algebraMap (algebraMap k (Polynomial k ⧸ placeP t)).injective

omit [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] in
/-- With `Q` maximal, both residue rings are fields; the base residue field has characteristic
zero (hence is perfect), so the residue extension `B/Q` over `k[X]/(X - t)` is separable. -/
theorem residue_isSeparable (t : k) (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    Algebra.IsSeparable (Polynomial k ⧸ placeP t) (Bring Ω ⧸ Q) := by
  haveI : Q.IsPrime := ‹Q.IsMaximal›.isPrime
  haveI : CharZero (Polynomial k ⧸ placeP t) := inferInstance
  infer_instance

/-! ## The inertia subgroup as a real `Subgroup`, and the ramification lemmas applied. -/

/-- `Q.inertia G` is a genuine `Subgroup` of the geometric Galois group `G = Ω ≃ₐ[k(T)] Ω`. -/
abbrev geomInertia (Q : Ideal (Bring Ω)) : Subgroup (Ω ≃ₐ[RatFunc k] Ω) :=
  Q.inertia (Ω ≃ₐ[RatFunc k] Ω)

/-- An inertia element's order divides the ramification index at `Q`. -/
theorem geom_orderOf_dvd_ramificationIdxIn
    (t : k) (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP t)]
    {g : Ω ≃ₐ[RatFunc k] Ω} (hg : g ∈ Q.inertia (Ω ≃ₐ[RatFunc k] Ω)) :
    orderOf g ∣ Ideal.ramificationIdxIn (placeP t) (Bring Ω) := by
  haveI := residue_isSeparable Ω t Q
  exact Rigidity.RET.orderOf_dvd_ramificationIdxIn_of_mem_inertia
    (placeP t) (placeP_ne_bot t) Q hg

omit [FiniteDimensional (RatFunc k) Ω] in
/-- Inertia transports along the Galois action on primes: `σ` lies in the inertia group of
`g • Q` iff its conjugate lies in the inertia group of `Q`. -/
theorem geom_mem_inertia_smul_iff
    (g σ : Ω ≃ₐ[RatFunc k] Ω) (Q : Ideal (Bring Ω)) :
    σ ∈ (g • Q).inertia (Ω ≃ₐ[RatFunc k] Ω) ↔
      g⁻¹ * σ * g ∈ Q.inertia (Ω ≃ₐ[RatFunc k] Ω) :=
  Rigidity.RET.mem_inertia_smul_iff g σ Q

/-- A maximal prime over the place, with its inertia subgroup and the ramification-index
divisibility. -/
theorem geom_inertia_package (t : k) :
    ∃ Q : Ideal (Bring Ω), ∃ _ : Q.IsMaximal, ∃ _ : Q.LiesOver (placeP t),
      ∀ {g : Ω ≃ₐ[RatFunc k] Ω}, g ∈ Q.inertia (Ω ≃ₐ[RatFunc k] Ω) →
        orderOf g ∣ Ideal.ramificationIdxIn (placeP t) (Bring Ω) := by
  obtain ⟨Q, hQmax, hQover⟩ := exists_Q_over_placeP Ω t
  refine ⟨Q, hQmax, hQover, ?_⟩
  intro g hg
  exact geom_orderOf_dvd_ramificationIdxIn Ω t Q hg

/-! ## Cyclicity of the geometric inertia groups. -/

section Cyclic

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] in
/-- A prime over the geometric place is nonzero. -/
theorem Q_ne_bot (t : k) (Q : Ideal (Bring Ω)) [Q.LiesOver (placeP t)] : Q ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (placeP_ne_bot t) Q

/-- The residue field of the geometric place is `k` itself, hence algebraically closed. -/
instance instIsAlgClosedResidue (t : k) : IsAlgClosed (Polynomial k ⧸ placeP t) :=
  IsAlgClosed.of_ringEquiv k _ (Polynomial.quotientSpanXSubCAlgEquiv t).symm.toRingEquiv

omit [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] in
/-- The residue field at `Q` has characteristic zero. -/
theorem charZero_residue_top (t : k) (Q : Ideal (Bring Ω)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] : CharZero (Bring Ω ⧸ Q) :=
  charZero_of_injective_algebraMap
    (algebraMap (Polynomial k ⧸ placeP t) (Bring Ω ⧸ Q)).injective

/-- **The residues at a geometric place are constants.**

The residue field `B/Q` is integral over the residue field `k[X]/(X - t) = k` of the place, and `k`
is algebraically closed, so every element of `B` is congruent modulo `Q` to a constant — which the
geometric Galois group fixes, since it acts by `k(T)`-algebra automorphisms. -/
theorem residueFixed_geom (t : k) (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    Rigidity.RET.ResidueFixed Q (Ω ≃ₐ[RatFunc k] Ω) := by
  haveI : Algebra.IsIntegral (Polynomial k ⧸ placeP t) (Bring Ω ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := Polynomial k)
  intro x
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := Polynomial k ⧸ placeP t) (K := Bring Ω ⧸ Q)).2 (Ideal.Quotient.mk Q x)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨algebraMap (Polynomial k) (Bring Ω) f, fun g _ => ?_, ?_⟩
  · rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  · rw [← Ideal.Quotient.eq, ← hc]
    rfl

/-- **The inertia group of a geometric place is cyclic.**

Over an algebraically closed constant field of characteristic zero all ramification is tame: wild
inertia vanishes (`Rigidity.RET.inertia_pow_sq_eq_bot`) and the tame character embeds the inertia
group into the multiplicative group of the residue field. -/
theorem isCyclic_geomInertia (t : k) (Q : Ideal (Bring Ω)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] : IsCyclic (geomInertia Ω Q) := by
  haveI := charZero_residue_top Ω t Q
  haveI : FaithfulSMul (Ω ≃ₐ[RatFunc k] Ω) (Bring Ω) := IsGaloisGroup.faithful (A := Polynomial k)
  obtain ⟨π, hπ, hπ2⟩ := Rigidity.RET.exists_uniformizer Q (Q_ne_bot Ω t Q)
  exact Rigidity.RET.isCyclic_inertia Q (Q_ne_bot Ω t Q) hπ hπ2 (residueFixed_geom Ω t Q)

end Cyclic

end GeomAKLB
