/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Differentiating along an unramified extension

A derivation of a ring extends to any extension that is unramified over it, and does so in exactly
one way.  Both halves of that statement come from the module of differentials: unramifiedness says
the relative differentials vanish, so no room is left for two extensions to differ, and étaleness
says the differentials of the larger ring are the differentials of the smaller one carried across,
so a derivation downstairs is the same thing as one upstairs.

The consequence that matters for covers of the line is a stability statement rather than an
existence one.  A ring of integral elements is unramified over the ring it is integral over exactly
when the cover it describes is unbranched, and then differentiating cannot leave the ring of
integral elements: the composite of the derivation with the projection onto the quotient by that
ring is itself a derivation, of the small ring into a module over the big one, and unramifiedness
kills it.

## Main definitions

* `Rigidity.RET.etaleLift` — the extension of a derivation along a formally étale algebra.

## Main results

* `Rigidity.RET.derivation_apply_eq_zero_of_formallyUnramified` — an unramified extension carries
  no derivations.
* `Rigidity.RET.derivation_eq_of_eqOn_base` — a derivation is determined by its restriction to an
  unramified subalgebra.
* `Rigidity.RET.etaleLift_algebraMap` — the extension of a derivation restricts to it.
* `Rigidity.RET.deriv_mem_integralClosure` — a derivation carrying a ring into its integral closure
  carries the integral closure into itself, when that closure is unramified.
-/

noncomputable section

namespace Rigidity.RET

/-! ## An unramified extension carries no derivations -/

section Vanishing

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- **An unramified extension carries no derivations.** -/
theorem derivation_apply_eq_zero_of_formallyUnramified [Algebra.FormallyUnramified R A]
    (d : Derivation R A M) (a : A) : d a = 0 := by
  rw [← d.liftKaehlerDifferential_comp_D a,
    Subsingleton.elim (KaehlerDifferential.D R A a) 0, map_zero]

theorem derivation_eq_zero_of_formallyUnramified [Algebra.FormallyUnramified R A]
    (d : Derivation R A M) : d = 0 := by
  ext a
  exact derivation_apply_eq_zero_of_formallyUnramified d a

end Vanishing

/-! ## A derivation is determined by its restriction to an unramified subalgebra -/

section Unique

variable {R S T M : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [AddCommGroup M] [Module R M] [Module S M] [Module T M]
  [IsScalarTower R T M] [IsScalarTower S T M]

/-- The difference of two derivations that agree on the base, as a derivation over the base. -/
def subDerivation (d₁ d₂ : Derivation R T M)
    (h : ∀ s : S, d₁ (algebraMap S T s) = d₂ (algebraMap S T s)) : Derivation S T M :=
  Derivation.mk'
    { toFun := fun t => d₁ t - d₂ t
      map_add' := fun t₁ t₂ => by
        show d₁ (t₁ + t₂) - d₂ (t₁ + t₂) = d₁ t₁ - d₂ t₁ + (d₁ t₂ - d₂ t₂)
        rw [map_add, map_add]
        abel
      map_smul' := fun s t => by
        show d₁ (s • t) - d₂ (s • t) = s • (d₁ t - d₂ t)
        rw [Algebra.smul_def s t, d₁.leibniz, d₂.leibniz, h s, smul_sub]
        simp only [algebraMap_smul]
        abel }
    (fun t₁ t₂ => by
      show d₁ (t₁ * t₂) - d₂ (t₁ * t₂) = t₁ • (d₁ t₂ - d₂ t₂) + t₂ • (d₁ t₁ - d₂ t₁)
      rw [d₁.leibniz, d₂.leibniz, smul_sub, smul_sub]
      abel)

omit [Algebra R S] [IsScalarTower R S T] [IsScalarTower R T M] in
/-- **A derivation is determined by its restriction to an unramified subalgebra.** -/
theorem derivation_eq_of_eqOn_base [Algebra.FormallyUnramified S T] (d₁ d₂ : Derivation R T M)
    (h : ∀ s : S, d₁ (algebraMap S T s) = d₂ (algebraMap S T s)) : d₁ = d₂ := by
  ext t
  have key : d₁ t - d₂ t = 0 :=
    derivation_apply_eq_zero_of_formallyUnramified (subDerivation d₁ d₂ h) t
  linear_combination (norm := abel) key

end Unique

/-! ## Extending a derivation along an étale extension -/

section EtaleLift

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- **The extension of a derivation along a formally étale algebra.**  The differentials of the
larger ring are those of the smaller one carried across, so a derivation of the smaller ring
determines a linear functional on the differentials of the larger one, and composing it with the
universal derivation gives back a derivation. -/
def etaleLift [Algebra.FormallyEtale S T] (d : Derivation R S S) : Derivation R T T :=
  ((KaehlerDifferential.isBaseChange_of_formallyEtale R S T).lift
      ((Algebra.linearMap S T).comp d.liftKaehlerDifferential)).compDer
    (KaehlerDifferential.D R T)

variable {R S T}

/-- **The extension of a derivation restricts to it.** -/
@[simp]
theorem etaleLift_algebraMap [Algebra.FormallyEtale S T] (d : Derivation R S S) (s : S) :
    etaleLift R S T d (algebraMap S T s) = algebraMap S T (d s) := by
  show (KaehlerDifferential.isBaseChange_of_formallyEtale R S T).lift
      ((Algebra.linearMap S T).comp d.liftKaehlerDifferential)
      (KaehlerDifferential.D R T (algebraMap S T s)) = _
  rw [← KaehlerDifferential.map_D R R S T s, IsBaseChange.lift_eq]
  simp

end EtaleLift

/-! ## Differentiating cannot leave an unramified ring of integral elements -/

section IntegralClosure

variable {R A F : Type*} [CommRing R] [CommRing A] [CommRing F] [Algebra A F] [Algebra R F]

/-- **Differentiating cannot leave an unramified ring of integral elements.**  A derivation that
carries a ring into the elements integral over it carries those integral elements into themselves,
provided they are unramified over the ring they are integral over. -/
theorem deriv_mem_integralClosure [Algebra.FormallyUnramified A ↥(integralClosure A F)]
    (d : Derivation R F F) (hA : ∀ a : A, d (algebraMap A F a) ∈ integralClosure A F)
    (b : ↥(integralClosure A F)) : d (b : F) ∈ integralClosure A F := by
  set N : Submodule ↥(integralClosure A F) F :=
    LinearMap.range (Algebra.linearMap ↥(integralClosure A F) F) with hN
  have hmemN : ∀ y : F, y ∈ N ↔ y ∈ integralClosure A F := by
    intro y
    constructor
    · rintro ⟨c, rfl⟩
      exact c.2
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hsmul : ∀ (c : ↥(integralClosure A F)) (y : F), N.mkQ ((c : F) * y) = c • N.mkQ y :=
    fun _ _ => rfl
  let hlin : ↥(integralClosure A F) →ₗ[A] (F ⧸ N) :=
    { toFun := fun c => N.mkQ (d (c : F))
      map_add' := fun c₁ c₂ => by
        show N.mkQ (d ((c₁ + c₂ : ↥(integralClosure A F)) : F))
          = N.mkQ (d (c₁ : F)) + N.mkQ (d (c₂ : F))
        rw [Subalgebra.coe_add, map_add, map_add]
      map_smul' := fun a c => by
        have hcoe : ((a • c : ↥(integralClosure A F)) : F) = algebraMap A F a * (c : F) := by
          rw [← Algebra.smul_def]
          rfl
        have hzero : N.mkQ ((c : F) * d (algebraMap A F a)) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN]
          exact mul_mem c.2 (hA a)
        show N.mkQ (d ((a • c : ↥(integralClosure A F)) : F)) = a • N.mkQ (d (c : F))
        rw [hcoe, d.leibniz, smul_eq_mul, smul_eq_mul, map_add, hzero, add_zero,
          ← Algebra.smul_def]
        rfl }
  have hleib : ∀ c₁ c₂ : ↥(integralClosure A F),
      hlin (c₁ * c₂) = c₁ • hlin c₂ + c₂ • hlin c₁ := by
    intro c₁ c₂
    show N.mkQ (d ((c₁ * c₂ : ↥(integralClosure A F)) : F))
      = c₁ • N.mkQ (d (c₂ : F)) + c₂ • N.mkQ (d (c₁ : F))
    rw [← hsmul, ← hsmul, ← map_add]
    congr 1
    rw [Subalgebra.coe_mul, d.leibniz, smul_eq_mul, smul_eq_mul]
  have hδ : N.mkQ (d (b : F)) = 0 :=
    derivation_apply_eq_zero_of_formallyUnramified (Derivation.mk' hlin hleib) b
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN] at hδ
  exact hδ

end IntegralClosure

end Rigidity.RET
