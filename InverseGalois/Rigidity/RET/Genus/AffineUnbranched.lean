/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Unbranched

/-!
# A cover unbranched over the affine line, tame at the far end, is trivial

The comparison of dimensions that trivializes a cover of the line unbranched everywhere asks less
of the far end of the line than unbranchedness.  It asks that differentiating a function regular
at the far end produce a function with at most a simple pole there — equivalently, that the
*logarithmic* derivation `x · d/dx`, which vanishes to first order at the far end, preserve the
functions regular there.  That is what happens at a branch point of a cover in characteristic
zero, where ramification is automatically tame: the logarithmic derivation along a branch divisor
lifts to the cover.

Everything else in the argument is untouched: the functions regular over both charts are the
constants, the derivative of a function regular over the affine line is again regular there when
the cover is unbranched over the affine line, and the kernel of differentiation is the constants.

## Main results

* `Rigidity.RET.finrank_eq_one_of_inertia_trivial_affine` — a Galois cover of the line with no
  non-trivial inertia at any place of the first chart, along which the logarithmic derivation
  preserves the functions regular at the far end, has degree one.
* `Rigidity.RET.subsingleton_autGroup_of_inertia_trivial_affine` — such a cover has trivial deck
  group.
-/

open Polynomial Module

noncomputable section


namespace Rigidity.RET

section AffineUnbranched

variable {k F : Type*} [Field k] [CharZero k] [IsAlgClosed k] [Field F] [Algebra k F]
  [Algebra k[X] F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  [IsGalois (RatFunc k) F]

/-- **A Galois cover of the line with no non-trivial inertia at any place of the first chart,
along which the logarithmic derivation preserves the functions regular at the far end, has degree
one.** -/
theorem finrank_eq_one_of_inertia_trivial_affine
    (h₁ : ∀ Q : Ideal ↥(integralClosure k[X] F), Q.IsMaximal →
      ∀ σ : F ≃ₐ[RatFunc k] F, σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) Q → σ = 1)
    (hlog : ∀ y ∈ inftyIntegers k F, coord k F * lineDeriv k F y ∈ inftyIntegers k F) :
    finrank (RatFunc k) F = 1 := by
  haveI : Algebra.FormallyUnramified k[X] ↥(integralClosure k[X] F) :=
    formallyUnramified_integralClosure (A := k[X]) (K := RatFunc k) (F := F) k h₁
  exact finrank_eq_one_of_logDeriv_mem_inftyIntegers hlog

/-- **Such a cover has trivial deck group**: the cover is the line itself. -/
theorem subsingleton_autGroup_of_inertia_trivial_affine
    (h₁ : ∀ Q : Ideal ↥(integralClosure k[X] F), Q.IsMaximal →
      ∀ σ : F ≃ₐ[RatFunc k] F, σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) Q → σ = 1)
    (hlog : ∀ y ∈ inftyIntegers k F, coord k F * lineDeriv k F y ∈ inftyIntegers k F) :
    Subsingleton (F ≃ₐ[RatFunc k] F) := by
  have hrank : finrank (RatFunc k) F = 1 := finrank_eq_one_of_inertia_trivial_affine h₁ hlog
  have htop : (⊥ : Subalgebra (RatFunc k) F) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hrank
  refine ⟨fun σ τ => AlgEquiv.ext fun x => ?_⟩
  have hx : x ∈ (⊥ : Subalgebra (RatFunc k) F) := by rw [htop]; exact Algebra.mem_top
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hx
  rw [AlgEquiv.commutes, AlgEquiv.commutes]

end AffineUnbranched

end Rigidity.RET
