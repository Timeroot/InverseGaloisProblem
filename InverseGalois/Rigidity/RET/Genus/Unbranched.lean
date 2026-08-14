/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.SimplyConnected
import InverseGalois.Rigidity.RET.Genus.UnramifiedAbstract
import InverseGalois.Rigidity.RET.Genus.InftyChartRing

/-!
# The line has no unbranched covers

A finite Galois extension of the rational functions in one variable over an algebraically closed
field of characteristic zero, with no non-trivial inertia at any place of either chart of the line,
is trivial: this is the algebraic form of the simple connectedness of the projective line.

The two halves of the argument are already in place.  Trivial inertia at every place of a chart
means the ring of functions on the cover regular over that chart is unramified over the chart, in
the sense that its module of relative differentials vanishes; and a cover whose integral models over
both charts are unramified has degree one, by the comparison of dimensions carried out on the
filtration by pole order.  What remains is to check that the second chart is as good a base as the
first: the functions regular at the far end of the line form a polynomial ring in the inverse
coordinate, so they are a Dedekind domain whose fraction field is the whole field of rational
functions.

## Main results

* `Rigidity.RET.finrank_eq_one_of_inertia_trivial` — a Galois cover of the line with no non-trivial
  inertia at any place of either chart has degree one.
* `Rigidity.RET.subsingleton_autGroup_of_inertia_trivial` — such a cover has trivial deck group.
-/

open Polynomial Module

noncomputable section


namespace Rigidity.RET

section Unbranched

variable {k F : Type*} [Field k] [CharZero k] [IsAlgClosed k] [Field F] [Algebra k F]
  [Algebra k[X] F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  [IsGalois (RatFunc k) F]

/-- **A Galois cover of the line with no non-trivial inertia at any place of either chart has
degree one.**  Trivial inertia makes the integral model over each chart unramified, and a cover
unramified over both charts is trivial. -/
theorem finrank_eq_one_of_inertia_trivial
    (h₁ : ∀ Q : Ideal ↥(integralClosure k[X] F), Q.IsMaximal →
      ∀ σ : F ≃ₐ[RatFunc k] F, σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) Q → σ = 1)
    (h₂ : ∀ Q : Ideal ↥(integralClosure ↥(inftyChart k) F), Q.IsMaximal →
      ∀ σ : F ≃ₐ[RatFunc k] F, σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) Q → σ = 1) :
    finrank (RatFunc k) F = 1 := by
  haveI : Algebra.FormallyUnramified k[X] ↥(integralClosure k[X] F) :=
    formallyUnramified_integralClosure (A := k[X]) (K := RatFunc k) (F := F) k h₁
  haveI : Algebra.FormallyUnramified ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F) :=
    formallyUnramified_integralClosure (A := ↥(inftyChart k)) (K := RatFunc k) (F := F) k h₂
  exact finrank_eq_one_of_unramified

/-- **A Galois cover of the line with no non-trivial inertia at any place of either chart has
trivial deck group**: the cover is the line itself. -/
theorem subsingleton_autGroup_of_inertia_trivial
    (h₁ : ∀ Q : Ideal ↥(integralClosure k[X] F), Q.IsMaximal →
      ∀ σ : F ≃ₐ[RatFunc k] F, σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) Q → σ = 1)
    (h₂ : ∀ Q : Ideal ↥(integralClosure ↥(inftyChart k) F), Q.IsMaximal →
      ∀ σ : F ≃ₐ[RatFunc k] F, σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) Q → σ = 1) :
    Subsingleton (F ≃ₐ[RatFunc k] F) := by
  have hrank : finrank (RatFunc k) F = 1 := finrank_eq_one_of_inertia_trivial h₁ h₂
  have htop : (⊥ : Subalgebra (RatFunc k) F) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hrank
  refine ⟨fun σ τ => AlgEquiv.ext fun x => ?_⟩
  have hx : x ∈ (⊥ : Subalgebra (RatFunc k) F) := by rw [htop]; exact Algebra.mem_top
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hx
  rw [AlgEquiv.commutes, AlgEquiv.commutes]

end Unbranched

end Rigidity.RET
