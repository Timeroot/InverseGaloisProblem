/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverEquation
import InverseGalois.Rigidity.RET.Analytic.CoverRational

/-!
# The cover attached to a monodromy homomorphism makes its functions algebraic

The cover built from a monodromy homomorphism over a region of the plane meets the hypotheses of
the general theory: its projection is a local homeomorphism, the deck group acts over the region
with each fibre a single orbit, and — when the projection is onto — the region is exactly the image
of the total space.  So a holomorphic function on it which grows no faster than a power of the
distance to each puncture, and no faster than a power of `‖z‖` at infinity, satisfies a polynomial
equation over the polynomials of the base with monic leading coefficient.

## Main results

* `Rigidity.RET.MonodromyData.range_projC` — the image of the cover in the plane is the region.
* `Rigidity.RET.MonodromyData.exists_algebraic_of_growth` — a holomorphic function of moderate
  growth on the cover of a punctured plane is algebraic over the base.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.MonodromyData

variable {U : Set ℂ} {x₀ : ↥U} {H : Type*} [Group H] (D : MonodromyData x₀ H)

/-- **The image of the cover in the plane is the region**, when the projection is onto. -/
theorem range_projC (hsurj : Function.Surjective D.proj) : Set.range D.projC = U := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact (D.proj y).2
  · intro hz
    obtain ⟨y, hy⟩ := hsurj ⟨z, hz⟩
    exact ⟨y, by rw [projC, hy]⟩

/-- **A holomorphic function of moderate growth on the cover of a punctured plane is algebraic over
the base**: it satisfies an equation of degree the order of the deck group whose coefficients are
polynomials in the base coordinate and whose leading coefficient is a monic polynomial in it,
vanishing only at the punctures. -/
theorem exists_algebraic_of_growth [Fintype H] (hU : IsOpen U) (hcov : IsCoveringMap D.proj)
    (htr : ∀ y z : D.Total, D.proj y = D.proj z → ∃ h : H, D.deck h y = z)
    (hsurj : Function.Surjective D.proj) (S : Finset ℂ) (hUS : U = (↑S)ᶜ)
    {g : D.Total → ℂ} (hg : IsHolo D.projC g)
    (hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ, ∀ y : D.Total,
      D.projC y ∈ Metric.ball s ρ \ {s} → ‖g y‖ * ‖D.projC y - s‖ ^ N ≤ C)
    {A R₀ : ℝ} (hA : 0 ≤ A) {m : ℕ}
    (hinf : ∀ y : D.Total, R₀ ≤ ‖D.projC y‖ → ‖g y‖ ≤ A * ‖D.projC y‖ ^ m) :
    ∃ (a : ℕ → ℂ[X]) (d : ℂ[X]), d.Monic ∧ (∀ z ∉ S, d.eval z ≠ 0) ∧
      ∀ y : D.Total, d.eval (D.projC y) * g y ^ Fintype.card H
        + ∑ k ∈ Finset.range (Fintype.card H), (a k).eval (D.projC y) * g y ^ k = 0 := by
  letI : MulAction H D.Total := MulAction.compHom D.Total D.deckHom
  haveI : ContinuousConstSMul H D.Total := ⟨fun h => D.continuous_deck h⁻¹⟩
  refine Rigidity.RET.exists_algebraic_of_growth (H := H)
    (D.isLocalHomeomorph_projC hU hcov) (fun a y => rfl) (fun y y' hyy => ?_) hg S ?_ hpunct hA hinf
  · obtain ⟨h, hh⟩ := htr y y' (Subtype.coe_injective hyy)
    refine ⟨h⁻¹, ?_⟩
    show y' = D.deck h⁻¹⁻¹ y
    rw [inv_inv, hh]
  · rw [D.range_projC hsurj, hUS]

end Rigidity.RET.MonodromyData

end
