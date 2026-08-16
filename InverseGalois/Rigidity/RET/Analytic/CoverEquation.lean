/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverSymm
import InverseGalois.Rigidity.RET.Pi1.Topological.CoverDeck

/-!
# The equation satisfied by a function on the cover attached to a monodromy homomorphism

The cover built from a monodromy homomorphism projects to a region of the plane by a covering map,
and the deck group acts on it over that region, simply transitively on every fibre.  Composing the
projection with the inclusion of the region into the plane gives a local homeomorphism to `ℂ`, so
the total space is a space over the plane in the sense of `RET/Analytic/CoverHolo.lean`, and the
deck group is a group of symmetries of it over the base with each fibre one orbit.

Everything the general theory says therefore applies to it: a holomorphic function on the cover
satisfies a monic equation of degree the order of the deck group whose coefficients are analytic
functions on the region.  This is the shape of the passage from a cover to an equation; what a
proof of the Riemann Existence Theorem still needs beyond it is a holomorphic function whose values
separate the sheets, and the meromorphy of the coefficients at the punctures and at infinity, which
turns *analytic* coefficients into *rational* ones.

## Main results

* `Rigidity.RET.MonodromyData.isLocalHomeomorph_projC` — the cover lies locally homeomorphically
  over the plane.
* `Rigidity.RET.MonodromyData.isHolo_projC` — the projection is a holomorphic function on the
  cover.
* `Rigidity.RET.MonodromyData.exists_monic_analytic_of_isHolo` — a holomorphic function on the
  cover satisfies a monic equation of degree the order of the deck group, with coefficients
  analytic on the region.
-/

noncomputable section

namespace Rigidity.RET.MonodromyData

variable {X : Set ℂ} {x₀ : ↥X} {H : Type*} [Group H] (D : MonodromyData x₀ H)

/-- **The projection of the cover to the plane**: the projection to the region, followed by the
inclusion of the region. -/
def projC (y : D.Total) : ℂ := (D.proj y : ℂ)

@[simp] theorem projC_deck (h : H) (y : D.Total) : D.projC (D.deck h y) = D.projC y := rfl

/-- **The cover lies locally homeomorphically over the plane** when the region is open and the
projection is a covering map. -/
theorem isLocalHomeomorph_projC (hX : IsOpen X) (hcov : IsCoveringMap D.proj) :
    IsLocalHomeomorph D.projC :=
  (hX.isOpenEmbedding_subtypeVal.isLocalHomeomorph).comp hcov.isLocalHomeomorph

/-- **The projection is a holomorphic function on the cover** — it is the local coordinate. -/
theorem isHolo_projC (hX : IsOpen X) (hcov : IsCoveringMap D.proj) : IsHolo D.projC D.projC :=
  isHoloAt_self (D.isLocalHomeomorph_projC hX hcov)

/-- **A holomorphic function on the cover is algebraic over the region.**

If the deck group is finite and acts transitively on the fibres — that is, if the cover is the
Galois cover with that group — then a holomorphic function on the total space satisfies a monic
equation of degree the order of the group whose coefficients are analytic on the region. -/
theorem exists_monic_analytic_of_isHolo [Fintype H] (hX : IsOpen X)
    (hcov : IsCoveringMap D.proj)
    (htrans : ∀ y z : D.Total, D.proj y = D.proj z → ∃ h : H, D.deck h y = z)
    {g : D.Total → ℂ} (hg : IsHolo D.projC g) :
    ∃ c : ℕ → ℂ → ℂ, (∀ k y, AnalyticAt ℂ (c k) (D.projC y)) ∧
      ∀ y, g y ^ Fintype.card H
        + ∑ k ∈ Finset.range (Fintype.card H), c k (D.projC y) * g y ^ k = 0 := by
  letI : MulAction H D.Total := MulAction.compHom D.Total D.deckHom
  haveI : ContinuousConstSMul H D.Total := ⟨fun h => D.continuous_deck h⁻¹⟩
  refine Rigidity.RET.exists_monic_analytic_of_isHolo (H := H)
    (D.isLocalHomeomorph_projC hX hcov) (fun a y => rfl) (fun y y' hyy => ?_) hg
  obtain ⟨h, hh⟩ := htrans y y' (Subtype.coe_injective hyy)
  refine ⟨h⁻¹, ?_⟩
  show y' = D.deck h⁻¹⁻¹ y
  rw [inv_inv, hh]

end Rigidity.RET.MonodromyData

end
