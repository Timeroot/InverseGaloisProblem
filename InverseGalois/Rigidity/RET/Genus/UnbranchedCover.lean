/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Unbranched
import InverseGalois.Rigidity.RET.Genus.UnramifiedModel
import InverseGalois.Rigidity.RET.Unramified

/-!
# An unbranched cover of the line has trivial deck group

The covers of the line over `ℚ̄` carried by `LineCover` are addressed through the integral model
over the first chart, and their ramification is recorded by the inertia groups at the places of
that model over the points of the line.  The far end of the line is addressed through the second
chart, whose functions are the polynomials in the inverse coordinate.  A cover with no non-trivial
inertia at any place of either model is trivial: its function field is the field of rational
functions and its deck group is trivial.

## Main definitions

* `Rigidity.RET.LineCover.IsUnramifiedOnInftyChart` — no non-trivial inertia at any place of the
  integral model over the second chart.

## Main results

* `Rigidity.RET.LineCover.finrank_eq_one_of_unbranched` — a cover unbranched over both charts has
  degree one.
* `Rigidity.RET.LineCover.subsingleton_deck_of_unbranched` — such a cover has trivial deck group.
-/

open Polynomial Module

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

namespace LineCover

/-- A cover of the line is **unbranched over the second chart** if no non-trivial deck
transformation lies in the inertia group of a place of its integral model over that chart. -/
def IsUnramifiedOnInftyChart (L : LineCover) : Prop :=
  ∀ Q : Ideal ↥(integralClosure ↥(inftyChart k) L.M), Q.IsMaximal →
    ∀ σ : L.deck, σ ∈ Ideal.inertia L.deck Q → σ = 1

/-- The constants act on the function field of a cover, through the rational functions. -/
local instance instAlgebraConst (L : LineCover) : Algebra k L.M :=
  ((algebraMap (RatFunc k) L.M).comp (algebraMap k (RatFunc k))).toAlgebra

local instance instTowerConstRatFunc (L : LineCover) : IsScalarTower k (RatFunc k) L.M :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance instTowerConstPoly (L : LineCover) : IsScalarTower k (Polynomial k) L.M :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) L.M]
    show algebraMap (RatFunc k) L.M (algebraMap k (RatFunc k) a) = _
    rw [IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]

/-- Unbranchedness over the first chart, read at the places of the integral model: every point of
the line is cut out by a linear polynomial, so a place of the model lies over a point. -/
theorem inertia_eq_one_of_isUnramifiedOutside_empty {L : LineCover}
    (h : L.IsUnramifiedOutside ∅) (Q : Ideal (Bring L.M)) (hQ : Q.IsMaximal) (σ : L.deck)
    (hσ : σ ∈ geomInertia L.M Q) : σ = 1 := by
  haveI := hQ
  haveI : (Q.under (Polynomial k)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  obtain ⟨t, ht⟩ := exists_eq_span_X_sub_C (Q.under (Polynomial k))
  haveI : Q.LiesOver (placeP t) := ⟨ht.symm⟩
  exact h t (Set.notMem_empty t) σ ⟨Q, hQ, inferInstance, hσ⟩

/-- **A cover of the line unbranched over both charts has degree one.** -/
theorem finrank_eq_one_of_unbranched (L : LineCover) (h₁ : L.IsUnramifiedOutside ∅)
    (h₂ : L.IsUnramifiedOnInftyChart) : finrank (RatFunc k) L.M = 1 :=
  finrank_eq_one_of_inertia_trivial
    (fun Q hQ σ hσ => inertia_eq_one_of_isUnramifiedOutside_empty h₁ Q hQ σ hσ)
    (fun Q hQ σ hσ => h₂ Q hQ σ hσ)

/-- **A cover of the line unbranched over both charts has trivial deck group.** -/
theorem subsingleton_deck_of_unbranched (L : LineCover) (h₁ : L.IsUnramifiedOutside ∅)
    (h₂ : L.IsUnramifiedOnInftyChart) : Subsingleton L.deck :=
  subsingleton_autGroup_of_inertia_trivial
    (fun Q hQ σ hσ => inertia_eq_one_of_isUnramifiedOutside_empty h₁ Q hQ σ hσ)
    (fun Q hQ σ hσ => h₂ Q hQ σ hσ)

end LineCover

end Rigidity.RET
