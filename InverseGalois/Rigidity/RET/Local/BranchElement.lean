/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.DeckElement
import InverseGalois.Rigidity.RET.InertiaLift
import InverseGalois.Rigidity.RET.Local.BranchGeneration

/-!
# The name of a puncture loop is a distinguished inertia element

The analytic monodromy of a loop encircling a single branch point is named by a deck
transformation, through the system of names attached to a point of the fibre over the base point.
Here that name is identified algebraically: it generates the inertia group above the encircled
parameter.

The identification proceeds in three moves.  First, the loop is replaced by the boundary circle of
the disc it comes from: the two generate the same cyclic subgroup of the fundamental group of the
punctured disc, hence the same cyclic subgroup after being pushed to the base point and named, and
being a distinguished inertia element only depends on that cyclic subgroup.  Second, the circle is
read in the Kummer coordinate whose exponent is the order of its monodromy, which produces an
inertia element of at least that order acting as the monodromy on one point of the fibre over the
disc.  Third, transporting that relation along the connecting path turns it into a relation at the
global base point, where the characterization of the system of names identifies the name of the
loop with a conjugate of the inverse of the inertia element — and inertia generators are stable
under both operations.

## Main results

* `Rigidity.RET.LineCover.isInertiaGenAt_deckCycle` — the name of a loop encircling a single
  parameter generates the inertia group above that parameter.
-/

open Polynomial Filter Topology GeomAKLB Rigidity.RET.Analytic
open scoped Pointwise

noncomputable section

namespace Rigidity.RET

namespace LineCover

/-- **The name of a puncture loop is a distinguished inertia element.**  A loop encircling a single
parameter `s` and nothing else is named, through the system of names attached to a point of the
fibre over the base point, by a generator of the inertia group above `s`. -/
theorem isInertiaGenAt_deckCycle (L : LineCover) [Algebra k ℂ] {s : k} {α : L.M} (D : DeckData α)
    (hα : IsIntegral (Polynomial k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ} (hbadS : (D.badSetC : Set ℂ) ⊆ (S : Set ℂ))
    (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (e₀ : Analytic.puncturedProj (complexEquation α) S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
    {γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩}
    (hγ : IsPunctureLoop ((S : Set ℂ)ᶜ) (algebraMap k ℂ s) hz₀ γ) :
    L.IsInertiaGenAt s
      (((D.toIntegralDeck.toRationalDeck).mono hbadS).deckCycle (monic_complexEquation hα) hS hz₀
        (L.card_deck_eq_natDegree_complexEquation hα hgen) e₀ γ) := by
  classical
  obtain ⟨ρ, hincl, b, g, δ, hρ, hgtop, hγeq⟩ := hγ
  set cov := Analytic.isCoveringMap_puncturedProj (monic_complexEquation hα) hS with hcovdef
  set RD : Analytic.RationalDeck (complexEquation α) S L.deck :=
    (D.toIntegralDeck.toRationalDeck).mono hbadS with hRDdef
  set Φ := RD.deckCycle (monic_complexEquation hα) hS hz₀
    (L.card_deck_eq_natDegree_complexEquation hα hgen) e₀ with hΦdef
  -- the boundary circle of the disc, and the map pushing the disc to the base point
  set cdisc : FundamentalGroup ↥(puncturedDisc (algebraMap k ℂ s) ρ) b :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (discLoop (algebraMap k ℂ s) b))
    with hcdiscdef
  set Ψ : FundamentalGroup ↥(puncturedDisc (algebraMap k ℂ s) ρ) b →*
      FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩ :=
    (FundamentalGroup.transport (Path.Homotopic.Quotient.mk δ) :
        FundamentalGroup ↥((S : Set ℂ)ᶜ) (discIncl hincl b) ≃*
          FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩).toMonoidHom.comp
      (FundamentalGroup.map (discIncl hincl) b) with hΨdef
  have hγΨ : γ = Ψ g := hγeq
  -- the loop and the circle generate the same cyclic group, hence so do their names
  have hzΨ : Subgroup.zpowers γ = Subgroup.zpowers (Ψ cdisc) := by
    rw [hγΨ, ← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, hgtop, hcdiscdef,
      zpowers_discLoop_eq_top (algebraMap k ℂ s) hρ b]
  have hzΦ : Subgroup.zpowers (Φ γ) = Subgroup.zpowers (Φ (Ψ cdisc)) := by
    rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, hzΨ]
  refine (?_ : L.IsInertiaGenAt s (Φ (Ψ cdisc))).of_zpowers_eq hzΦ
  have hγc : IsPunctureLoop ((S : Set ℂ)ᶜ) (algebraMap k ℂ s) hz₀ (Ψ cdisc) :=
    ⟨ρ, hincl, b, cdisc, δ, hρ, hcdiscdef ▸ zpowers_discLoop_eq_top (algebraMap k ℂ s) hρ b, rfl⟩
  have hloc : Analytic.IsLocalMonodromy (monic_complexEquation hα) hS hz₀ (algebraMap k ℂ s)
      (Analytic.monodromyHom (monic_complexEquation hα) hS hz₀ (Ψ cdisc)) := ⟨Ψ cdisc, hγc, rfl⟩
  -- the local monodromy has the order of the monodromy of the circle
  have hord : orderOf (Analytic.monodromyHom (monic_complexEquation hα) hS hz₀ (Ψ cdisc))
      = orderOf (Analytic.discCycle (monic_complexEquation hα) hS hincl b) :=
    cov.orderOf_monodromyHom_transport (Path.Homotopic.Quotient.mk δ) _
  set n : ℕ := orderOf (Analytic.discCycle (monic_complexEquation hα) hS hincl b) with hndef
  haveI : Finite (Analytic.puncturedProj (complexEquation α) S ⁻¹' {subsetIncl hincl b}) :=
    (Analytic.finite_puncturedFiber (monic_complexEquation hα) (hincl b.2)).to_subtype
  have hn : 0 < n := orderOf_pos_iff.mpr (isOfFinOrder_of_finite _)
  -- read the disc in the Kummer coordinate of that exponent
  obtain ⟨ρ', hρ', hmap, w, hw⟩ := exists_kummerRegionMap_eq hρ hn b
  have hordeq : orderOf (Analytic.discCycle (monic_complexEquation hα) hS hincl
      (kummerRegionMap (algebraMap k ℂ s) n hmap w)) = n := by rw [hw]
  have hfix : Analytic.discCycle (monic_complexEquation hα) hS hincl
      (kummerRegionMap (algebraMap k ℂ s) n hmap w) ^ n = 1 := by
    have hp := pow_orderOf_eq_one (Analytic.discCycle (monic_complexEquation hα) hS hincl
      (kummerRegionMap (algebraMap k ℂ s) n hmap w))
    rwa [hordeq] at hp
  obtain ⟨τ, hinert, hdvd, hex⟩ :=
    L.exists_isInertiaAt_orderOf_discCycle_dvd D hα hgen hbadS hS hρ hρ' hincl hn hmap w hfix
  rw [hordeq] at hdvd
  have hτgen : L.IsInertiaGenAt s τ := by
    refine L.isInertiaGenAt_of_localMonodromy hα hgen hS hz₀ hloc hinert ?_
    rw [hord]
    exact Nat.le_of_dvd (orderOf_pos_iff.mpr (isOfFinOrder_of_finite τ)) hdvd
  -- move the fibre relation to the base point of the disc, then to the global base point
  have hex' : ∃ E, Analytic.discCycle (monic_complexEquation hα) hS hincl b E
      = RD.orbitFibre (hincl b.2) E τ := by
    rw [← hw]
    exact hex
  obtain ⟨E, hE⟩ := hex'
  have hmove : Analytic.monodromyHom (monic_complexEquation hα) hS hz₀ (Ψ cdisc)
        (cov.fibreEquiv (Path.Homotopic.Quotient.mk δ) E)
      = RD.orbitFibre hz₀ (cov.fibreEquiv (Path.Homotopic.Quotient.mk δ) E) τ := by
    rw [show Analytic.monodromyHom (monic_complexEquation hα) hS hz₀ (Ψ cdisc)
        = Equiv.permCongrHom (cov.fibreEquiv (Path.Homotopic.Quotient.mk δ))
            (Analytic.discCycle (monic_complexEquation hα) hS hincl b) from
      cov.monodromyHom_transport (Path.Homotopic.Quotient.mk δ) _]
    show cov.fibreEquiv (Path.Homotopic.Quotient.mk δ)
        (Analytic.discCycle (monic_complexEquation hα) hS hincl b
          ((cov.fibreEquiv (Path.Homotopic.Quotient.mk δ)).symm
            (cov.fibreEquiv (Path.Homotopic.Quotient.mk δ) E))) = _
    rw [Equiv.symm_apply_apply, hE]
    exact RD.fibreEquiv_orbitFibre (monic_complexEquation hα) hS hz₀ (hincl b.2)
      (Path.Homotopic.Quotient.mk δ) E τ
  obtain ⟨c, hc⟩ := RD.deckCycle_conj (monic_complexEquation hα) hS hz₀
    (L.card_deck_eq_natDegree_complexEquation hα hgen) e₀ (Ψ cdisc) hmove
  rw [hΦdef, hc]
  have hfin : L.IsInertiaGenAt s (c⁻¹ * τ⁻¹ * c⁻¹⁻¹) := hτgen.inv.conj c⁻¹
  rwa [inv_inv] at hfin

end LineCover

end Rigidity.RET

end
