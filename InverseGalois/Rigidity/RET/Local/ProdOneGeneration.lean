/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.BranchCycleReduce
import InverseGalois.Rigidity.RET.Local.InertiaGeneration
import InverseGalois.Rigidity.RET.Local.InfinityElement
import InverseGalois.Rigidity.RET.Pi1.Topological.PlaneSpider

/-!
# Inertia generators in the order of a spider, with the product relation

The distinguished inertia elements above a finite set of points generate the deck group; that
statement carries no information about the order in which the points are taken, and none about the
ordered product of the elements.  Reading the names of the loops of a *spider* instead — one loop
per puncture, followed by one further loop, the whole ordered list contracting in the punctured
plane — records both: the names come in the order of the punctures, and their ordered product,
extended by the name of the last loop, is the identity.

The last name is the one attached to the point at infinity.  It is the only entry of the list
which is not localized at a point of the line, and on a cover unramified at infinity it is
trivial: the last loop of the spider is supported at the point at infinity, and a loop supported
there names the identity.  The list may then be reordered and cut down to the prescribed tuple by
the Hurwitz moves of `RET/BranchCycleReduce.lean`, which is exactly the completeness direction of
the Riemann Existence Theorem for the line.

## Main results

* `Rigidity.RET.LineCover.exists_isInertiaGenAt_prodOne` — over a finite set of points containing
  the prescribed ones there is a list of distinguished inertia elements, one above each point and
  one further entry, generating the deck group, with ordered product the identity, and with the
  last entry trivial.
* `Rigidity.RET.LineCover.exists_isBranchCycleGenSystem_of_last_eq_one` — such a list whose last
  entry is trivial cuts down to a system of branch cycles over the prescribed points.
* `Rigidity.RET.geomRETCompleteness_of_injective` — every cover of the line branched only over a
  prescribed tuple of distinct points and infinity carries a system of branch cycles there.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

namespace LineCover

/-! ### The names of the loops of a spider -/

/-- **The distinguished inertia elements above a finite set of points, in the order of a spider,
have trivial ordered product once the name of the loop at infinity is appended.**

The set of points is the set of exceptional parameters of an equation of the cover, enlarged by
the prescribed points; each of them carries a distinguished inertia element above it, namely the
name of the loop of the spider winding around it.  The names generate the deck group, and the
ordered list of them, with the name of the last loop of the spider appended, has product the
identity.  That last name is the identity, because the last loop of the spider is supported at the
point at infinity, where the cover is unramified. -/
theorem exists_isInertiaGenAt_prodOne (L : LineCover) [Algebra k ℂ]
    (hinf : L.IsUnramifiedAtInfinity) {r : ℕ} (t : Fin r → k) :
    ∃ (m : ℕ) (v : Fin m → k) (g : Fin (m + 1) → L.deck),
      Function.Injective v ∧ Set.range t ⊆ Set.range v ∧
        (∀ i : Fin m, L.IsInertiaGenAt (v i) (g i.castSucc)) ∧
          (List.ofFn g).prod = 1 ∧ Subgroup.closure (Set.range g) = ⊤ ∧
            g (Fin.last m) = 1 := by
  classical
  obtain ⟨α, hα, hgen, ⟨D⟩⟩ := L.exists_deckData
  set S : Finset ℂ := D.badSetC ∪ Finset.image (fun i => algebraMap k ℂ (t i)) Finset.univ
    with hSdef
  have hbadS : (D.badSetC : Set ℂ) ⊆ (S : Set ℂ) := by
    intro z hz
    exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hz))
  have htS : ∀ i : Fin r, algebraMap k ℂ (t i) ∈ (S : Set ℂ) := by
    intro i
    exact Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable :=
    fun _ hz => D.separable_spec fun h => hz (hbadS h)
  obtain ⟨z₀, hz₀⟩ := Infinite.exists_notMem_finset S
  have hz₀' : z₀ ∉ (S : Set ℂ) := hz₀
  have hdeg : 0 < (complexEquation α).natDegree := natDegree_complexEquation_pos hα
  have hirr : Irreducible (complexEquation α) := irreducible_complexEquation hα
  have hcard : Nat.card L.deck = (complexEquation α).natDegree :=
    L.card_deck_eq_natDegree_complexEquation hα hgen
  have hpos : 0 < Nat.card (Analytic.puncturedProj (complexEquation α) S ⁻¹'
      {(⟨z₀, hz₀'⟩ : ↥((S : Set ℂ)ᶜ))}) := by
    rw [Analytic.card_puncturedFiber (monic_complexEquation hα) hS hz₀']
    exact hdeg
  obtain ⟨e₀⟩ := (Nat.card_pos_iff.mp hpos).1
  set RD : Analytic.RationalDeck (complexEquation α) S L.deck :=
    (D.toIntegralDeck.toRationalDeck).mono hbadS with hRDdef
  set Φ := RD.deckCycle (monic_complexEquation hα) hS hz₀' hcard e₀ with hΦdef
  -- the spider
  obtain ⟨m, pt, γ, hinj, hrange, hloop, hprod, htop, hinfγ⟩ :=
    exists_punctureLoops_prodOne_compl S.finite_toSet (z₀ := z₀) hz₀'
  -- every exceptional parameter comes from the constant field
  have hfromk : ∀ z ∈ (S : Set ℂ), ∃ s₀ : k, algebraMap k ℂ s₀ = z := by
    intro z hz
    rw [hSdef, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ] at hz
    rcases hz with hz | hz
    · have hroots : Multiset.card D.bad.roots = D.bad.natDegree :=
        (Polynomial.splits_iff_card_roots).1 (IsAlgClosed.splits D.bad)
      have hmap : D.bad.roots.map (algebraMap k ℂ) = (D.bad.map (algebraMap k ℂ)).roots :=
        Polynomial.roots_map_of_injective_of_card_eq_natDegree (algebraMap k ℂ).injective hroots
      have hz' : z ∈ (D.bad.map (algebraMap k ℂ)).roots := Multiset.mem_toFinset.1 hz
      rw [← hmap] at hz'
      obtain ⟨s₀, -, hs₀⟩ := Multiset.mem_map.1 hz'
      exact ⟨s₀, hs₀⟩
    · obtain ⟨i, rfl⟩ := hz
      exact ⟨t i, rfl⟩
  have hchoice : ∀ i : Fin m, ∃ s₀ : k, algebraMap k ℂ s₀ = pt i := fun i =>
    hfromk (pt i) (hrange ▸ Set.mem_range_self i)
  choose v hv using hchoice
  refine ⟨m, v, fun i => Φ (γ i), fun i j hij => hinj (by rw [← hv i, ← hv j, hij]),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the prescribed points are among the punctures
    rintro x ⟨i, rfl⟩
    have hmem : algebraMap k ℂ (t i) ∈ Set.range pt := by rw [hrange]; exact htS i
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, (algebraMap k ℂ).injective (by rw [hv j, hj])⟩
  · -- each name is a distinguished inertia element above its puncture
    intro i
    refine L.isInertiaGenAt_deckCycle D hα hgen hbadS hS hz₀' e₀ ?_
    rw [hv i]
    exact hloop i
  · -- the ordered product is trivial
    rw [show (List.ofFn fun i => Φ (γ i)) = (List.ofFn γ).map Φ by
      simp [List.map_ofFn, Function.comp_def]]
    rw [← map_list_prod, hprod, map_one]
  · -- the names generate
    rw [Set.range_comp' Φ γ, ← MonoidHom.map_closure, htop, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top]
    exact RD.surjective_deckCycle (monic_complexEquation hα) hdeg hirr hS hz₀' hcard e₀
  · -- the last name is that of a loop supported at the point at infinity
    exact L.deckCycle_eq_one_of_isSupportedAtInfinity D hα hgen hbadS hS hinf hz₀' e₀ hinfγ

/-! ### Cutting the list down to the prescribed points -/

/-- **A list of distinguished inertia elements with trivial ordered product, whose last entry is
trivial, is a system of branch cycles over any sub-tuple of its points containing the branch
locus.**  Discarding the trivial last entry leaves a system of branch cycles over the punctures,
which the Hurwitz moves reorder and cut down. -/
theorem exists_isBranchCycleGenSystem_of_last_eq_one (L : LineCover) {r m : ℕ} {t : Fin r → k}
    {v : Fin m → k} {g : Fin (m + 1) → L.deck} (hv : Function.Injective v)
    (ht : Function.Injective t) (hsub : Set.range t ⊆ Set.range v)
    (hunr : L.IsUnramifiedOutside (Set.range t))
    (hin : ∀ i : Fin m, L.IsInertiaGenAt (v i) (g i.castSucc))
    (hprod : (List.ofFn g).prod = 1) (htop : Subgroup.closure (Set.range g) = ⊤)
    (hlast : g (Fin.last m) = 1) :
    ∃ g' : Fin r → L.deck, L.IsBranchCycleGenSystem t g' := by
  refine L.exists_isBranchCycleGenSystem_of_subset hv ht hsub hunr ⟨g ∘ Fin.castSucc, hin, ?_, ?_⟩
  · refine eq_top_iff.2 ?_
    rw [← htop]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => rw [hlast]; exact one_mem _
    | cast j => exact Subgroup.subset_closure ⟨j, rfl⟩
  · have hp := hprod
    rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton, hlast,
      mul_one] at hp
    exact hp

end LineCover

/-! ### The completeness direction of the Riemann Existence Theorem -/

/-- **A cover of the line branched only over a prescribed tuple of distinct points and infinity
carries a system of branch cycles over that tuple.**

The names of the loops of a spider drawn around a finite set of points containing the prescribed
ones are distinguished inertia elements which generate the deck group and whose ordered product,
extended by the name of the loop at infinity, is trivial; unramifiedness at infinity makes that
last name trivial, and the Hurwitz moves then reorder the list and cut it down to the prescribed
points. -/
theorem geomRETCompleteness_of_injective {r : ℕ} {t : Fin r → k} (ht : Function.Injective t) :
    GeomRETCompleteness t := by
  letI : Algebra k ℂ := (IsAlgClosed.lift (R := ℚ) (S := k) (M := ℂ)).toRingHom.toAlgebra
  intro L hunr hinf
  obtain ⟨m, v, g, hv, hsub, hin, hprod, htop, hlast⟩ := L.exists_isInertiaGenAt_prodOne hinf t
  exact L.exists_isBranchCycleGenSystem_of_last_eq_one hv ht hsub hunr hin hprod htop hlast

end Rigidity.RET

end
