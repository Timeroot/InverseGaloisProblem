/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.GeometricBaseChange
import InverseGalois.Rigidity.RET.Local.BranchElement
import InverseGalois.Rigidity.RET.Unramified

/-!
# Inertia generators generate the deck group

A cover of the line is described analytically by the equation of a primitive element, read with
complex coefficients.  Loops around the exceptional parameters of that equation carry names in the
deck group, and those names generate it; each name is a distinguished inertia element above the
parameter it winds around.  A parameter outside the branch locus contributes the trivial name, so
the names attached to the branch points already generate the deck group.

Setting this up needs a primitive element that is integral over the coordinate ring of the line:
a primitive element exists because the extension is finite and separable, and scaling it by a
suitable polynomial makes it integral without changing the field it generates.

## Main results

* `Rigidity.RET.adjoin_simple_smul_eq` — scaling a generator by a nonzero constant does not change
  the field it generates.
* `Rigidity.RET.exists_primitive_integral` — a finite separable extension has a primitive element
  integral over any subring with the base field as fraction field.
* `Rigidity.RET.LineCover.exists_deckData` — a cover of the line carries a primitive element
  together with a group of root formulas for it.
* `Rigidity.RET.LineCover.exists_isInertiaGenAt_generating` — over any finite set of points
  containing the branch locus there is a tuple of distinguished inertia elements, one above each
  point, generating the deck group.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

/-! ### A primitive element integral over the coordinate ring -/

/-- Scaling a generator by a nonzero constant does not change the field it generates. -/
theorem adjoin_simple_smul_eq {F M : Type*} [Field F] [Field M] [Algebra F M] {c : F}
    (hc : c ≠ 0) (α : M) :
    IntermediateField.adjoin F {c • α} = IntermediateField.adjoin F {α} := by
  have hmem : ∀ (d : F) (β : M) (E : IntermediateField F M), β ∈ E → d • β ∈ E := by
    intro d β E hβ
    rw [Algebra.smul_def]
    exact mul_mem (E.algebraMap_mem d) hβ
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact hmem c α _ (IntermediateField.mem_adjoin_simple_self F α)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have hα : α = c⁻¹ • (c • α) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    have h2 := hmem c⁻¹ (c • α) (IntermediateField.adjoin F {c • α})
      (IntermediateField.mem_adjoin_simple_self F (c • α))
    rwa [← hα] at h2

/-- **A finite separable extension has a primitive element integral over the base ring.**  Any
primitive element becomes integral after being scaled by a suitable element of the ring, and
scaling does not change the field it generates. -/
theorem exists_primitive_integral (R F M : Type*) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field M] [Algebra F M] [Algebra R M] [IsScalarTower R F M]
    [FiniteDimensional F M] [Algebra.IsSeparable F M] :
    ∃ α : M, IsIntegral R α ∧ IntermediateField.adjoin F {α} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F M
  have halg : IsAlgebraic R α :=
    (IsFractionRing.isAlgebraic_iff R F M).2 ((Algebra.IsAlgebraic.of_finite F M).isAlgebraic α)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  refine ⟨y • α, hyint, ?_⟩
  have hcy : (y : R) • α = (algebraMap R F y) • α := by rw [algebraMap_smul]
  have hcne : algebraMap R F y ≠ 0 := fun h => hy0 (IsFractionRing.to_map_eq_zero_iff.1 h)
  rw [hcy, adjoin_simple_smul_eq hcne α]
  exact hα

namespace LineCover

/-- **A cover of the line carries a primitive element together with a group of root formulas for
it.** -/
theorem exists_deckData (L : LineCover) :
    ∃ α : L.M, ∃ _ : IsIntegral (Polynomial k) α,
      IntermediateField.adjoin (RatFunc k) {α} = ⊤ ∧ Nonempty (DeckData α) := by
  obtain ⟨α, hα, hgen⟩ := exists_primitive_integral (Polynomial k) (RatFunc k) L.M
  refine ⟨α, hα, hgen, Rigidity.RET.exists_deckData hα ?_⟩
  exact exists_aeval_eq_of_adjoin_eq_top hα.tower_top hgen

/-! ### The names of the localized loops -/

/-- **The distinguished inertia elements above a finite set containing the branch locus generate
the deck group.**  Each point of the set is given an inertia generator above it, and together they
generate; the points which are not branch points contribute the identity. -/
theorem exists_isInertiaGenAt_generating (L : LineCover) [Algebra k ℂ] {r : ℕ} (t : Fin r → k)
    (hunr : L.IsUnramifiedOutside (Set.range t)) :
    ∃ g : Fin r → L.deck, (∀ i, L.IsInertiaGenAt (t i) (g i)) ∧
      Subgroup.closure (Set.range g) = ⊤ := by
  classical
  obtain ⟨α, hα, hgen, ⟨D⟩⟩ := L.exists_deckData
  set S : Finset ℂ := D.badSetC with hSdef
  have hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable :=
    fun _ hz => D.separable_spec hz
  obtain ⟨z₀, hz₀⟩ := Infinite.exists_notMem_finset S
  have hz₀' : z₀ ∉ (S : Set ℂ) := hz₀
  have hdeg : 0 < (complexEquation α).natDegree := natDegree_complexEquation_pos hα
  have hirr : Irreducible (complexEquation α) := irreducible_complexEquation hα
  have hcard : Nat.card L.deck = (complexEquation α).natDegree :=
    L.card_deck_eq_natDegree_complexEquation hα hgen
  -- a point of the fibre over the base point
  have hpos : 0 < Nat.card (Analytic.puncturedProj (complexEquation α) S ⁻¹'
      {(⟨z₀, hz₀'⟩ : ↥((S : Set ℂ)ᶜ))}) := by
    rw [Analytic.card_puncturedFiber (monic_complexEquation hα) hS hz₀']
    exact hdeg
  obtain ⟨e₀⟩ := (Nat.card_pos_iff.mp hpos).1
  have hbadS : (D.badSetC : Set ℂ) ⊆ (S : Set ℂ) := subset_rfl
  set RD : Analytic.RationalDeck (complexEquation α) S L.deck :=
    (D.toIntegralDeck.toRationalDeck).mono hbadS with hRDdef
  obtain ⟨γ, hγ, htop⟩ :=
    RD.exists_localizedNames (monic_complexEquation hα) hdeg hirr hS hz₀' hcard e₀
  set Φ : ℂ → L.deck :=
    fun s => RD.deckCycle (monic_complexEquation hα) hS hz₀' hcard e₀ (γ s) with hΦdef
  -- every exceptional parameter comes from the constant field
  have hfromk : ∀ s ∈ (S : Set ℂ), ∃ s₀ : k, algebraMap k ℂ s₀ = s := by
    intro s hs
    have hroots : Multiset.card D.bad.roots = D.bad.natDegree :=
      (Polynomial.splits_iff_card_roots).1 (IsAlgClosed.splits D.bad)
    have hmap : D.bad.roots.map (algebraMap k ℂ) = (D.bad.map (algebraMap k ℂ)).roots :=
      Polynomial.roots_map_of_injective_of_card_eq_natDegree (algebraMap k ℂ).injective hroots
    have hs' : s ∈ (D.bad.map (algebraMap k ℂ)).roots := by
      have := hs
      rw [hSdef] at this
      exact Multiset.mem_toFinset.1 this
    rw [← hmap] at hs'
    obtain ⟨s₀, _, hs₀⟩ := Multiset.mem_map.1 hs'
    exact ⟨s₀, hs₀⟩
  -- the name of the loop around a parameter is a distinguished inertia element there
  have key : ∀ s₀ : k, algebraMap k ℂ s₀ ∈ (S : Set ℂ) →
      L.IsInertiaGenAt s₀ (Φ (algebraMap k ℂ s₀)) :=
    fun s₀ hs => L.isInertiaGenAt_deckCycle D hα hgen hbadS hS hz₀' e₀ (hγ _ hs)
  -- outside the branch locus that element is trivial
  have htriv : ∀ s₀ : k, algebraMap k ℂ s₀ ∈ (S : Set ℂ) → s₀ ∉ Set.range t →
      Φ (algebraMap k ℂ s₀) = 1 := by
    intro s₀ hs hnr
    obtain ⟨Q, hmax, hover, hI⟩ := key s₀ hs
    exact hunr s₀ hnr _ ⟨Q, hmax, hover, by rw [hI]; exact Subgroup.mem_zpowers _⟩
  refine ⟨fun i => if h : algebraMap k ℂ (t i) ∈ (S : Set ℂ) then Φ (algebraMap k ℂ (t i))
    else Classical.choose (L.exists_isInertiaGenAt (t i)), fun i => ?_, ?_⟩
  · by_cases h : algebraMap k ℂ (t i) ∈ (S : Set ℂ)
    · simp only [dif_pos h]
      exact key (t i) h
    · simp only [dif_neg h]
      exact Classical.choose_spec (L.exists_isInertiaGenAt (t i))
  · rw [eq_top_iff, ← htop]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨s, hs, rfl⟩
    obtain ⟨s₀, rfl⟩ := hfromk s hs
    by_cases hmem : s₀ ∈ Set.range t
    · obtain ⟨i, rfl⟩ := hmem
      refine Subgroup.subset_closure ⟨i, ?_⟩
      simp only [dif_pos hs]
    · show Φ (algebraMap k ℂ s₀) ∈ Subgroup.closure _
      rw [htriv s₀ hs hmem]
      exact one_mem _

end LineCover

end Rigidity.RET

end
