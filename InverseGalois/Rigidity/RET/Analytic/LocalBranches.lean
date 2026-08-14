/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootSection
import InverseGalois.Rigidity.RET.Analytic.RootFiber

/-!
# A complete system of local branches at a separable parameter

Over a parameter where the specialized equation has no repeated root, each of its roots extends to
a local branch of the family.  Taking the intersection of the neighbourhoods on which the branches
are defined, shrinking until the branches stay pairwise distinct, and shrinking once more to a disc
gives a connected neighbourhood carrying as many branches as the degree of the family.

On such a disc the branches account for *every* root: the specialized equation stays separable, so
it has exactly as many roots as its degree, and the branches already supply that many distinct
ones.  The fibre of the family over the disc is therefore the disjoint union of the graphs of the
branches, which is the local picture a sheet of the root cover is built from.

## Main results

* `Rigidity.RET.Analytic.card_rootFinset` — a separable specialization has as many distinct roots
  as the degree of the family.
* `Rigidity.RET.Analytic.exists_local_branches` — a connected neighbourhood of any separable
  parameter carrying a complete system of pairwise distinct continuous branches.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

/-- **A separable specialization has as many distinct roots as the degree of the family.** -/
theorem card_rootFinset {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) {z : ℂ}
    (hz : (spec P z).Separable) : (spec P z).roots.toFinset.card = P.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hz),
    ← (IsAlgClosed.splits (spec P z)).natDegree_eq_card_roots, natDegree_spec hP z]

theorem mem_rootFinset {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) {z w : ℂ} :
    w ∈ (spec P z).roots.toFinset ↔ (spec P z).eval w = 0 := by
  have hne : spec P z ≠ 0 := (spec_monic hP z).ne_zero
  simp [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot]

/-- **Every separable parameter has a connected neighbourhood carrying a complete system of
pairwise distinct continuous branches of the roots.** -/
theorem exists_local_branches {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) {S : Set ℂ}
    (hSc : IsOpen Sᶜ) (hsep : ∀ z ∉ S, (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ S) :
    ∃ (V : Set ℂ) (f : Fin P.natDegree → ℂ → ℂ),
      IsOpen V ∧ IsPreconnected V ∧ z₀ ∈ V ∧ V ⊆ Sᶜ ∧
        (∀ i, ContinuousOn (f i) V) ∧
        (∀ i, ∀ z ∈ V, (spec P z).eval (f i z) = 0) ∧
        (∀ z ∈ V, Function.Injective fun i => f i z) ∧
        (∀ z ∈ V, ∀ u : ℂ, (spec P z).eval u = 0 → ∃ i, f i z = u) := by
  classical
  have hsep₀ := hsep z₀ hz₀
  have hcard : (spec P z₀).roots.toFinset.card = P.natDegree := card_rootFinset hP hsep₀
  -- Enumerate the roots of the specialization at the base parameter.
  let e : Fin P.natDegree ≃ (spec P z₀).roots.toFinset :=
    ((spec P z₀).roots.toFinset.equivFin.trans (finCongr hcard)).symm
  have hwroot : ∀ i, (spec P z₀).eval ((e i : ℂ)) = 0 := fun i =>
    (mem_rootFinset hP).1 (e i).2
  have hwinj : Function.Injective fun i => ((e i : ℂ)) := fun i j hij =>
    e.injective (Subtype.ext hij)
  -- Each root extends to a local branch.
  have hsections : ∀ i : Fin P.natDegree, ∃ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V ∧ z₀ ∈ V ∧
      g z₀ = (e i : ℂ) ∧ ContinuousOn g V ∧ (∀ z ∈ V, (spec P z).eval (g z) = 0) ∧
      DifferentiableAt ℂ g z₀ := fun i =>
    exists_root_section P (hwroot i)
      (Polynomial.Separable.aeval_derivative_ne_zero hsep₀ (hwroot i))
  choose U f hUopen hz₀U hfz₀ hfcont hfroot _ using hsections
  -- Shrink to a common neighbourhood inside the separable part.
  set W : Set ℂ := (⋂ i, U i) ∩ Sᶜ with hWdef
  have hWopen : IsOpen W := (isOpen_iInter_of_finite hUopen).inter hSc
  have hz₀W : z₀ ∈ W := ⟨Set.mem_iInter.2 hz₀U, hz₀⟩
  have hWU : ∀ i, W ⊆ U i := fun i z hz => Set.mem_iInter.1 hz.1 i
  have hWS : W ⊆ Sᶜ := fun _ hz => hz.2
  -- Shrink again so that the branches stay pairwise distinct.
  set Ω : Fin P.natDegree × Fin P.natDegree → Set ℂ := fun p =>
    if p.1 = p.2 then Set.univ else W ∩ (fun z => f p.1 z - f p.2 z) ⁻¹' ({(0 : ℂ)}ᶜ) with hΩdef
  have hΩopen : ∀ p, IsOpen (Ω p) := by
    intro p
    simp only [hΩdef]
    split
    · exact isOpen_univ
    · exact ContinuousOn.isOpen_inter_preimage
        (((hfcont p.1).mono (hWU p.1)).sub ((hfcont p.2).mono (hWU p.2))) hWopen
        isOpen_compl_singleton
  have hz₀Ω : ∀ p, z₀ ∈ Ω p := by
    intro p
    simp only [hΩdef]
    split
    · exact Set.mem_univ _
    · rename_i hne
      refine ⟨hz₀W, ?_⟩
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero,
        hfz₀ p.1, hfz₀ p.2]
      exact fun h => hne (hwinj h)
  set W₂ : Set ℂ := W ∩ ⋂ p, Ω p with hW₂def
  have hW₂open : IsOpen W₂ := hWopen.inter (isOpen_iInter_of_finite hΩopen)
  have hz₀W₂ : z₀ ∈ W₂ := ⟨hz₀W, Set.mem_iInter.2 hz₀Ω⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW₂open z₀ hz₀W₂
  -- The disc of radius `r` is the neighbourhood we want.
  have hballW : Metric.ball z₀ r ⊆ W := fun z hz => (hball hz).1
  have hdistinct : ∀ z ∈ Metric.ball z₀ r, Function.Injective fun i => f i z := by
    intro z hz i j hij
    by_contra hne
    have hΩ := Set.mem_iInter.1 (hball hz).2 (i, j)
    simp only [hΩdef] at hΩ
    simp only [if_neg hne] at hΩ
    exact hΩ.2 (by simpa [sub_eq_zero] using hij)
  refine ⟨Metric.ball z₀ r, f, Metric.isOpen_ball, (convex_ball z₀ r).isPreconnected,
    Metric.mem_ball_self hr, fun z hz => hWS (hballW hz), fun i => (hfcont i).mono
      (fun z hz => hWU i (hballW hz)), fun i z hz => hfroot i z (hWU i (hballW hz)),
    hdistinct, ?_⟩
  -- The branches exhaust the fibre, by counting.
  intro z hz u hu
  have hzS : z ∉ S := hWS (hballW hz)
  have hRcard : (spec P z).roots.toFinset.card = P.natDegree := card_rootFinset hP (hsep z hzS)
  have hsub : Finset.image (fun i => f i z) Finset.univ ⊆ (spec P z).roots.toFinset := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact (mem_rootFinset hP).2 (hfroot i z (hWU i (hballW hz)))
  have hicard : (Finset.image (fun i => f i z) Finset.univ).card = P.natDegree := by
    rw [Finset.card_image_of_injective _ (hdistinct z hz), Finset.card_univ, Fintype.card_fin]
  have heq : Finset.image (fun i => f i z) Finset.univ = (spec P z).roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hicard, hRcard])
  have huR : u ∈ Finset.image (fun i => f i z) Finset.univ := by
    rw [heq]
    exact (mem_rootFinset hP).2 hu
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 huR
  exact ⟨i, hi⟩

end Rigidity.RET.Analytic

end
