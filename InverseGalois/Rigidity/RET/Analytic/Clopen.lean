/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.LocalBranches
import InverseGalois.Rigidity.RET.Analytic.Sheet

/-!
# A part of the root cover that is open and closed is cut out by an algebraic factor

Over the complement of a finite set the root variety of a monic family is a covering space, and a
subset of it that is open and closed selects, over each parameter, part of the fibre.  This file
turns such a selection into an algebraic object: the monic polynomial whose roots are the selected
ones is the specialization of a monic factor of the family.

The passage is local-to-global twice.  Locally the fibre is a disjoint union of continuous
branches; membership of a branch in a set that is open and closed is itself open and closed along
a disc, hence constant there, so the selection is a fixed sub-family of the branches and its
cardinality is locally constant.  The complement of a finite set in the plane is connected, so that
cardinality is a single number, and the selection is a locally continuous family of the shape the
factorization theorem consumes.

## Main results

* `Rigidity.RET.Analytic.selectedRoots` — the roots over a parameter that lie in a given part of
  the root variety.
* `Rigidity.RET.Analytic.exists_local_selection` — near any parameter outside the finite set the
  selection is given by finitely many continuous branches.
* `Rigidity.RET.Analytic.exists_monic_factor_of_clopen` — a part of the root cover that is open and
  closed is cut out by a monic factor of the family.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Set ℂ}

/-! ### The part of the root variety over the complement of a set -/

/-- The part of the root variety lying over the complement of a set. -/
def puncturedVariety (P : Polynomial (Polynomial ℂ)) (S : Set ℂ) : Set (rootVariety P) :=
  {q | (q : ℂ × ℂ).1 ∉ S}

theorem mem_puncturedVariety {q : rootVariety P} :
    q ∈ puncturedVariety P S ↔ (q : ℂ × ℂ).1 ∉ S := Iff.rfl

theorem isOpen_puncturedVariety (hSc : IsOpen (Sᶜ : Set ℂ)) : IsOpen (puncturedVariety P S) :=
  hSc.preimage (continuous_rootProj P)

theorem mem_image_val_iff {W : Set (rootVariety P)} {p : ℂ × ℂ} (hp : p ∈ rootVariety P) :
    p ∈ Subtype.val '' W ↔ (⟨p, hp⟩ : rootVariety P) ∈ W := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨⟨p, hp⟩, h, rfl⟩

/-! ### The selected part of a fibre -/

open scoped Classical in
/-- The roots of the specialization at a parameter that lie in a given part of the root
variety. -/
def selectedRoots (P : Polynomial (Polynomial ℂ)) (W : Set (rootVariety P)) (z : ℂ) : Finset ℂ :=
  (spec P z).roots.toFinset.filter fun w => ((z, w) : ℂ × ℂ) ∈ Subtype.val '' W

theorem mem_selectedRoots (hP : P.Monic) {W : Set (rootVariety P)} {z w : ℂ} :
    w ∈ selectedRoots P W z ↔
      ∃ h : ((z, w) : ℂ × ℂ) ∈ rootVariety P, (⟨(z, w), h⟩ : rootVariety P) ∈ W := by
  classical
  rw [selectedRoots, Finset.mem_filter, Multiset.mem_toFinset,
    Polynomial.mem_roots (spec_monic hP z).ne_zero]
  constructor
  · rintro ⟨hroot, himg⟩
    have hp : ((z, w) : ℂ × ℂ) ∈ rootVariety P := hroot
    exact ⟨hp, (mem_image_val_iff hp).1 himg⟩
  · rintro ⟨hp, hW⟩
    exact ⟨hp, (mem_image_val_iff hp).2 hW⟩

/-! ### The selection is locally given by continuous branches -/

/-- **Near any parameter outside the exceptional set the selection is a fixed sub-family of the
local branches.** -/
theorem exists_local_selection (hP : P.Monic) (hSc : IsOpen (Sᶜ : Set ℂ))
    (hsep : ∀ z ∉ S, (spec P z).Separable)
    {W : Set (rootVariety P)} (hWopen : IsOpen W)
    (hWcoopen : IsOpen (puncturedVariety P S \ W)) {z₀ : ℂ} (hz₀ : z₀ ∉ S) :
    ∃ (V : Set ℂ) (m : ℕ) (s : Fin m → ℂ → ℂ), IsOpen V ∧ z₀ ∈ V ∧ V ⊆ Sᶜ ∧
      (∀ i, ContinuousOn (s i) V) ∧
      (∀ i, ∀ z ∈ V, (spec P z).eval (s i z) = 0) ∧
      (∀ z ∈ V, Function.Injective fun i => s i z) ∧
      (∀ z ∈ V, selectedRoots P W z = Finset.image (fun i => s i z) Finset.univ) := by
  classical
  obtain ⟨U, hU, hUW⟩ := isOpen_induced_iff.1 hWopen
  obtain ⟨U', hU', hU'W⟩ := isOpen_induced_iff.1 hWcoopen
  obtain ⟨V, f, hVopen, hVconn, hz₀V, hVS, hfcont, hfroot, hfinj, hfsurj⟩ :=
    exists_local_branches hP hSc hsep hz₀
  have hpt : ∀ (i : Fin P.natDegree), ∀ z ∈ V, ((z, f i z) : ℂ × ℂ) ∈ rootVariety P :=
    fun i z hz => hfroot i z hz
  -- membership of a branch in `W` is constant along the disc
  have hconst : ∀ i : Fin P.natDegree, ∀ z ∈ V,
      (((z, f i z) : ℂ × ℂ) ∈ U ↔ ((z₀, f i z₀) : ℂ × ℂ) ∈ U) := by
    intro i
    have hmapcont : ContinuousOn (fun z : ℂ => ((z, f i z) : ℂ × ℂ)) V :=
      continuousOn_id.prodMk (hfcont i)
    have hAopen : IsOpen (V ∩ (fun z : ℂ => ((z, f i z) : ℂ × ℂ)) ⁻¹' U) :=
      hmapcont.isOpen_inter_preimage hVopen hU
    have hBopen : IsOpen (V ∩ (fun z : ℂ => ((z, f i z) : ℂ × ℂ)) ⁻¹' U') :=
      hmapcont.isOpen_inter_preimage hVopen hU'
    have hU'mem : ∀ z ∈ V, ((z, f i z) : ℂ × ℂ) ∉ U → ((z, f i z) : ℂ × ℂ) ∈ U' := by
      intro z hz hnot
      have hq : (⟨(z, f i z), hpt i z hz⟩ : rootVariety P) ∈ puncturedVariety P S \ W := by
        refine ⟨hVS hz, fun hmem => hnot ?_⟩
        rw [← hUW] at hmem
        exact hmem
      rw [← hU'W] at hq
      exact hq
    have hcover : V ⊆ (V ∩ (fun z : ℂ => ((z, f i z) : ℂ × ℂ)) ⁻¹' U) ∪
        (V ∩ (fun z : ℂ => ((z, f i z) : ℂ × ℂ)) ⁻¹' U') := by
      intro z hz
      by_cases h : ((z, f i z) : ℂ × ℂ) ∈ U
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, hU'mem z hz h⟩
    have hdisj : ∀ z ∈ V, ((z, f i z) : ℂ × ℂ) ∈ U → ((z, f i z) : ℂ × ℂ) ∈ U' → False := by
      intro z hz h1 h2
      have hw1 : (⟨(z, f i z), hpt i z hz⟩ : rootVariety P) ∈ W := by
        rw [← hUW]; exact h1
      have hw2 : (⟨(z, f i z), hpt i z hz⟩ : rootVariety P) ∈ puncturedVariety P S \ W := by
        rw [← hU'W]; exact h2
      exact hw2.2 hw1
    have key : ∀ z₁ ∈ V, ∀ z₂ ∈ V,
        ((z₁, f i z₁) : ℂ × ℂ) ∈ U → ((z₂, f i z₂) : ℂ × ℂ) ∈ U := by
      intro z₁ h1 z₂ h2 hin
      by_contra hout
      obtain ⟨y, hyV, hyA, hyB⟩ :=
        hVconn _ _ hAopen hBopen hcover ⟨z₁, h1, h1, hin⟩ ⟨z₂, h2, h2, hU'mem z₂ h2 hout⟩
      exact hdisj y hyV hyA.2 hyB.2
    exact fun z hz => ⟨fun h => key z hz z₀ hz₀V h, fun h => key z₀ hz₀V z hz h⟩
  -- the branches selected at the base parameter
  set J : Finset (Fin P.natDegree) :=
    Finset.univ.filter fun i => ((z₀, f i z₀) : ℂ × ℂ) ∈ U with hJdef
  set e : Fin J.card ≃ J := J.equivFin.symm
  refine ⟨V, J.card, fun i => f ((e i : Fin P.natDegree)), hVopen, hz₀V, hVS,
    fun i => hfcont _, fun i z hz => hfroot _ z hz, ?_, ?_⟩
  · intro z hz i j hij
    exact e.injective (Subtype.ext (hfinj z hz hij))
  · intro z hz
    have himg : Finset.image (fun i : Fin J.card => f ((e i : Fin P.natDegree)) z) Finset.univ
        = J.image fun j => f j z := by
      ext w
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(e i : Fin P.natDegree), (e i).2, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨e.symm ⟨j, hj⟩, by rw [Equiv.apply_symm_apply]⟩
    rw [himg]
    ext w
    rw [mem_selectedRoots hP, Finset.mem_image]
    constructor
    · rintro ⟨hp, hW⟩
      obtain ⟨i, hi⟩ := hfsurj z hz w hp
      refine ⟨i, ?_, hi⟩
      rw [hJdef, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hconst i z hz, hi]
      rw [← hUW] at hW
      exact hW
    · rintro ⟨i, hiJ, rfl⟩
      refine ⟨hpt i z hz, ?_⟩
      rw [← hUW]
      show ((z, f i z) : ℂ × ℂ) ∈ U
      rw [hconst i z hz]
      rw [hJdef, Finset.mem_filter] at hiJ
      exact hiJ.2

/-! ### The factor cut out by a part that is open and closed -/

/-- **A part of the root cover that is open and closed is cut out by a monic factor of the
family.** -/
theorem exists_monic_factor_of_clopen (hP : P.Monic) (hdeg : 0 < P.natDegree)
    (hS : S.Finite) (hsep : ∀ z ∉ S, (spec P z).Separable)
    {W : Set (rootVariety P)} (hWopen : IsOpen W)
    (hWcoopen : IsOpen (puncturedVariety P S \ W)) :
    ∃ (Q : Polynomial (Polynomial ℂ)) (m : ℕ), Q.Monic ∧ Q.natDegree = m ∧ Q ∣ P ∧
      (∀ z ∉ S, (selectedRoots P W z).card = m) ∧
      (∀ z ∉ S, spec Q z = ∏ w ∈ selectedRoots P W z, (X - C w)) := by
  classical
  have hSc : IsOpen (Sᶜ : Set ℂ) := hS.isClosed.isOpen_compl
  -- the fibre count of the selection is locally constant
  have hlc : ∀ z₀ ∉ S, ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ Sᶜ ∧
      ∀ z ∈ V, (selectedRoots P W z).card = (selectedRoots P W z₀).card := by
    intro z₀ hz₀
    obtain ⟨V, m, s, hVopen, hz₀V, hVS, -, -, hsinj, hsel⟩ :=
      exists_local_selection hP hSc hsep hWopen hWcoopen hz₀
    refine ⟨V, hVopen, hz₀V, hVS, fun z hz => ?_⟩
    rw [hsel z hz, hsel z₀ hz₀V,
      Finset.card_image_of_injective _ (hsinj z hz),
      Finset.card_image_of_injective _ (hsinj z₀ hz₀V)]
  -- the complement of a finite set is connected, so the count is a single number
  have hconn : IsConnected (Sᶜ : Set ℂ) := hS.countable.isConnected_compl_of_one_lt_rank (by simp)
  obtain ⟨z₁, hz₁⟩ := hconn.nonempty
  set m : ℕ := (selectedRoots P W z₁).card
  have hcard : ∀ z ∉ S, (selectedRoots P W z).card = m := by
    by_contra hbad
    push_neg at hbad
    obtain ⟨z₂, hz₂S, hz₂⟩ := hbad
    set A : Set ℂ := {z | z ∉ S ∧ (selectedRoots P W z).card = m}
    set B : Set ℂ := {z | z ∉ S ∧ (selectedRoots P W z).card ≠ m}
    have hAopen : IsOpen A := by
      rw [isOpen_iff_forall_mem_open]
      intro z hz
      obtain ⟨V, hVopen, hzV, hVS, hVcard⟩ := hlc z hz.1
      exact ⟨V, fun y hy => ⟨hVS hy, (hVcard y hy).trans hz.2⟩, hVopen, hzV⟩
    have hBopen : IsOpen B := by
      rw [isOpen_iff_forall_mem_open]
      intro z hz
      obtain ⟨V, hVopen, hzV, hVS, hVcard⟩ := hlc z hz.1
      exact ⟨V, fun y hy => ⟨hVS hy, by rw [hVcard y hy]; exact hz.2⟩, hVopen, hzV⟩
    have hcover : (Sᶜ : Set ℂ) ⊆ A ∪ B := by
      intro z hz
      by_cases h : (selectedRoots P W z).card = m
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    obtain ⟨y, -, hyA, hyB⟩ :=
      hconn.isPreconnected _ _ hAopen hBopen hcover ⟨z₁, hz₁, hz₁, rfl⟩ ⟨z₂, hz₂S, hz₂S, hz₂⟩
    exact hyB.2 hyA.2
  -- the selection divides the specialization
  have hFdvd : ∀ z ∉ S, (∏ w ∈ selectedRoots P W z, (X - C w)) ∣ spec P z := by
    intro z hz
    have hle : (selectedRoots P W z).val ≤ (spec P z).roots := by
      refine Finset.val_le_iff_val_subset.2 fun a ha => ?_
      have ha' : a ∈ selectedRoots P W z := ha
      rw [selectedRoots, Finset.mem_filter, Multiset.mem_toFinset] at ha'
      exact ha'.1
    have hdvd := (Multiset.prod_X_sub_C_dvd_iff_le_roots (spec_monic hP z).ne_zero
      (selectedRoots P W z).val).2 hle
    exact hdvd
  -- the local data required by the factorization theorem
  have hloc : ∀ z₀ ∉ S, ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ Sᶜ ∧
      ∃ s : Fin m → ℂ → ℂ, (∀ i, ContinuousOn (s i) V) ∧
        (∀ i, ∀ z ∈ V, (spec P z).eval (s i z) = 0) ∧
        (∀ z ∈ V, (∏ w ∈ selectedRoots P W z, (X - C w)) = ∏ i : Fin m, (X - C (s i z))) := by
    intro z₀ hz₀
    obtain ⟨V, m₀, s, hVopen, hz₀V, hVS, hscont, hsroot, hsinj, hsel⟩ :=
      exists_local_selection hP hSc hsep hWopen hWcoopen hz₀
    have hm : m₀ = m := by
      have h1 := hcard z₀ hz₀
      rw [hsel z₀ hz₀V, Finset.card_image_of_injective _ (hsinj z₀ hz₀V)] at h1
      simpa using h1
    refine ⟨V, hVopen, hz₀V, hVS, fun i => s (finCongr hm.symm i),
      fun i => hscont _, fun i z hz => hsroot _ z hz, fun z hz => ?_⟩
    rw [hsel z hz, Finset.prod_image (fun x _ y _ h => hsinj z hz h)]
    exact (Fintype.prod_equiv (finCongr hm.symm) (fun i => X - C (s (finCongr hm.symm i) z))
      (fun j => X - C (s j z)) fun _ => rfl).symm
  obtain ⟨Q, hQmonic, hQdeg, hQdvd, hQspec⟩ :=
    exists_monic_factor_of_local_sections hP hdeg hS hsep m
      (fun z => ∏ w ∈ selectedRoots P W z, (X - C w)) hFdvd hloc
  exact ⟨Q, m, hQmonic, hQdeg, hQdvd, hcard, hQspec⟩

end Rigidity.RET.Analytic

end
