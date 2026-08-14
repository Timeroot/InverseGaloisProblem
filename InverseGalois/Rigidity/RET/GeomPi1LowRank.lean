/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.GeomPi1
import InverseGalois.Rigidity.RET.DeckGroups
import InverseGalois.Rigidity.RET.TranslateInfinity
import InverseGalois.Rigidity.RET.ExistenceCyclic

/-!
# The geometric fundamental group of the line with few punctures

A cover of the line unramified away from at most one point of the sphere is trivial, and one
unramified away from at most two points is cyclic.  Through the dictionary between the covers over
a set of points and the finite quotients of the geometric fundamental group, those two facts become
statements about the group itself: with at most one puncture it is trivial, and with at most two it
is abelian.

The bridge in both directions is that an automorphism of the cover field is determined by its
restrictions to the finite Galois subextensions, each of which is the field of a cover over the
same set of points: an identity that holds in every deck group over `S` therefore holds in the
geometric fundamental group.

## Main results

* `Rigidity.RET.subsingleton_of_isDeckGroupOver` — over at most one point only the trivial group
  occurs.
* `Rigidity.RET.eq_of_restrictNormalHom` — an automorphism of the cover field is determined by its
  restrictions to the finite Galois subextensions.
* `Rigidity.RET.subsingleton_geomPi1` — the line with at most one puncture is simply connected.
* `Rigidity.RET.commute_geomPi1` — the geometric fundamental group of the line with at most two
  punctures is abelian.
* `Rigidity.RET.coverField_eq_bot` — with at most one puncture the cover field is the line itself.
* `Rigidity.RET.exists_surjective_geomPi1_iff_isCyclic` — with exactly two punctures the finite
  quotients are exactly the finite cyclic groups.
* `Rigidity.RET.infinite_geomPi1` — with two punctures the fundamental group is infinite.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

/-! ### One puncture -/

/-- **Over at most one point only the trivial group occurs**, because the sphere with one puncture
is simply connected. -/
theorem subsingleton_of_isDeckGroupOver {S : Set k} (hS : S.Finite) (hcard : hS.toFinset.card ≤ 1)
    {G : Type} [Group G] [Finite G] (h : IsDeckGroupOver S G) : Subsingleton G := by
  obtain ⟨L, ⟨e⟩, hout, hinf⟩ := h
  obtain ⟨t, -, hsub⟩ := exists_range_superset_of_card_le hS hcard
  have hsub' : S ⊆ {t 0} := by simpa [Set.range_unique] using hsub
  haveI := LineCover.subsingleton_deck_of_unramifiedOutside_singleton L (t 0)
    (hout.mono hsub') hinf
  exact e.symm.injective.subsingleton

/-! ### Finite Galois subextensions of the cover field -/

/-- **Every element of the cover field lies in a finite Galois subextension of it**, namely in one
of the covers whose compositum the cover field is. -/
theorem exists_finiteDimensional_normal_mem {S : Set k} (x : (coverField S : Type)) :
    ∃ A : IntermediateField (RatFunc k) (coverField S : Type),
      FiniteDimensional (RatFunc k) (A : Type) ∧ Normal (RatFunc k) (A : Type) ∧ x ∈ A := by
  obtain ⟨E, hE, hxE⟩ := mem_coverField_iff.mp x.2
  have hle : E ≤ coverField S := hE.le_coverField
  haveI := hE.finiteDimensional
  haveI := hE.normal
  refine ⟨IntermediateField.restrict hle, ?_, ?_, (IntermediateField.mem_restrict hle x).mpr hxE⟩
  · exact LinearEquiv.finiteDimensional (IntermediateField.restrict_algEquiv hle).toLinearEquiv
  · exact Normal.of_algEquiv (IntermediateField.restrict_algEquiv hle)

/-- **The automorphism group of a finite Galois subextension of the cover field occurs over `S`.**
-/
theorem isDeckGroupOver_aut {S : Set k} (A : IntermediateField (RatFunc k) (coverField S : Type))
    [FiniteDimensional (RatFunc k) (A : Type)] [Normal (RatFunc k) (A : Type)] :
    IsDeckGroupOver S ((A : Type) ≃ₐ[RatFunc k] (A : Type)) :=
  isDeckGroupOver_of_mulEquiv_subextension A (MulEquiv.refl _)

/-- **An automorphism of the cover field is determined by its restrictions to the finite Galois
subextensions**, since every element of the cover field lies in one of them. -/
theorem eq_of_restrictNormalHom {S : Set k} {σ τ : geomPi1 S}
    (h : ∀ A : IntermediateField (RatFunc k) (coverField S : Type),
      ∀ [FiniteDimensional (RatFunc k) (A : Type)] [Normal (RatFunc k) (A : Type)],
      AlgEquiv.restrictNormalHom A σ = AlgEquiv.restrictNormalHom A τ) : σ = τ := by
  refine AlgEquiv.ext fun x => ?_
  obtain ⟨A, hfin, hnor, hxA⟩ := exists_finiteDimensional_normal_mem x
  haveI := hfin
  haveI := hnor
  have hσ := AlgEquiv.restrictNormalHom_apply A σ ⟨x, hxA⟩
  have hτ := AlgEquiv.restrictNormalHom_apply A τ ⟨x, hxA⟩
  rw [h A] at hσ
  simpa using hσ.symm.trans hτ

/-! ### The fundamental group with few punctures -/

/-- **The line with at most one puncture is simply connected**: its geometric fundamental group is
trivial, because each of its finite Galois subextensions has trivial automorphism group. -/
theorem subsingleton_geomPi1 {S : Set k} (hS : S.Finite) (hcard : hS.toFinset.card ≤ 1) :
    Subsingleton (geomPi1 S) := by
  refine ⟨fun σ τ => eq_of_restrictNormalHom fun A _ _ => ?_⟩
  haveI := subsingleton_of_isDeckGroupOver hS hcard (isDeckGroupOver_aut A)
  exact Subsingleton.elim _ _

/-- **The geometric fundamental group of the line with at most two punctures is abelian**: the
automorphism group of each finite Galois subextension is cyclic, and an automorphism is determined
by its restrictions. -/
theorem commute_geomPi1 {S : Set k} (hS : S.Finite) (hcard : hS.toFinset.card ≤ 2)
    (σ τ : geomPi1 S) : Commute σ τ := by
  show σ * τ = τ * σ
  refine eq_of_restrictNormalHom fun A _ _ => ?_
  haveI : IsCyclic ((A : Type) ≃ₐ[RatFunc k] (A : Type)) :=
    isCyclic_of_isDeckGroupOver hS hcard (isDeckGroupOver_aut A)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (A : Type) ≃ₐ[RatFunc k] (A : Type))
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (AlgEquiv.restrictNormalHom A σ))
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (AlgEquiv.restrictNormalHom A τ))
  rw [map_mul, map_mul, ← hm, ← hn]
  exact (Commute.refl g).zpow_zpow m n

/-! ### The cover field with at most one puncture -/

/-- A cover field over at most one point is the line itself, being a Galois extension with trivial
automorphism group. -/
theorem IsCoverFieldOver.eq_bot {S : Set k} (hS : S.Finite) (hcard : hS.toFinset.card ≤ 1)
    {E : IntermediateField (RatFunc k) LineCover.closure} (h : IsCoverFieldOver S E) : E = ⊥ := by
  haveI := h.finiteDimensional
  haveI := h.isGalois
  haveI : Subsingleton ((E : Type) ≃ₐ[RatFunc k] (E : Type)) := by
    obtain ⟨L, ⟨e⟩, hout, hinf⟩ := h
    exact subsingleton_of_isDeckGroupOver hS hcard ⟨L, ⟨AlgEquiv.autCongr e⟩, hout, hinf⟩
  rw [← IntermediateField.finrank_eq_one_iff, ← IsGalois.card_aut_eq_finrank]
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- **The cover field over at most one point is the line itself**, since each of the covers it is
built from is trivial. -/
theorem coverField_eq_bot {S : Set k} (hS : S.Finite) (hcard : hS.toFinset.card ≤ 1) :
    coverField S = ⊥ := by
  refine le_bot_iff.mp ?_
  simp only [coverField]
  exact iSup_le fun E => le_of_eq (IsCoverFieldOver.eq_bot hS hcard E.2)

/-! ### Two punctures -/

/-- **Every finite cyclic group occurs over any two points**: it is the deck group of the Kummer
cover whose branch cycles at those two points are a generator and its inverse. -/
theorem isDeckGroupOver_of_isCyclic {S : Set k} (hS : S.Finite) (hcard : 2 ≤ hS.toFinset.card)
    {G : Type} [Group G] [Finite G] [hcyc : IsCyclic G] : IsDeckGroupOver S G := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < hS.toFinset.card)
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  set t : Fin 2 → k := ![a, b] with htdef
  have htinj : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t]
  have hprod : (List.ofFn ![g, g⁻¹]).prod = 1 := by simp [List.ofFn_succ]
  have htop : Subgroup.closure (Set.range ![g, g⁻¹]) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hgmem : g ∈ Subgroup.closure (Set.range ![g, g⁻¹]) := Subgroup.subset_closure ⟨0, rfl⟩
    obtain ⟨m, rfl⟩ := hg x
    exact zpow_mem hgmem m
  obtain ⟨L, e, hout, hinf, -⟩ := exists_cover_of_isCyclic t htinj ![g, g⁻¹] hprod htop
  refine IsDeckGroupOver.mono ?_ ⟨L, ⟨e⟩, hout, hinf⟩
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · simpa [t] using hS.mem_toFinset.mp ha
  · simpa [t] using hS.mem_toFinset.mp hb

/-- **Over exactly two points exactly the finite cyclic groups occur.** -/
theorem isDeckGroupOver_iff_isCyclic {S : Set k} (hS : S.Finite) (hcard : hS.toFinset.card = 2)
    {G : Type} [Group G] [Finite G] : IsDeckGroupOver S G ↔ IsCyclic G :=
  ⟨isCyclic_of_isDeckGroupOver hS hcard.le, fun _ => isDeckGroupOver_of_isCyclic hS hcard.ge⟩

/-! ### Finite quotients -/

/-- **A finite quotient of the geometric fundamental group of the line with at most two punctures
is cyclic.** -/
theorem isCyclic_of_surjective_geomPi1 {S : Set k} (hS : S.Finite) (hcard : hS.toFinset.card ≤ 2)
    {G : Type} [Group G] [Finite G] (φ : geomPi1 S →* G) (hφ : Function.Surjective φ)
    (hopen : IsOpen (φ.ker : Set (geomPi1 S))) : IsCyclic G :=
  isCyclic_of_isDeckGroupOver hS hcard (isDeckGroupOver_of_surjective φ hφ hopen)

/-- **A finite quotient of the geometric fundamental group of the line with at most one puncture is
trivial.** -/
theorem subsingleton_of_surjective_geomPi1 {S : Set k} (hS : S.Finite)
    (hcard : hS.toFinset.card ≤ 1) {G : Type} [Group G] [Finite G] (φ : geomPi1 S →* G)
    (hφ : Function.Surjective φ) (hopen : IsOpen (φ.ker : Set (geomPi1 S))) : Subsingleton G :=
  subsingleton_of_isDeckGroupOver hS hcard (isDeckGroupOver_of_surjective φ hφ hopen)

/-- **The finite quotients of the fundamental group of the twice-punctured line are exactly the
finite cyclic groups.** -/
theorem exists_surjective_geomPi1_iff_isCyclic {S : Set k} (hS : S.Finite)
    (hcard : hS.toFinset.card = 2) (G : Type) [Group G] [Finite G] :
    (∃ φ : geomPi1 S →* G, Function.Surjective φ ∧ IsOpen (φ.ker : Set (geomPi1 S))) ↔
      IsCyclic G :=
  (isDeckGroupOver_iff_exists_surjective G).symm.trans (isDeckGroupOver_iff_isCyclic hS hcard)

/-- **The fundamental group of the line with two punctures is infinite**, having a quotient of
every finite cyclic order. -/
theorem infinite_geomPi1 {S : Set k} (hS : S.Finite) (hcard : 2 ≤ hS.toFinset.card) :
    Infinite (geomPi1 S) := by
  rw [← not_finite_iff_infinite]
  intro hfin
  haveI := hfin
  set n : ℕ := Nat.card (geomPi1 S) + 1 with hn
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨φ, hφ, -⟩ := exists_surjective_of_isDeckGroupOver
    (isDeckGroupOver_of_isCyclic (G := Multiplicative (ZMod n)) hS hcard)
  have hle := Nat.card_le_card_of_surjective φ hφ
  rw [(Nat.card_congr (Multiplicative.ofAdd (α := ZMod n)).symm).trans (Nat.card_zmod n)] at hle
  omega

end Rigidity.RET
