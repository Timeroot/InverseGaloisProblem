/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.NamedFamilyPower
import InverseGalois.CFT.Units.StablePlaces

/-!
# A family of units named at finitely many places and confined everywhere else

The bookkeeping of the two-place construction carries more than the prescription it answers: a
finite set of places over which everything happens, a pair of places for each coordinate, and the
whole list of clauses relating them.  What a prescription over a level asks for is only the units,
together with four statements about them: that they are trivial at a prescribed Galois stable set of
places, that they carry the named classes at the named places, that they die at every proper
conjugate of a named place, and that everywhere else, where one of them fails to have order
divisible by the exponent, the place is either a conjugate of a named one or is completely split in
the auxiliary field with a single coordinate surviving it.

Reading those four statements off the bookkeeping is a matter of choosing the two auxiliary sets of
places the construction is run over.  The distinguished part is taken to be the whole orbit of the
named places, so that a place where the units ramify and which is not one of the pairs is a
conjugate of a named place; and the set the prescription is made over is enlarged, by a set stable
under the Galois group carrying the ideal classes, to contain the prescribed set, the places above
the exponent and the places ramified in the auxiliary field.  Enlarging it is free: the prescription
made over the larger set is trivial away from the named places, which is exactly the triviality
asked for at the prescribed set.

## Main results

* `InverseGalois.CFT.exists_units_named_prescribed`: **a naming orthogonal to the `S`-units which
  become a power in the auxiliary field is carried by a family of units trivial on a prescribed set
  of places, dying at the proper conjugates of the named places, and ramified only over the named
  places or at places completely split in the auxiliary field with a single coordinate surviving.**

## Tags

number field, place, local class, prescription, S-unit, completely split, Poitou-Tate duality
-/

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

section NamedUnits

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  [IsScalarTower k K A] [Finite Gal(K/k)] {Ω : IntermediateField k A} [NumberField ↥Ω]
  [Normal k ↥Ω] [Algebra K ↥Ω] [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω]
  [FiniteDimensional k ↥Ω] [IsGalois k ↥Ω] {p : ℕ} [NeZero p]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

variable (Ω) in
/-- **A naming has a family of units carrying it, trivial on a prescribed set of places disjoint
from the named ones, dying at every conjugate of a named place which is not itself named, and
ramified only over the named places or at places completely split in the auxiliary field with a
single coordinate surviving.**

The two auxiliary sets of the two-place construction are chosen for it.  The distinguished part,
outside which the units of the family are unramified away from their own pair of places, is the
whole orbit of the named places; so a place carrying one of the units is a conjugate of a named
place or one of a pair, and at a place of a pair the bookkeeping already says that the other
coordinates die there, that the whole orbit of the place dies there, and that the place is
completely split.  The set the prescription is made over is any Galois stable set carrying the ideal
classes and containing the orbit, the prescribed set, the places above the exponent and the places
ramified in the auxiliary field; over it the prescription is the naming at the named places and
trivial everywhere else, which is what the prescribed set is asking for. -/
theorem exists_units_named_prescribed (hp : p.Prime) (hodd : 2 < p) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {Tp Tz Tram : Finset (HeightOneSpectrum (𝓞 K))} (hdisj : ∀ v ∈ Tp, v ∉ Tz)
    (hram : ∀ v ∉ Tram, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1)
    {cl : (w : ↥Tp) → ℕ → localClasses (w : HeightOneSpectrum (𝓞 K)) p}
    (hcln : ∀ (w : ↥Tp) (t : ℕ),
      FinitePlace.mk (w : HeightOneSpectrum (𝓞 K)) ((p : ℕ) : K) ≠ 1 → cl w t = 1)
    {D : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hDgal : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
      Subgroup.zpowers (D (σ • v)) = Subgroup.zpowers (localClassesGalEquiv σ v p (D v)))
    (hDcl : ∀ (w : ↥Tp) (t : ℕ),
      cl w t ∈ Subgroup.zpowers (D (w : HeightOneSpectrum (𝓞 K))))
    (horth : ∀ Tn : Finset (HeightOneSpectrum (𝓞 K)), Tp ⊆ Tn → ∀ (t : ℕ)
      (u : ↥(sUnits K (Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))))),
      (∀ w : InfinitePlace K, infClassHom w p ((u : Kˣ)) = 1) →
      (∃ y : (↥Ω)ˣ, Units.map (algebraMap K ↥Ω : K →* ↥Ω) ((u : Kˣ)) = y ^ p) →
      localSymbolPiPairing hres hζ (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))
        (sUnitClassHom (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K)) p u)
        (fun y => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 K))) = 1) (d : ℕ) :
    ∃ z : ℕ → Kˣ,
      (∀ q < d, ∀ v ∈ Tz, localClassHom v p (z q) = 1) ∧
      (∀ q < d, ∀ w : ↥Tp, localClassHom (w : HeightOneSpectrum (𝓞 K)) p (z q) = cl w q) ∧
      (∀ q < d, ∀ (σ : Gal(K/k)) (w : ↥Tp), σ • (w : HeightOneSpectrum (𝓞 K)) ∉ Tp →
        localClassHom (σ • (w : HeightOneSpectrum (𝓞 K))) p (z q) = 1) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), (∃ q < d, ¬ (p : ℤ) ∣ placeValue v (z q)) →
        (∃ (σ : Gal(K/k)) (w : ↥Tp), v = σ • (w : HeightOneSpectrum (𝓞 K))) ∨
          ((∃ W : HeightOneSpectrum (𝓞 ↥Ω),
              primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/k) W = ⊥) ∧
            (∃ q₀ < d, ∀ q < d, q ≠ q₀ → localClassHom v p (z q) = 1) ∧
            ∀ σ : Gal(K/k), σ ≠ 1 → ∀ q < d, localClassHom (σ • v) p (z q) = 1) := by
  classical
  letI : Fintype Gal(K/k) := Fintype.ofFinite _
  obtain ⟨Tr, hmemTr⟩ : ∃ Tr : Finset (HeightOneSpectrum (𝓞 K)), ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ Tr ↔ ∃ (σ : Gal(K/k)) (w : ↥Tp), σ • (w : HeightOneSpectrum (𝓞 K)) = v := by
    refine ⟨Finset.image (fun q : Gal(K/k) × ↥Tp => q.1 • (q.2 : HeightOneSpectrum (𝓞 K)))
      (Finset.univ : Finset (Gal(K/k) × ↥Tp)), fun v => ?_⟩
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨σ, w⟩, -, hq⟩
      exact ⟨σ, w, hq⟩
    · rintro ⟨σ, w, hq⟩
      exact ⟨(σ, w), Finset.mem_univ _, hq⟩
  have hTpTr : Tp ⊆ Tr := fun v hv => (hmemTr v).2 ⟨1, ⟨v, hv⟩, one_smul _ _⟩
  have hTrst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tr → σ • v ∈ Tr := by
    intro σ v hv
    obtain ⟨τ, w, hw⟩ := (hmemTr v).1 hv
    exact (hmemTr _).2 ⟨σ * τ, w, by rw [mul_smul, hw]⟩
  obtain ⟨Ts, hTs0, hTsst, hpTs, hrepr⟩ := exists_stable_ord_places k K (ℓ := p) hp.ne_zero
    (((Tr ∪ Tz ∪ Tram : Finset (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 K))))
    (Finset.finite_toSet _)
  have hTrTs : Tr ⊆ Ts := fun v hv =>
    hTs0 (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_left _ hv)))
  have hTzTs : Tz ⊆ Ts := fun v hv =>
    hTs0 (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_right _ hv)))
  have hTramTs : Tram ⊆ Ts := fun v hv => hTs0 (Finset.mem_coe.2 (Finset.mem_union_right _ hv))
  obtain ⟨Tn, hTsTn, -, S, Q, R, z, hfam⟩ :=
    exists_isTwoPlaceFamily_named_of_orthogonal Ω hp hodd hζ hres hTpTr hTrTs hTrst hTsst hpTs
      hrepr hcln hDgal hDcl
      (fun Tn hTn => horth Tn fun v hv => hTn (hTrTs (hTpTr hv)))
      (fun v hv => hram v fun hc => hv (hTramTs hc)) d
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro q hq v hv
    rw [hfam.prescribed q hq v (hTsTn (hTzTs hv)),
      spreadClasses_of_notMem (fun hc => hdisj v hc hv) q]
  · intro q hq w
    rw [hfam.prescribed q hq (w : HeightOneSpectrum (𝓞 K)) (hTsTn (hTrTs (hTpTr w.2))),
      spreadClasses_of_mem w.2 q]
  · intro q hq σ w hnm
    have hmem : σ • (w : HeightOneSpectrum (𝓞 K)) ∈ Tn := hTsTn (hTrTs (hTrst σ _ (hTpTr w.2)))
    rw [hfam.prescribed q hq _ hmem, spreadClasses_of_notMem hnm q]
  · rintro v ⟨q, hqd, hq⟩
    by_cases hvTr : v ∈ Tr
    · obtain ⟨σ, w, hw⟩ := (hmemTr v).1 hvTr
      exact Or.inl ⟨σ, w, hw.symm⟩
    refine Or.inr ?_
    have hQR : v = Q q ∨ v = R q := by
      by_contra hcon
      push_neg at hcon
      exact hq (hfam.unram q hqd v hvTr hcon.1 hcon.2)
    rcases hQR with rfl | rfl
    · refine ⟨?_, ⟨q, hqd, ?_⟩, ?_⟩
      · have hS : Q q ∈ S := by
          have h1 := hfam.memQ q hqd 1
          rwa [one_smul] at h1
        exact hfam.split _ hS (hfam.notMemQ q hqd)
      · intro q' hq' hne
        have h1 := hfam.crossQ q' hq' q hqd hne 1
        rwa [one_smul] at h1
      · intro σ hσ q' hq'
        by_cases hqq : q' = q
        · subst hqq
          exact hfam.conjQ q' hq' σ hσ
        · exact hfam.crossQ q' hq' q hqd hqq σ
    · refine ⟨?_, ⟨q, hqd, ?_⟩, ?_⟩
      · have hS : R q ∈ S := by
          have h1 := hfam.memR q hqd 1
          rwa [one_smul] at h1
        exact hfam.split _ hS (hfam.notMemR q hqd)
      · intro q' hq' hne
        have h1 := hfam.crossR q' hq' q hqd hne 1
        rwa [one_smul] at h1
      · intro σ hσ q' hq'
        by_cases hqq : q' = q
        · subst hqq
          exact hfam.conjR q' hq' σ hσ
        · exact hfam.crossR q' hq' q hqd hqq σ

end NamedUnits

end InverseGalois.CFT
