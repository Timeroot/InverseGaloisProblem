/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.NamedFamily
import InverseGalois.CFT.PoitouTate.PartPrescribed

/-!
# A two-place family for a naming, with the prescription left free at the split places

The two-place construction asks for a global `S`-unit whose classes meet the prescription at a
distinguished part of the places of `S` and are trivial at the rest, and it repairs the classes at
the rest, provided those places are completely split in the auxiliary field.  Asking the `S`-unit
to meet a naming at the named places therefore leaves the classes at the split places free, and the
reciprocity obstruction to the existence of such an `S`-unit weakens accordingly: only the `S`-units
whose classes are already trivial at the split places have to be tested against the naming.

That is the shape in which the obstruction can be made to vanish outright.  If the split places
detect the `S`-units, in the sense that an `S`-unit trivial at all of them and at every infinite
place is trivial at every named place too, then every factor of the product of symbols has a
trivial argument and the naming is realised with nothing left to check.

## Main results

* `InverseGalois.CFT.exists_isTwoPlaceFamily_named_split_of_sUnits`: a naming realised at the
  distinguished places by a family of `S`-units has a two-place family, the remaining places of `S`
  being completely split.
* `InverseGalois.CFT.exists_isTwoPlaceFamily_named_detecting`: **a naming at places detected by the
  split places of `S` has a two-place family**, with no orthogonality left to check.

## Tags

number field, place, local class, prescription, S-unit, completely split, Poitou-Tate duality
-/

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

section NamedSplit

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  [IsScalarTower k K A] {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω]
  {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

variable (Ω) in
/-- **A naming realised at the distinguished places by a family of `S`-units has a two-place
family**, as soon as the remaining places of `S` are completely split in the auxiliary field.  The
classes of the `S`-units at those remaining places are left free, the construction repairing them
by the complete splitting. -/
theorem exists_isTwoPlaceFamily_named_split_of_sUnits (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {Tp Tr Ts Tn : Finset (HeightOneSpectrum (𝓞 K))} (hTp : Tp ⊆ Tr) (hTr : Tr ⊆ Ts)
    (hTs : Ts ⊆ Tn)
    (hTrst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tr → σ • v ∈ Tr)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {cl : (w : ↥Tp) → ℕ → localClasses (w : HeightOneSpectrum (𝓞 K)) p}
    (hclfree : ∀ σ : Gal(K/k), σ ≠ 1 → ∀ w ∈ Tp, σ • w ∉ Tp)
    (hcln : ∀ (w : ↥Tp) (t : ℕ),
      FinitePlace.mk (w : HeightOneSpectrum (𝓞 K)) ((p : ℕ) : K) ≠ 1 → cl w t = 1)
    {D : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hDgal : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
      Subgroup.zpowers (D (σ • v)) = Subgroup.zpowers (localClassesGalEquiv σ v p (D v)))
    (hDcl : ∀ (w : ↥Tp) (t : ℕ),
      cl w t ∈ Subgroup.zpowers (D (w : HeightOneSpectrum (𝓞 K))))
    {g : ℕ → Kˣ} (hg : ∀ t : ℕ, g t ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hgcl : ∀ (t : ℕ) (w : ↥Tp),
      cl w t = localClassHom (w : HeightOneSpectrum (𝓞 K)) p (g t))
    (hg1 : ∀ t : ℕ, ∀ w ∈ Ts, w ∉ Tp → localClassHom w p (g t) = 1)
    (hsplit : ∀ v ∈ Tn, v ∉ Ts → ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/K) W = ⊥)
    (hram : ∀ v ∉ Tn, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1) (d : ℕ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (Q R : ℕ → HeightOneSpectrum (𝓞 K)) (z : ℕ → Kˣ),
      IsTwoPlaceFamily Ω p Tr Tn (spreadClasses Tp cl) d S Q R z := by
  refine exists_isTwoPlaceFamily_zpowers (Ω := Ω) hp hodd hζ hres hTr hTs
    hTrst hTnst hpTn hrepr ?_ ?_ hg ?_ ?_ ?_ hDgal ?_ hsplit hram d
  · intro t v _ hvTr
    rw [spreadClasses_of_notMem (fun hc => hvTr (hTp hc)) t]
    exact Subgroup.one_mem _
  · intro t σ hσ v hv
    by_cases hvp : v ∈ Tp
    · exact Or.inl (spreadClasses_of_notMem (hclfree σ hσ v hvp) t)
    · exact Or.inr (spreadClasses_of_notMem hvp t)
  · intro t v hv
    by_cases hvp : v ∈ Tp
    · rw [spreadClasses_of_mem hvp t]
      exact hgcl t ⟨v, hvp⟩
    · rw [spreadClasses_of_notMem hvp t, hg1 t v hv hvp]
  · intro t v _ hvs
    exact spreadClasses_of_notMem (fun hc => hvs (hTr (hTp hc))) t
  · intro t v _ hvp
    by_cases hvT : v ∈ Tp
    · rw [spreadClasses_of_mem hvT t]
      exact hcln ⟨v, hvT⟩ t hvp
    · exact spreadClasses_of_notMem hvT t
  · intro t v _
    by_cases hvT : v ∈ Tp
    · rw [spreadClasses_of_mem hvT t]
      exact hDcl ⟨v, hvT⟩ t
    · rw [spreadClasses_of_notMem hvT t]
      exact Subgroup.one_mem _

variable (Ω) in
/-- **A naming at places detected by the split places of `S` has a two-place family**, with no
orthogonality left to check.

An `S`-unit whose classes are trivial at the split places pairs trivially with the naming at every
place: at a named place because its own class there is trivial, by the detection, and away from the
named places because the naming is.  So the naming is the local behaviour of an `S`-unit at the
distinguished places, one coordinate at a time, and the two-place construction turns that family of
`S`-units into the family the coordinates are read from. -/
theorem exists_isTwoPlaceFamily_named_detecting (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {Tp Tr Ts Tn : Finset (HeightOneSpectrum (𝓞 K))} (hTp : Tp ⊆ Tr) (hTr : Tr ⊆ Ts)
    (hTs : Ts ⊆ Tn)
    (hTrst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tr → σ • v ∈ Tr)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {cl : (w : ↥Tp) → ℕ → localClasses (w : HeightOneSpectrum (𝓞 K)) p}
    (hclfree : ∀ σ : Gal(K/k), σ ≠ 1 → ∀ w ∈ Tp, σ • w ∉ Tp)
    (hcln : ∀ (w : ↥Tp) (t : ℕ),
      FinitePlace.mk (w : HeightOneSpectrum (𝓞 K)) ((p : ℕ) : K) ≠ 1 → cl w t = 1)
    {D : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hDgal : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
      Subgroup.zpowers (D (σ • v)) = Subgroup.zpowers (localClassesGalEquiv σ v p (D v)))
    (hDcl : ∀ (w : ↥Tp) (t : ℕ),
      cl w t ∈ Subgroup.zpowers (D (w : HeightOneSpectrum (𝓞 K))))
    (hdet : ∀ u : Kˣ, u ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))) →
      (∀ w : InfinitePlace K, infClassHom w p u = 1) →
      (∀ v ∈ Tn, v ∉ Ts → localClassHom v p u = 1) →
      ∀ v ∈ Tp, localClassHom v p u = 1)
    (hsplit : ∀ v ∈ Tn, v ∉ Ts → ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/K) W = ⊥)
    (hram : ∀ v ∉ Tn, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1) (d : ℕ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (Q R : ℕ → HeightOneSpectrum (𝓞 K)) (z : ℕ → Kˣ),
      IsTwoPlaceFamily Ω p Tr Tn (spreadClasses Tp cl) d S Q R z := by
  classical
  have hrange : Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))
      = (Tn : Set (HeightOneSpectrum (𝓞 K))) := by
    rw [Subtype.range_coe_subtype]
    exact Finset.setOf_mem
  have hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 →
      v ∈ Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K)) := by
    intro v hv
    rw [hrange]
    exact hpTn v hv
  have hrepr' : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K)),
        Rigidity.RET.ord K v (a : K) = m v := by
    intro m hm
    obtain ⟨a, ha⟩ := hrepr m hm
    exact ⟨a, fun v hv => ha v (by rwa [hrange] at hv)⟩
  have hex : ∀ t : ℕ, ∃ u : Kˣ, u ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))) ∧
      ∀ w ∈ Ts, localClassHom w p u = spreadClasses Tp cl t w := by
    intro t
    obtain ⟨u, hu⟩ := exists_sUnit_forall_localClassHom_eq_of_detecting hp hres hζ
      (ι := (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))) Subtype.val_injective hnι hrepr'
      {y : ↥Tn | (y : HeightOneSpectrum (𝓞 K)) ∈ Ts}
      {y : ↥Tn | (y : HeightOneSpectrum (𝓞 K)) ∈ Tp}
      (fun y => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 K)))
      (fun y _ hy => spreadClasses_of_notMem hy t)
      (by
        intro v hvinf hvTs y hy
        refine hdet (v : Kˣ) (by rw [← hrange]; exact v.2) hvinf ?_ (y : _) hy
        intro w hw hws
        exact hvTs ⟨w, hw⟩ hws)
    have humem : (u : Kˣ) ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))) := by
      rw [← hrange]
      exact u.2
    exact ⟨(u : Kˣ), humem, fun w hw => hu ⟨w, hTs hw⟩ hw⟩
  choose g hgS hgloc using hex
  refine exists_isTwoPlaceFamily_named_split_of_sUnits Ω hp hodd hζ hres hTp hTr hTs hTrst hTnst
    hpTn hrepr hclfree hcln hDgal hDcl hgS ?_ ?_ hsplit hram d
  · intro t w
    have h := hgloc t (w : HeightOneSpectrum (𝓞 K)) (hTr (hTp w.2))
    rw [spreadClasses_of_mem w.2 t] at h
    exact h.symm
  · intro t w hw hwp
    rw [hgloc t w hw]
    exact spreadClasses_of_notMem hwp t

end NamedSplit

end InverseGalois.CFT
