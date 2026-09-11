/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.NamedFamilySplit
import InverseGalois.CFT.PoitouTate.SplitDetect

/-!
# A two-place family for a naming, tested only against the powers of the auxiliary field

Asking the split places of `S` to detect the `S`-units outright — an `S`-unit trivial at all of them
being trivial at the named places too — is more than the split places can deliver: they see an
`S`-unit only through its being a power in the auxiliary field, and the units of the base which are
already powers there escape them.  What they do deliver is exactly that much, and it is enough to
cut the reciprocity obstruction down to those units.

The obstruction to realising a naming by the class of an `S`-unit is a product of symbols over the
places of `S`, to be tested against the `S`-units which are local powers at the infinite places and
trivial at the places where the naming is not made.  Every such `S`-unit becomes a power in the
auxiliary field, so the test may be restricted to those, and the two-place construction then turns
the realising family of `S`-units into a family of two-place data.  Choosing the places of `S`
outside the prescribed part to be the detecting ones makes that restriction available for free, and
leaves the orthogonality against the powers of the auxiliary field as the only condition.

## Main results

* `InverseGalois.CFT.exists_isTwoPlaceFamily_named_orthogonal`: a naming orthogonal to those
  `S`-units which become a power in the auxiliary field has a two-place family.
* `InverseGalois.CFT.exists_isTwoPlaceFamily_named_of_orthogonal`: **enlarging the set of places by
  a Galois stable set of split detecting places, a naming orthogonal to the `S`-units which become a
  power in the auxiliary field has a two-place family**, with the detection supplied by the
  enlargement.

## Tags

number field, place, local class, prescription, S-unit, completely split, Poitou-Tate duality
-/

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

section NamedPower

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  [IsScalarTower k K A] {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω]
  {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

variable (Ω) in
/-- **A naming orthogonal to those `S`-units which become a power in the auxiliary field has a
two-place family.**

The `S`-units against which the naming has to be tested are those which are a local power at every
infinite place and trivial at every place of `S` where the naming is not made.  When the places of
that second kind force such an `S`-unit to be a power in the auxiliary field, the test is only ever
applied to units which are, so orthogonality against those alone realises the naming by the class of
an `S`-unit, one coordinate at a time. -/
theorem exists_isTwoPlaceFamily_named_orthogonal (hp : p.Prime) (hodd : 2 < p)
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
    (hpow : ∀ u : Kˣ, u ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))) →
      (∀ v ∈ Tn, v ∉ Ts → localClassHom v p u = 1) →
      ∃ y : (↥Ω)ˣ, Units.map (algebraMap K ↥Ω : K →* ↥Ω) u = y ^ p)
    (horth : ∀ (t : ℕ)
      (u : ↥(sUnits K (Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))))),
      (∀ w : InfinitePlace K, infClassHom w p ((u : Kˣ)) = 1) →
      (∃ y : (↥Ω)ˣ, Units.map (algebraMap K ↥Ω : K →* ↥Ω) ((u : Kˣ)) = y ^ p) →
      localSymbolPiPairing hres hζ (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))
        (sUnitClassHom (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K)) p u)
        (fun y => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 K))) = 1)
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
    obtain ⟨u, hu⟩ := exists_sUnit_forall_mem_localClassHom_eq hp hres hζ
      (ι := (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))) Subtype.val_injective hnι hrepr'
      {y : ↥Tn | (y : HeightOneSpectrum (𝓞 K)) ∈ Ts}
      (fun y => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 K)))
      (by
        intro v hvinf hvTs
        refine horth t v hvinf (hpow (v : Kˣ) (by rw [← hrange]; exact v.2) ?_)
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

end NamedPower

/-! ### The enlargement by the detecting places -/

section NamedDetect

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  [IsScalarTower k K A] {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω] [FiniteDimensional k ↥Ω]
  [IsGalois k ↥Ω] {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

variable (Ω) in
/-- **A naming orthogonal to the `S`-units which become a power in the auxiliary field has a
two-place family**, over a set of places enlarged by a Galois stable set of places completely split
in that field.

The enlargement is the set of detecting places: an `S`-unit for any set of places containing them,
trivial at every place outside the original set, is a power in the auxiliary field.  Adjoining them
keeps every property the two-place construction asks of the set of places — stability under the
Galois group, containing the places over the exponent, carrying representatives of the divisors, and
the complete splitting at the new places — so the only condition left is the orthogonality against
those `S`-units which are already powers upstairs. -/
theorem exists_isTwoPlaceFamily_named_of_orthogonal (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {Tp Tr Ts : Finset (HeightOneSpectrum (𝓞 K))} (hTp : Tp ⊆ Tr) (hTr : Tr ⊆ Ts)
    (hTrst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tr → σ • v ∈ Tr)
    (hTsst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Ts → σ • v ∈ Ts)
    (hpTs : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Ts)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Ts : Set (HeightOneSpectrum (𝓞 K))),
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
    (horth : ∀ Tn : Finset (HeightOneSpectrum (𝓞 K)), Ts ⊆ Tn → ∀ (t : ℕ)
      (u : ↥(sUnits K (Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))))),
      (∀ w : InfinitePlace K, infClassHom w p ((u : Kˣ)) = 1) →
      (∃ y : (↥Ω)ˣ, Units.map (algebraMap K ↥Ω : K →* ↥Ω) ((u : Kˣ)) = y ^ p) →
      localSymbolPiPairing hres hζ (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))
        (sUnitClassHom (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K)) p u)
        (fun y => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 K))) = 1)
    (hram : ∀ v ∉ Ts, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1) (d : ℕ) :
    ∃ Tn : Finset (HeightOneSpectrum (𝓞 K)), Ts ⊆ Tn ∧
      (∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn) ∧
      ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (Q R : ℕ → HeightOneSpectrum (𝓞 K)) (z : ℕ → Kˣ),
        IsTwoPlaceFamily Ω p Tr Tn (spreadClasses Tp cl) d S Q R z := by
  classical
  obtain ⟨Tf, hTf, hTfst, hTfsp, hTfdet⟩ :=
    exists_finset_stable_split_detecting_sUnits Ω hp hζ hres (Ts.image (primeUnder (𝓞 k))) Ts
      (fun v hv => Finset.mem_image_of_mem _ hv) hrepr
  have hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Ts ∪ Tf → σ • v ∈ Ts ∪ Tf := by
    intro σ v hv
    rcases Finset.mem_union.1 hv with h | h
    · exact Finset.mem_union_left _ (hTsst σ v h)
    · exact Finset.mem_union_right _ (hTfst σ v h)
  have hreprn : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ ((Ts ∪ Tf : Finset (HeightOneSpectrum (𝓞 K))) :
        Set (HeightOneSpectrum (𝓞 K))), Rigidity.RET.ord K v (a : K) = m v := by
    intro m hm
    obtain ⟨a, ha⟩ := hrepr m hm
    exact ⟨a, fun v hv => ha v fun hc =>
      hv (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hc)))⟩
  refine ⟨Ts ∪ Tf, Finset.subset_union_left, hTnst, ?_⟩
  refine exists_isTwoPlaceFamily_named_orthogonal Ω hp hodd hζ hres hTp hTr
    Finset.subset_union_left hTrst hTnst
    (fun v hv => Finset.mem_union_left _ (hpTs v hv)) hreprn hclfree hcln hDgal hDcl
    (hTfdet (Ts ∪ Tf) Finset.subset_union_right)
    (horth (Ts ∪ Tf) Finset.subset_union_left) ?_
    (fun v hv => hram v fun hc => hv (Finset.mem_union_left _ hc)) d
  intro v hv hvs
  obtain ⟨W, hW, hWbot⟩ := hTfsp v ((Finset.mem_union.1 hv).resolve_left hvs)
  exact ⟨W, hW, stabilizer_eq_bot_of_stabilizer_base_eq_bot (k := k) hWbot⟩

end NamedDetect

end InverseGalois.CFT
