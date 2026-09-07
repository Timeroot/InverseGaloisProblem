/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ClassSetAvoid
import InverseGalois.CFT.PoitouTate.TwoPlaces

/-!
# Two completely split places, with no hypothesis on the class group

The construction of two completely split places carrying a prescribed local behaviour is run
relative to a finite set of places, and it asks that every finitely supported system of orders be
realised by an element of the field away from that set.  The primes occurring in a system of
representatives of the ideal classes are exactly such a set, but they are not the set the
construction is handed: that one is dictated by the places where the unit being prescribed fails to
be a unit, and by the places over the exponent.

The two can be reconciled.  The representatives of the ideal classes may be moved off any finite
set, so they may be moved off the places already spoken for; the set the construction is run with is
then their union, and the extra places contribute nothing, being places where the unit is a unit and
which do not lie over the exponent.  What remains is a statement about the places one actually cares
about: a finite stable set containing those over the exponent, and a unit whose failure to be a unit
outside it happens only at places completely split in the auxiliary field.

## Main results

* `InverseGalois.CFT.exists_two_places_sUnit_class_eq_of_split`: **two places completely split in
  the auxiliary field and a unit ramified exactly at them realising a prescribed local behaviour**,
  with no hypothesis relating the fixed set of places to the ideal classes.

## Tags

number field, place, completely split, local class, prescription, class group
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### Absorbing the ideal classes into the set of places -/

section Free

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω] {p : ℕ} [NeZero p]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **Two places completely split in the auxiliary field and a unit ramified exactly at them,
realising a prescribed local behaviour on a stable finite set of places.**  The set is only asked to
be stable and to contain the places over the exponent, the unit being a unit outside it except at
places which are themselves completely split; the primes carrying the ideal classes are adjoined to
it, and being places where the unit is a unit and which do not lie over the exponent they leave the
prescription untouched. -/
theorem exists_two_places_sUnit_class_eq_of_split (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hpT : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ T)
    {y : Kˣ}
    (hysplit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → Rigidity.RET.ord K v (y : K) ≠ 0 →
      ∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = v ∧
        stabilizer Gal(↥Ω/k) w = ⊥)
    (hyunr : ∀ v ∈ T, localClassHom v p y ∈ localUnramified v p)
    (hyp : ∀ v ∈ T, Pc v ∣ p → localClassHom v p y = 1) :
    ∃ Q R : HeightOneSpectrum (𝓞 K), Q ∉ T ∧ R ∉ T ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = Q ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = R ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      (∀ σ : Gal(K/k), Q ≠ σ • R) ∧
      stabilizer Gal(K/k) Q = ⊥ ∧ stabilizer Gal(K/k) R = ⊥ ∧
      ∃ z : Kˣ, (∀ v ∈ T, localClassHom v p z = localClassHom v p y) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ≠ Q → v ≠ R → (p : ℤ) ∣ placeValue v z) ∧
        ¬ (p : ℤ) ∣ placeValue Q z ∧ ¬ (p : ℤ) ∣ placeValue R z ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • Q) p z = 1) ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • R) p z = 1) := by
  classical
  haveI : IsGalois k ↥Ω := ⟨⟩
  have hsupp : {v : HeightOneSpectrum (𝓞 K) | Rigidity.RET.ord K v (y : K) ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (Rigidity.RET.ord_finite (y : K))
  set Y : Set (HeightOneSpectrum (𝓞 K)) :=
    ⋃ σ : Gal(K/k), (fun v => σ • v) ''
      {v : HeightOneSpectrum (𝓞 K) | Rigidity.RET.ord K v (y : K) ≠ 0} with hYdef
  have hYfin : Y.Finite := by
    rw [hYdef]
    exact Set.finite_iUnion fun σ => hsupp.image _
  have hYsupp : ∀ v : HeightOneSpectrum (𝓞 K), Rigidity.RET.ord K v (y : K) ≠ 0 → v ∈ Y := by
    intro v hv
    rw [hYdef]
    exact Set.mem_iUnion.2 ⟨1, v, hv, one_smul _ v⟩
  have hYstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Y → σ • v ∈ Y := by
    intro σ v hv
    rw [hYdef] at hv ⊢
    obtain ⟨τ, u, hu, hτu⟩ := Set.mem_iUnion.1 hv
    refine Set.mem_iUnion.2 ⟨σ * τ, u, hu, ?_⟩
    show (σ * τ) • u = σ • v
    rw [mul_smul, show τ • u = v from hτu]
  have hYsplit : ∀ v ∈ Y, v ∉ T → ∃ w : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) w = v ∧ stabilizer Gal(↥Ω/k) w = ⊥ := by
    intro v hv hvT
    rw [hYdef] at hv
    obtain ⟨τ, u, hu, rfl⟩ := Set.mem_iUnion.1 hv
    obtain ⟨w, hw1, hw2⟩ := hysplit u (fun hc => hvT (hTstable τ u hc)) hu
    subst hw1
    exact exists_primeUnder_eq_smul_stabilizer_eq_bot (K := K) hw2 τ
  have hEstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
      v ∈ T ∪ hYfin.toFinset → σ • v ∈ T ∪ hYfin.toFinset := by
    intro σ v hv
    rcases Finset.mem_union.1 hv with h | h
    · exact Finset.mem_union_left _ (hTstable σ v h)
    · exact Finset.mem_union_right _
        ((Set.Finite.mem_toFinset _).2 (hYstable σ v ((Set.Finite.mem_toFinset _).1 h)))
  obtain ⟨X, hXfin, hXstable, hXE, hXrepr⟩ :=
    exists_finite_stable_ord_repr_disjoint (k := k) (T ∪ hYfin.toFinset) hEstable
  obtain ⟨T', hT'⟩ : ∃ T' : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ v : HeightOneSpectrum (𝓞 K), v ∈ T' ↔ v ∈ T ∨ v ∈ X :=
    ⟨T ∪ hXfin.toFinset, fun v => by rw [Finset.mem_union, Set.Finite.mem_toFinset]⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S₀ ↔ v ∈ T' ∨ v ∈ Y :=
    ⟨T' ∪ hYfin.toFinset, fun v => by rw [Finset.mem_union, Set.Finite.mem_toFinset]⟩
  have hT'stable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T' → σ • v ∈ T' := by
    intro σ v hv
    rcases (hT' v).1 hv with h | h
    · exact (hT' _).2 (Or.inl (hTstable σ v h))
    · exact (hT' _).2 (Or.inr ((hXstable σ v).2 h))
  have hT'S : T' ⊆ S₀ := fun v hv => (hS₀ v).2 (Or.inl hv)
  have hSstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S₀ → σ • v ∈ S₀ := by
    intro σ v hv
    rcases (hS₀ v).1 hv with h | h
    · exact (hS₀ _).2 (Or.inl (hT'stable σ v h))
    · exact (hS₀ _).2 (Or.inr (hYstable σ v h))
  have hSsplit : ∀ v ∈ S₀, v ∉ T' → ∃ w : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) w = v ∧ stabilizer Gal(↥Ω/k) w = ⊥ := by
    intro v hv hvT'
    rcases (hS₀ v).1 hv with h | h
    · exact absurd h hvT'
    · exact hYsplit v h fun hc => hvT' ((hT' v).2 (Or.inl hc))
  have hpT' : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ T' :=
    fun v hv => (hT' v).2 (Or.inl (hpT v hv))
  have hreprS : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (S₀ : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v := by
    intro m hm
    obtain ⟨a, ha⟩ := hXrepr m hm
    exact ⟨a, fun v hv => ha v fun hvX =>
      hv (Finset.mem_coe.2 ((hS₀ v).2 (Or.inl ((hT' v).2 (Or.inr hvX)))))⟩
  have hyS : y ∈ sUnits K (S₀ : Set (HeightOneSpectrum (𝓞 K))) :=
    mem_sUnits.2 fun v hv => by
      by_contra hc
      exact hv (Finset.mem_coe.2 ((hS₀ v).2 (Or.inr (hYsupp v hc))))
  have hyzero : ∀ v ∈ X, Rigidity.RET.ord K v (y : K) = 0 := by
    intro v hv
    by_contra hc
    exact hXE v hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 (hYsupp v hc)))
  have hyunr' : ∀ v ∈ T', localClassHom v p y ∈ localUnramified v p := by
    intro v hv
    rcases (hT' v).1 hv with h | h
    · exact hyunr v h
    · refine (localClassHom_mem_localUnramified_iff v y).2 ?_
      rw [placeValue_eq_neg_ord, hyzero v h, neg_zero]
      exact dvd_zero _
  have hyp' : ∀ v ∈ T', Pc v ∣ p → localClassHom v p y = 1 := by
    intro v hv hdvd
    rcases (hT' v).1 hv with h | h
    · exact hyp v h hdvd
    · exact absurd (Finset.mem_union_left _ (hpT v fun hone =>
        not_dvd_of_finitePlace_natCast_eq_one (hres v) hone hdvd)) (hXE v h)
  obtain ⟨Q, R, hQT, hRT, hQspl, hRspl, hQR, hQstab, hRstab, z, hzT, hzunr, hzQ, hzR, hzQc,
    hzRc⟩ := exists_two_places_sUnit_class_eq (Ω := Ω) hp hodd hζ hres hT'stable hT'S hSstable
      hSsplit hpT' hreprS hyS hyunr' hyp'
  exact ⟨Q, R, fun hc => hQT ((hT' Q).2 (Or.inl hc)), fun hc => hRT ((hT' R).2 (Or.inl hc)),
    hQspl, hRspl, hQR, hQstab, hRstab, z, fun v hv => hzT v ((hT' v).2 (Or.inl hv)),
    hzunr, hzQ, hzR, hzQc, hzRc⟩

end Free

end InverseGalois.CFT
