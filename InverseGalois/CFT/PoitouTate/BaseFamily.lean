/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.BasePrescription
import InverseGalois.CFT.PoitouTate.RankOne

/-!
# The coordinates of a family carried down to the base field

The family of units built one coordinate at a time lives in the upper field, and the way down to
the base is the norm, applied coordinate by coordinate.  Three of the properties of the family
survive the descent, and together they are what a prescription with values in a module of several
coordinates asks for.

On the set carrying the prescription the constructed unit of a coordinate has, at every place above
a place of the base, the same class as the prescribed unit of that coordinate; so the two norms have
the same class at that place of the base.

At a place of the base lying under one of the exceptional places of a coordinate, every other
coordinate is a local power at every place above, so the norm of every other coordinate is a local
power there and the one surviving coordinate generates.  That place of the base is completely split,
so its completion is the completion of the upper field and carries the roots of unity that field was
assumed to contain: the class is a radical class of a field with the roots of unity, hence split by
a cyclic extension.

At every other place of the base outside the prescribed part no coordinate is ramified at any place
above, so every coordinate is unramified downstairs, and an unramified class is split by an
unramified extension.

## Main results

* `InverseGalois.CFT.exists_base_norm_class_of_isTwoPlaceFamily`: the norms of the units of a family
  agree with the norms of the prescribed units on the prescribed part, and at every place of the
  base outside it are either all unramified or all powers of a single class over a completion
  carrying the roots of unity.
* `InverseGalois.CFT.exists_base_family_norm_class_eq`: **for every number of coordinates there are
  numbers of the base field with that behaviour.**

## Tags

number field, norm, place, local class, cyclic, unramified, completely split, prescription
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### The descent of a family -/

section Descent

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Field K] [NumberField K]
  [Algebra k K] [IsGalois k K] {Ω : IntermediateField k A} [NumberField ↥Ω] [Algebra K ↥Ω]
  {p : ℕ} [NeZero p]

/-- **The norms of the units of a family behave as a prescription with values in a module of
several coordinates asks.**  On the prescribed part the norm of a coordinate has the class of the
norm of the prescribed unit of that coordinate.  Outside it, a place of the base either lies under
one of the exceptional places of some coordinate, where every other coordinate is a local power and
the completion carries the roots of unity, or lies under no exceptional place at all, where every
coordinate is unramified. -/
theorem exists_base_norm_class_of_isTwoPlaceFamily (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ Tn)
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    (hTram : ∀ v : HeightOneSpectrum (𝓞 K), ramIdx (𝓞 k) v ≠ 1 → v ∈ T)
    {c : ℕ → (v : HeightOneSpectrum (𝓞 K)) → localClasses v p} {g : ℕ → Kˣ}
    (hc : ∀ (i : ℕ), ∀ v ∈ T, c i v = localClassHom v p (g i))
    {d : ℕ} {S : Finset (HeightOneSpectrum (𝓞 K))} {Q R : ℕ → HeightOneSpectrum (𝓞 K)}
    {z : ℕ → Kˣ} (h : IsTwoPlaceFamily Ω p Tn c d S Q R z) :
    (∀ i < d, ∀ v ∈ T,
        localClassHom (primeUnder (𝓞 k) v) p (Units.map (Algebra.norm k : K →* k) (z i))
          = localClassHom (primeUnder (𝓞 k) v) p
              (Units.map (Algebra.norm k : K →* k) (g i))) ∧
      ∀ q : HeightOneSpectrum (𝓞 k), (∀ v ∈ T, primeUnder (𝓞 k) v ≠ q) →
        (∀ i < d, localClassHom q p (Units.map (Algebra.norm k : K →* k) (z i))
            ∈ localUnramified q p) ∨
          ((∃ ξ : q.adicCompletion k, IsPrimitiveRoot ξ p) ∧
            ∃ u : localClasses q p, ∀ i < d,
              localClassHom q p (Units.map (Algebra.norm k : K →* k) (z i))
                ∈ Subgroup.zpowers u) := by
  classical
  refine ⟨fun i hi v hv => ?_, fun q hq => ?_⟩
  · refine localClassHom_norm_eq_of_forall_eq k v hp.ne_zero (z i) (g i) fun σ => ?_
    rw [h.prescribed i hi (σ • v) (hTnst σ v (hT hv)), hc i (σ • v) (hTstable σ v hv)]
  by_cases hA : ∃ j < d, primeUnder (𝓞 k) (Q j) = q ∨ primeUnder (𝓞 k) (R j) = q
  · obtain ⟨j, hj, hjq⟩ := hA
    refine Or.inr ⟨?_, ?_⟩
    · rcases hjq with hjq | hjq
      · exact hjq ▸ exists_isPrimitiveRoot_adicCompletion_of_stabilizer_eq_bot k (Q j) hζ
          (h.stabQ j hj)
      · exact hjq ▸ exists_isPrimitiveRoot_adicCompletion_of_stabilizer_eq_bot k (R j) hζ
          (h.stabR j hj)
    · refine ⟨localClassHom q p (Units.map (Algebra.norm k : K →* k) (z j)), fun i hi => ?_⟩
      rcases eq_or_ne i j with rfl | hij
      · exact Subgroup.mem_zpowers _
      · have hone : localClassHom q p (Units.map (Algebra.norm k : K →* k) (z i)) = 1 := by
          rcases hjq with hjq | hjq
          · rw [← hjq]
            exact localClassHom_norm_eq_one k (Q j) hp.ne_zero (z i)
              fun σ => h.crossQ i hi j hj hij σ
          · rw [← hjq]
            exact localClassHom_norm_eq_one k (R j) hp.ne_zero (z i)
              fun σ => h.crossR i hi j hj hij σ
        rw [hone]
        exact one_mem _
  · push_neg at hA
    obtain ⟨P, rfl⟩ := exists_primeUnder_eq (𝓞 k) (𝓞 K) q
    have hPT : P ∉ T := fun hcon => hq P hcon rfl
    refine Or.inl fun i hi => localClassHom_norm_mem_localUnramified k P
      (not_not.1 fun hcon => hPT (hTram P hcon)) (z i) fun σ => ?_
    refine (localClassHom_mem_localUnramified_iff (σ • P) (z i)).2
      (h.unram i hi (σ • P) (fun hcon => (hA i hi).1 ?_) fun hcon => (hA i hi).2 ?_)
    · rw [← hcon, primeUnder_smul_eq]
    · rw [← hcon, primeUnder_smul_eq]

end Descent

/-! ### The numbers of the base field -/

section Base

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  [IsScalarTower k K A] {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω]
  {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **For every number of coordinates there are numbers of the base field realising a prescription
with values in a module of that many coordinates, cyclically at every place outside the prescribed
part.**  The family of units of the upper field is carried down coordinate by coordinate by the
norm. -/
theorem exists_base_family_norm_class_eq (hp : p.Prime) (hodd : 2 < p) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ Tn)
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hTram : ∀ v : HeightOneSpectrum (𝓞 K), ramIdx (𝓞 k) v ≠ 1 → v ∈ T)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {c : ℕ → (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hcunr : ∀ (i : ℕ), ∀ v ∈ Tn, c i v ∈ localUnramified v p)
    {g : ℕ → Kˣ} (hg : ∀ i : ℕ, g i ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ (i : ℕ), ∀ v ∈ T, c i v = localClassHom v p (g i))
    (hcT : ∀ (i : ℕ), ∀ v ∈ Tn, v ∉ T → c i v = 1)
    (hcn : ∀ (i : ℕ), ∀ v ∈ T, FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → c i v = 1)
    (hsplit : ∀ v ∈ Tn, v ∉ T → ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/K) W = ⊥)
    (hram : ∀ v ∉ Tn, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1) (d : ℕ) :
    ∃ x : ℕ → kˣ,
      (∀ i : ℕ, ∃ t : Kˣ, x i = Units.map (Algebra.norm k : K →* k) t) ∧
      (∀ i < d, ∀ v ∈ T, localClassHom (primeUnder (𝓞 k) v) p (x i)
        = localClassHom (primeUnder (𝓞 k) v) p
            (Units.map (Algebra.norm k : K →* k) (g i))) ∧
      ∀ q : HeightOneSpectrum (𝓞 k), (∀ v ∈ T, primeUnder (𝓞 k) v ≠ q) →
        (∀ i < d, localClassHom q p (x i) ∈ localUnramified q p) ∨
          ((∃ ξ : q.adicCompletion k, IsPrimitiveRoot ξ p) ∧
            ∃ u : localClasses q p, ∀ i < d,
              localClassHom q p (x i) ∈ Subgroup.zpowers u) := by
  classical
  obtain ⟨S, Q, R, z, hfam⟩ :=
    exists_isTwoPlaceFamily (Ω := Ω) hp hodd hζ hres hT hTnst hpTn hrepr hcunr hg hc hcT hcn
      hsplit hram d
  obtain ⟨hxT, hxq⟩ :=
    exists_base_norm_class_of_isTwoPlaceFamily (Ω := Ω) hp hζ hT hTstable hTnst hTram hc hfam
  exact ⟨fun i => Units.map (Algebra.norm k : K →* k) (z i), fun i => ⟨z i, rfl⟩, hxT, hxq⟩

end Base

end InverseGalois.CFT
