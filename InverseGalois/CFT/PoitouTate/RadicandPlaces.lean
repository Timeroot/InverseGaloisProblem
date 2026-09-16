/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.OrdFinsupp

/-!
# Making a set of places stable

The descent through the units of a number field is run over sets of places carried into themselves
by the Galois group, while the sets a prescription arrives with — the finitely many named places,
the finitely many places a local condition is imposed at — are arbitrary.  Two constructions repair
that: the **hull**, the places some translate of which lies in the given set, and the **core**, the
places every translate of which does.  The hull is the smallest stable set containing the given
one, and is still finite when the given one is; the core is the largest stable set contained in it.

Together with the observation that a union of stable sets is stable, that is everything needed to
put an arbitrary prescription into the shape the descent consumes.

## Main definitions

* `InverseGalois.CFT.stableHull`: **the smallest stable set of places containing a given one.**
* `InverseGalois.CFT.stableCore`: **the largest stable set of places contained in a given one.**

## Main results

* `InverseGalois.CFT.subset_stableHull`, `InverseGalois.CFT.stableCore_subset`: the given set sits
  between its core and its hull.
* `InverseGalois.CFT.stableHull_finite`: **the hull of a finite set is finite.**
* `InverseGalois.CFT.isGaloisStablePlaces_union`: a union of two stable sets is stable.
* `InverseGalois.CFT.stableCore_eq_self`: a stable set is its own core.
* `InverseGalois.CFT.stableHull_subset_of_stable`: the hull is the smallest stable set containing
  the given one.
* `InverseGalois.CFT.stableHull_eq_self`: a stable set is its own hull.
* `InverseGalois.CFT.exists_orbitReps`: **a finite set of places is met by finitely many orbits**,
  and representatives of them lie in the set and have the same hull.

## Tags

number field, height one prime, Galois action, stable set of places
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Hull

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **The smallest stable set of places containing a given one**: the places some translate of
which lies in the set. -/
def stableHull : Set (HeightOneSpectrum (𝓞 K)) := {v | ∃ σ : Gal(K/k), σ • v ∈ S}

/-- **The largest stable set of places contained in a given one**: the places every translate of
which lies in the set. -/
def stableCore : Set (HeightOneSpectrum (𝓞 K)) := {v | ∀ σ : Gal(K/k), σ • v ∈ S}

omit [NumberField K] in
theorem mem_stableHull {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ stableHull k K S ↔ ∃ σ : Gal(K/k), σ • v ∈ S := Iff.rfl

omit [NumberField K] in
theorem mem_stableCore {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ stableCore k K S ↔ ∀ σ : Gal(K/k), σ • v ∈ S := Iff.rfl

/-- The hull of a set is stable. -/
instance isGaloisStablePlaces_stableHull : IsGaloisStablePlaces k K (stableHull k K S) where
  smul_mem_iff τ v := by
    constructor
    · rintro ⟨σ, hσ⟩
      exact ⟨σ * τ, by rw [mul_smul]; exact hσ⟩
    · rintro ⟨σ, hσ⟩
      refine ⟨σ * τ⁻¹, ?_⟩
      rw [mul_smul, inv_smul_smul]
      exact hσ

/-- The core of a set is stable. -/
instance isGaloisStablePlaces_stableCore : IsGaloisStablePlaces k K (stableCore k K S) where
  smul_mem_iff τ v := by
    constructor
    · intro h σ
      have h2 := h (σ * τ⁻¹)
      rwa [mul_smul, inv_smul_smul] at h2
    · intro h σ
      rw [← mul_smul]
      exact h (σ * τ)

omit [NumberField K] in
/-- A set is contained in its hull. -/
theorem subset_stableHull : S ⊆ stableHull k K S := fun _ hv => ⟨1, by rwa [one_smul]⟩

omit [NumberField K] in
/-- The core of a set is contained in the set. -/
theorem stableCore_subset : stableCore k K S ⊆ S := fun _ hv => by simpa using hv 1

variable {k K S}

omit [NumberField K] in
/-- **The hull of a finite set is finite**: it is covered by the translates of the set, and there
are finitely many of those. -/
theorem stableHull_finite [Finite Gal(K/k)] (hS : S.Finite) : (stableHull k K S).Finite := by
  refine Set.Finite.subset (Set.finite_iUnion
    (fun σ : Gal(K/k) => hS.image (fun w => σ⁻¹ • w))) fun v hv => ?_
  obtain ⟨σ, hσ⟩ := hv
  exact Set.mem_iUnion.2 ⟨σ, ⟨σ • v, hσ, inv_smul_smul σ v⟩⟩

/-- A union of two stable sets of places is stable. -/
theorem isGaloisStablePlaces_union (S₁ S₂ : Set (HeightOneSpectrum (𝓞 K)))
    [IsGaloisStablePlaces k K S₁] [IsGaloisStablePlaces k K S₂] :
    IsGaloisStablePlaces k K (S₁ ∪ S₂) where
  smul_mem_iff σ v :=
    or_congr (IsGaloisStablePlaces.smul_mem_iff (k := k) σ v)
      (IsGaloisStablePlaces.smul_mem_iff (k := k) σ v)

/-- **A stable set of places is its own core**, every translate of one of its places lying in it
again. -/
theorem stableCore_eq_self [IsGaloisStablePlaces k K S] : stableCore k K S = S :=
  Set.Subset.antisymm (stableCore_subset k K S)
    fun _ hv σ => (IsGaloisStablePlaces.smul_mem_iff (k := k) σ _).2 hv

omit [NumberField K] in
/-- The hull is monotone. -/
theorem stableHull_mono {S₁ S₂ : Set (HeightOneSpectrum (𝓞 K))} (h : S₁ ⊆ S₂) :
    stableHull k K S₁ ⊆ stableHull k K S₂ := fun _ ⟨σ, hσ⟩ => ⟨σ, h hσ⟩

/-- **The hull is the smallest stable set containing the given one.** -/
theorem stableHull_subset_of_stable {S T : Set (HeightOneSpectrum (𝓞 K))}
    [IsGaloisStablePlaces k K T] (h : S ⊆ T) : stableHull k K S ⊆ T :=
  fun _ ⟨σ, hσ⟩ => (IsGaloisStablePlaces.smul_mem_iff (k := k) σ _).1 (h hσ)

/-- **A stable set of places is its own hull**, a place one translate of which lies in it lying in
it itself. -/
theorem stableHull_eq_self [IsGaloisStablePlaces k K S] : stableHull k K S = S :=
  Set.Subset.antisymm (stableHull_subset_of_stable (k := k) subset_rfl) (subset_stableHull k K S)

end Hull

/-! ### Representatives of the orbits met by a set of places -/

section Reps

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]

/-- The places of a set, related when the Galois group moves one to the other. -/
def placeOrbitSetoid (k : Type) [Field k] {K : Type} [Field K] [Algebra k K] [NumberField K]
    (X : Set (HeightOneSpectrum (𝓞 K))) : Setoid ↥X where
  r v v' := ∃ σ : Gal(K/k), σ • (v : HeightOneSpectrum (𝓞 K)) = (v' : HeightOneSpectrum (𝓞 K))
  iseqv :=
    { refl := fun v => ⟨1, one_smul _ _⟩
      symm := fun ⟨σ, hσ⟩ => ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩
      trans := fun ⟨σ, hσ⟩ ⟨τ, hτ⟩ => ⟨τ * σ, by rw [mul_smul, hσ, hτ]⟩ }

/-- **A finite set of places is met by finitely many orbits, and representatives of them lie in the
set and have the same hull.**  Naming one place in each orbit the set meets replaces the set by one
whose places lie in distinct orbits, which is what a prescription made one orbit at a time asks
for, and nothing is lost because the two sets become stable in the same way. -/
theorem exists_orbitReps (X : Set (HeightOneSpectrum (𝓞 K))) (hX : X.Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → HeightOneSpectrum (𝓞 K)),
      (∀ μ : ι, w μ ∈ X) ∧ (∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(K/k), σ • w μ ≠ w ν) ∧
      stableHull k K (Set.range w) = stableHull k K X := by
  classical
  haveI : Finite ↥X := hX
  letI st : Setoid ↥X := placeOrbitSetoid k X
  refine ⟨Quotient st, Fintype.ofFinite _,
    fun q => ((Quotient.out q : ↥X) : HeightOneSpectrum (𝓞 K)), fun q => (Quotient.out q).2,
    fun μ ν hμν σ hcon => hμν ?_, ?_⟩
  · have hrel : (Quotient.out μ : ↥X) ≈ (Quotient.out ν : ↥X) := ⟨σ, hcon⟩
    rw [← Quotient.out_eq μ, ← Quotient.out_eq ν]
    exact Quotient.sound hrel
  · refine Set.Subset.antisymm (stableHull_mono fun v hv => ?_)
      (stableHull_subset_of_stable fun v hv => ?_)
    · obtain ⟨q, rfl⟩ := hv
      exact (Quotient.out q).2
    · obtain ⟨σ, hσ⟩ := Quotient.mk_out (s := st) (⟨v, hv⟩ : ↥X)
      have hσ' : σ • ((Quotient.mk st (⟨v, hv⟩ : ↥X)).out : HeightOneSpectrum (𝓞 K)) = v := hσ
      exact ⟨σ⁻¹, ⟨Quotient.mk st ⟨v, hv⟩, eq_inv_smul_iff.2 hσ'⟩⟩

end Reps

end InverseGalois.CFT
