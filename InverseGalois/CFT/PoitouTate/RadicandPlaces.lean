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

end Hull

end InverseGalois.CFT
