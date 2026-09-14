/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.PoitouTate.SplitPlaceDescend
import InverseGalois.CFT.Units.BaseChangeCocycle

/-!
# Finitely many completely split primes force a radical into an intermediate field

A radical of an element of a subfield is fixed by the decomposition group at a prime exactly when
its radicand is a power in the completion below, the subfield carrying the roots of unity.  A prime
of the base splitting completely in an intermediate field has every decomposition group above it
inside the subgroup fixing that field, hence inside the subgroup fixing any smaller field; so the
decomposition group, read over the base, may be read over the subfield instead, and the local
condition applies to it.

Finitely many completely split primes already detect membership of the intermediate field.
Combining the two, **being a local power at each of finitely many completely split primes of the
base forces the radical into the intermediate field**: a purely finite-level statement, with no
infinite extension and no place of the intermediate field anywhere in it.

## Main results

* `InverseGalois.CFT.exists_finite_splitsCompletelyIn_mem_of_forall_localPow`: **finitely many
  primes of the base, splitting completely in an intermediate field and avoiding any prescribed
  finite set, force a radical whose radicand is locally a power at each of them into that field.**

## Tags

number field, Kummer theory, radical, completely split, decomposition group, completion
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField NumberTheory

section Member

variable {k N : Type} [Field k] [NumberField k] [Field N] [NumberField N] [Algebra k N]
  [IsGalois k N]

/-- **Finitely many primes of the base, splitting completely in an intermediate field and avoiding
any prescribed finite set, force a radical whose radicand is locally a power at each of them into
that field.**

At such a prime the decomposition group above it fixes the intermediate field, hence the smaller
field carrying the radicand and the roots of unity, so it may be read as a decomposition group over
that smaller field; there the radicand being a power in the completion says exactly that the
radical is fixed.  Fixed by every decomposition group above finitely many completely split primes,
the radical lies in the intermediate field. -/
theorem exists_finite_splitsCompletelyIn_mem_of_forall_localPow (K E : IntermediateField k N)
    [NumberField ↥K] [NumberField ↥E] [IsGalois k ↥E] (hKE : K ≤ E) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (T : Finset (HeightOneSpectrum (𝓞 k))) :
    ∃ S : Set (HeightOneSpectrum (𝓞 k)), S.Finite ∧
      (∀ v ∈ S, v ∉ T ∧ SplitsCompletelyIn k ↥E v) ∧
      ∀ (a : ↥K) (ξ : N), algebraMap (↥K) N a = ξ ^ ℓ →
        (∀ W : HeightOneSpectrum (𝓞 N), primeUnder (𝓞 k) W ∈ S →
          ∃ c : (primeUnder (𝓞 ↥K) W).adicCompletion ↥K,
            c ^ ℓ = algebraMap (↥K) ((primeUnder (𝓞 ↥K) W).adicCompletion ↥K) a) →
        ξ ∈ E := by
  classical
  haveI : IsGalois (↥K) N := IsGalois.tower_top_of_isGalois k (↥K) N
  obtain ⟨S, hSfin, hSsplit, hdetect⟩ :=
    exists_finite_splitsCompletelyIn_forall_stabilizer_fixed E T
  refine ⟨S, hSfin, hSsplit, fun a ξ ha hloc => hdetect ξ fun W hW σ hσ => ?_⟩
  have hfix : ∀ τ : ↥(stabilizer Gal(N/↥K) W), (τ : Gal(N/↥K)) ξ = ξ :=
    (forall_stabilizer_smul_eq_iff_exists_pow W hζ hℓ ha).2 (hloc W hW)
  have hσE : σ ∈ E.fixingSubgroup :=
    stabilizer_le_fixingSubgroup_of_splitsCompletelyIn E (hSsplit _ hW).2 rfl hσ
  have hσK : σ ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσE ⊢
    exact fun x hx => hσE x (hKE hx)
  have hres : (IntermediateField.fixingSubgroupEquiv K ⟨σ, hσK⟩).restrictScalars k = σ :=
    AlgEquiv.ext fun _ => rfl
  have hτW : IntermediateField.fixingSubgroupEquiv K ⟨σ, hσK⟩ ∈ stabilizer Gal(N/↥K) W := by
    refine mem_stabilizer_iff.mpr ?_
    rw [← restrictScalars_smul_heightOneSpectrum (k := k) _ W, hres]
    exact mem_stabilizer_iff.mp hσ
  exact hfix ⟨_, hτW⟩

end Member

end InverseGalois.CFT
