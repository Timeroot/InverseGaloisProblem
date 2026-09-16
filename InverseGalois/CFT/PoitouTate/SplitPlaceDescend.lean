/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.SplitPlaceGenerate

/-!
# Finitely many completely split primes detect membership of an intermediate field

The decomposition groups at the primes lying above the primes of the base splitting completely in
an intermediate field generate the whole subgroup fixing that field, and a finite group is carried
by finitely many of its generators.  So **finitely many primes of the base already suffice**: an
element of the top field fixed by every decomposition group above them is fixed by everything
fixing the intermediate field, and therefore lies in it.

Phrasing the conclusion as membership of the intermediate field, and the hypothesis as a statement
about the decomposition groups rather than about the completions, keeps the whole statement inside
the Galois group of the top field: no place of the intermediate field and no completion appears.
The prescribed finite set of primes to avoid is there because the primes may have to be kept away
from a ramification locus, or from a place a prescription has already named.

## Main results

* `InverseGalois.CFT.exists_finite_splitsCompletelyIn_forall_stabilizer_fixed`: **finitely many
  primes of the base, splitting completely in an intermediate field and avoiding any prescribed
  finite set, detect membership of that field** through the decomposition groups above them.

## Tags

Chebotarev density theorem, completely split, decomposition group, intermediate field, Galois
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField NumberTheory

section Descend

variable {k N : Type*} [Field k] [NumberField k] [Field N] [NumberField N] [Algebra k N]
  [IsGalois k N]

/-- **Finitely many primes of the base, splitting completely in an intermediate field and avoiding
any prescribed finite set of primes, detect membership of that field.**

The decomposition groups above the completely split primes generate the subgroup fixing the
intermediate field, and finitely many of the primes of the base already carry that subgroup.  An
element of the top field fixed by each of the decomposition groups above them is then fixed by the
whole subgroup, so it lies in the field that subgroup fixes, which is the intermediate field. -/
theorem exists_finite_splitsCompletelyIn_forall_stabilizer_fixed (E : IntermediateField k N)
    [NumberField ↥E] [IsGalois k ↥E] (T : Finset (HeightOneSpectrum (𝓞 k))) :
    ∃ S : Set (HeightOneSpectrum (𝓞 k)), S.Finite ∧
      (∀ v ∈ S, v ∉ T ∧ SplitsCompletelyIn k ↥E v) ∧
      ∀ ξ : N, (∀ P : HeightOneSpectrum (𝓞 N), primeUnder (𝓞 k) P ∈ S →
        ∀ σ ∈ stabilizer Gal(N/k) P, σ ξ = ξ) → ξ ∈ E := by
  classical
  obtain ⟨S, hSsub, hSfin, hSle⟩ := exists_finite_subset_decompositionSubgroupAbove (N := N)
    {v : HeightOneSpectrum (𝓞 k) | v ∉ T ∧ SplitsCompletelyIn k ↥E v}
  have hgen : E.fixingSubgroup ≤ decompositionSubgroupAbove k N S :=
    le_trans (fixingSubgroup_le_decompositionSubgroupAbove E T (fun _ hv => hv.2)
      (fun _ hvT hv => Set.mem_setOf.mpr ⟨hvT, hv⟩)) hSle
  refine ⟨S, hSfin, fun v hv => hSsub hv, fun ξ hξ => ?_⟩
  have hstab : decompositionSubgroupAbove k N S ≤ stabilizer Gal(N/k) ξ :=
    decompositionSubgroupAbove_le fun σ hσ => by
      obtain ⟨P, hPS, hPσ⟩ := mem_decompositionSetAbove.mp hσ
      exact hξ P hPS σ (mem_stabilizer_iff.mpr hPσ)
  have hmem : ξ ∈ IntermediateField.fixedField E.fixingSubgroup :=
    MulAction.mem_fixedPoints.2 fun σ => hstab (hgen σ.2)
  rwa [IsGalois.fixedField_fixingSubgroup] at hmem

end Descend

end InverseGalois.CFT
