/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.Units.DecompositionField
import InverseGalois.CFT.Units.TowerCoboundary

/-!
# Moving the decomposition field of a level

Let `k ⊆ K ⊆ L` be a tower of number fields with `K` normal over `k` and `L` normal over `K`, and
let `Q` be a prime of `L`.  The decomposition field of `Q` over `K` is the subfield of `L` fixed by
the decomposition group of `Q` in the Galois group over `K`, and it embeds into the completion of
`K` at the prime below `Q`.  An automorphism of `L` over `k` fixing `Q` restricts to an
automorphism of `K` over `k` fixing the prime below, and **the two automorphisms are compatible
with that embedding**: moving an element of the decomposition field and then reading it in the
completion of `K` is reading it in the completion and then moving it there.

The compatibility rests on a single membership criterion.  An element of the completion of `L`
comes from the completion of `K` exactly when the decomposition group over `K` fixes it, so an
element of `L` lies in the decomposition field exactly when its image in the completion of `L`
comes from the completion of `K`; the image of a moved element is the moved image, and the
transport of the completions along the tower carries the completion of `K` to itself.  This gives
at once that the decomposition field is stable under every automorphism fixing the prime, and that
the embedding intertwines the two actions.

The point of the statement is that the decomposition field of a prime is the level-by-level
approximation to the fixed field of a decomposition subgroup of an infinite extension, and a local
condition on a cohomology class at a place is a condition on the decomposition subgroup there;
the equivariance is what lets the condition be read on the completion.

## Main results

* `InverseGalois.CFT.mem_decompositionField_iff_mem_range`: **an element lies in the decomposition
  field exactly when its image in the completion comes from the completion of the base.**
* `InverseGalois.CFT.algebraMap_stabilizerRestrictPlace_smul`: **the embedding of the completion of
  the middle field intertwines the action of the decomposition group above with the action of the
  decomposition group below.**
* `InverseGalois.CFT.smul_mem_decompositionField`: **the decomposition field of a level is stable
  under every automorphism fixing the prime.**
* `InverseGalois.CFT.decompositionFieldHom_smul`: **the embedding of the decomposition field into
  the completion of the level is equivariant** for the decomposition group above and its
  restriction to the level.

## Tags

number field, tower, completion, decomposition group, decomposition field, Galois action
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### The decomposition field inside the completion -/

section Range

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **An element of the extension lies in the decomposition field exactly when its image in the
completion comes from the completion of the base.**  The decomposition group fixes an element of
the completion exactly when the element comes from the completion of the base, and it fixes the
image of an element of the extension exactly when it fixes the element itself. -/
theorem mem_decompositionField_iff_mem_range {x : K} :
    x ∈ decompositionField k w ↔ toAdicCompletion w x ∈
      Set.range (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)) := by
  rw [← mem_range_algebraMap_iff_forall_stabilizer_smul_eq k w, mem_decompositionField_iff k w]
  refine ⟨fun h σ => ?_, fun h σ => ?_⟩
  · rw [stabilizer_smul_toAdicCompletion, h σ]
  · exact (toAdicCompletion w).injective (by rw [← stabilizer_smul_toAdicCompletion]; exact h σ)

end Range

/-! ### Moving the decomposition field along a tower -/

section Tower

variable {k K L : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
  [IsGalois k K] [IsGalois K L] (Q : HeightOneSpectrum (𝓞 L))

omit [NumberField k] [IsGalois K L] in
/-- **The embedding of the completion of the middle field into the completion of the top field
intertwines the two decomposition-group actions**: transporting an element of the completion below
and then moving it by an automorphism fixing the prime above is moving it by the restricted
automorphism and then transporting it. -/
theorem algebraMap_stabilizerRestrictPlace_smul (σ : ↥(stabilizer Gal(L/k) Q))
    (c : (primeUnder (𝓞 K) Q).adicCompletion K) :
    algebraMap ((primeUnder (𝓞 K) Q).adicCompletion K) (Q.adicCompletion L)
        (stabilizerRestrictPlace K Q σ • c)
      = σ • algebraMap ((primeUnder (𝓞 K) Q).adicCompletion K) (Q.adicCompletion L) c := by
  rw [algebraMap_adicCompletion K Q, stabilizer_smul_adicCompletion_def,
    stabilizer_smul_adicCompletion_def]
  exact (adicCompletionAut_adicCompletionComap_restrict K Q σ.1 (mem_stabilizer_iff.mp σ.2) c).symm

omit [NumberField k] in
/-- **The decomposition field of a level is stable under every automorphism of the top field
fixing the prime.**  The image of the element in the completion comes from the completion of the
level, and the image of the moved element is the transport of a moved element there. -/
theorem smul_mem_decompositionField (σ : ↥(stabilizer Gal(L/k) Q)) {x : L}
    (hx : x ∈ decompositionField K Q) : (σ : Gal(L/k)) x ∈ decompositionField K Q := by
  rw [mem_decompositionField_iff_mem_range K Q] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  exact ⟨stabilizerRestrictPlace K Q σ • c, by
    rw [algebraMap_stabilizerRestrictPlace_smul Q σ c, hc, stabilizer_smul_toAdicCompletion Q σ x]⟩

omit [NumberField k] in
/-- **The embedding of the decomposition field of a level into the completion of the level is
equivariant** for the decomposition group at the prime above and its restriction to the level:
both sides have the same image in the completion of the top field. -/
theorem decompositionFieldHom_smul (σ : ↥(stabilizer Gal(L/k) Q))
    (x : ↥(decompositionField K Q)) :
    decompositionFieldHom K Q ⟨(σ : Gal(L/k)) (x : L), smul_mem_decompositionField Q σ x.2⟩
      = stabilizerRestrictPlace K Q σ • decompositionFieldHom K Q x := by
  refine (algebraMap ((primeUnder (𝓞 K) Q).adicCompletion K) (Q.adicCompletion L)).injective ?_
  rw [algebraMap_decompositionFieldHom K Q, algebraMap_stabilizerRestrictPlace_smul Q σ,
    algebraMap_decompositionFieldHom K Q, stabilizer_smul_toAdicCompletion Q σ]

end Tower

end InverseGalois.CFT
