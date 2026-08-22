import Mathlib
import InverseGalois.CFT.Compositum
import InverseGalois.CFT.Disjoint
import InverseGalois.CFT.Scholz.Condition

/-!
# The split case of the Scholz–Reichardt induction

In the split case of Serre's Theorem 2.1.3 the group `G̃` to be realised is `G × C_ℓ`, and the
extension realising it is the compositum of the extension `A` already realising `G` with a cyclic
extension `B` of degree `ℓ`.  All the arithmetic is contained in the choice of the prime `q` at
which `B` ramifies: `q` must split completely in `A`, it must be congruent to one modulo `ℓ ^ M`,
and every prime ramified in `A` must split completely in `B`.

Given those three properties the compositum is controlled completely.  It is a compositum of two
linearly disjoint fields, so its Galois group is the product of the two; its ramified primes are
those of `A` together with `q`, one more prime; and it satisfies Serre's condition `(S_M)`, the
residue-degree half by the compositum theorem
`InverseGalois.CFT.isSplitInertia_of_sup` and the level half because `q` was chosen congruent to
one.

The statements below are phrased inside an ambient Galois number field `N` presented as the
compositum `A ⊔ B = ⊤` of two normal subextensions.

## Main results

* `InverseGalois.CFT.inf_eq_bot_of_scholzSplit`: the two factors are linearly disjoint.
* `InverseGalois.CFT.isScholz_of_scholzSplit`: **the compositum satisfies `(S_M)`.**
* `InverseGalois.CFT.isScholz_of_scholzSplit_of_isSplitInertia`: the same conclusion when the
  residue-degree half of the new factor is supplied directly.
* `InverseGalois.CFT.ramifiedSet_subset_of_scholzSplit`: the compositum is ramified at the primes
  of `A` and at `q`, and nowhere else.
* `InverseGalois.CFT.galEquivProdTop`: the Galois group of the compositum is the product of the
  two Galois groups.
* `InverseGalois.CFT.finrank_of_scholzSplit`: the degree is multiplied by `ℓ`.
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N]
variable (A B : IntermediateField ℚ N) [Normal ℚ ↥A] [Normal ℚ ↥B]

section Disjointness

variable {A B}

omit [IsGalois ℚ N] [Normal ℚ ↥A] [Normal ℚ ↥B] in
/-- **The two factors of the split case meet in `ℚ`.**  The new field ramifies only at `q`, and
`q` splits completely in the old one. -/
theorem inf_eq_bot_of_scholzSplit {q : ℕ} (hqA : SplitsCompletely ↥A q)
    (hBram : ramifiedSet ↥B ⊆ {q}) : A ⊓ B = ⊥ :=
  inf_eq_bot_of_splitsCompletely A B hqA hBram

end Disjointness

section Scholz

variable {A B}

omit [IsGalois ℚ N] [Normal ℚ ↥B] in
/-- **The new degree-`ℓ` factor satisfies Serre's condition `(S_M)`.**  Its only ramified prime is
`q`, which is congruent to one modulo `ℓ ^ M`, and a Galois extension of prime degree has residue
degree one at every ramified prime. -/
theorem isScholz_of_finrank_prime [IsGalois ℚ ↥B] {ℓ M q : ℕ} (hℓ : ℓ.Prime)
    (hBdeg : finrank ℚ ↥B = ℓ) (hBram : ramifiedSet ↥B ⊆ {q}) (hqlevel : q ≡ 1 [MOD ℓ ^ M]) :
    IsScholz ℓ M ↥B := by
  haveI : NumberField ↥B := ⟨⟩
  refine ⟨fun p hp => ?_, isSplitInertia_of_finrank_prime hℓ hBdeg⟩
  rw [Set.mem_singleton_iff.mp (hBram hp)]
  exact hqlevel

/-- **The compositum satisfies Serre's condition `(S_M)`.**  Every prime ramified in the old field
splits completely in the new one and conversely, so the compositum theorem applies to both halves
of the condition. -/
theorem isScholz_of_scholzSplit [IsGalois ℚ ↥B] {ℓ M q : ℕ} (hℓ : ℓ.Prime)
    (hAB : A ⊔ B = ⊤) (hA : IsScholz ℓ M ↥A) (hBdeg : finrank ℚ ↥B = ℓ)
    (hBram : ramifiedSet ↥B ⊆ {q}) (hqlevel : q ≡ 1 [MOD ℓ ^ M]) (hqA : SplitsCompletely ↥A q)
    (hsplit : ∀ p ∈ ramifiedSet ↥A, SplitsCompletely ↥B p) :
    IsScholz ℓ M N := by
  haveI : NumberField ↥A := ⟨⟩
  haveI : NumberField ↥B := ⟨⟩
  refine IsScholz.of_sup_eq_top A B hAB hA
    (isScholz_of_finrank_prime hℓ hBdeg hBram hqlevel) hsplit fun p hp => ?_
  rw [Set.mem_singleton_iff.mp (hBram hp)]
  exact hqA

omit [IsGalois ℚ N] [Normal ℚ ↥B] in
/-- **A field ramified at a single prime of level `M` and with split inertia satisfies `(S_M)`.**
This is the form of the previous statement in which the residue-degree half is supplied directly
rather than deduced from the degree being prime. -/
theorem isScholz_of_isSplitInertia {ℓ M q : ℕ} (hBsplit : IsSplitInertia ↥B)
    (hBram : ramifiedSet ↥B ⊆ {q}) (hqlevel : q ≡ 1 [MOD ℓ ^ M]) :
    IsScholz ℓ M ↥B := by
  haveI : NumberField ↥B := ⟨⟩
  refine ⟨fun p hp => ?_, hBsplit⟩
  rw [Set.mem_singleton_iff.mp (hBram hp)]
  exact hqlevel

/-- **The compositum satisfies Serre's condition `(S_M)`**, with the residue-degree half of the
new factor supplied directly.  This is the form of `InverseGalois.CFT.isScholz_of_scholzSplit`
that applies when the new factor is cyclic of prime-power degree rather than of prime degree. -/
theorem isScholz_of_scholzSplit_of_isSplitInertia {ℓ M q : ℕ} (hAB : A ⊔ B = ⊤)
    (hA : IsScholz ℓ M ↥A) (hBsplit : IsSplitInertia ↥B) (hBram : ramifiedSet ↥B ⊆ {q})
    (hqlevel : q ≡ 1 [MOD ℓ ^ M]) (hqA : SplitsCompletely ↥A q)
    (hsplit : ∀ p ∈ ramifiedSet ↥A, SplitsCompletely ↥B p) :
    IsScholz ℓ M N := by
  haveI : NumberField ↥A := ⟨⟩
  haveI : NumberField ↥B := ⟨⟩
  refine IsScholz.of_sup_eq_top A B hAB hA
    (isScholz_of_isSplitInertia hBsplit hBram hqlevel) hsplit fun p hp => ?_
  rw [Set.mem_singleton_iff.mp (hBram hp)]
  exact hqA

omit [IsGalois ℚ N] [Normal ℚ ↥A] [Normal ℚ ↥B] in
/-- **The compositum is ramified at one more prime than the old field.** -/
theorem ramifiedSet_subset_of_scholzSplit {q : ℕ} (hAB : A ⊔ B = ⊤)
    (hBram : ramifiedSet ↥B ⊆ {q}) : ramifiedSet N ⊆ ramifiedSet ↥A ∪ {q} := by
  haveI : NumberField ↥A := ⟨⟩
  haveI : NumberField ↥B := ⟨⟩
  intro p hp
  have hmem : p ∈ ramifiedSet ↥A ∪ ramifiedSet ↥B := by
    rw [← ramifiedSet_sup A B, hAB]
    rwa [ramifiedSet_eq_of_ringEquiv (IntermediateField.topEquiv (F := ℚ) (E := N)).toRingEquiv]
  exact hmem.imp id fun h => hBram h

end Scholz

section GaloisGroup

variable [IsGalois ℚ ↥A] [IsGalois ℚ ↥B]

/-- The compositum of two normal subextensions filling out the ambient field is that field. -/
noncomputable def supEquivTop (hAB : A ⊔ B = ⊤) : ↥(A ⊔ B) ≃ₐ[ℚ] N :=
  (IntermediateField.equivOfEq hAB).trans IntermediateField.topEquiv

/-- **The Galois group of the compositum is the product of the two Galois groups**, when the two
factors meet in `ℚ` and generate the ambient field. -/
noncomputable def galEquivProdTop (hAB : A ⊔ B = ⊤) (h : A ⊓ B = ⊥) :
    Gal(N/ℚ) ≃* Gal(↥A/ℚ) × Gal(↥B/ℚ) :=
  ((AlgEquiv.autCongr (supEquivTop A B hAB)).symm).trans (galEquivProd A B h)

omit [IsGalois ℚ N] [Normal ℚ ↥A] [Normal ℚ ↥B] [IsGalois ℚ ↥B] in
/-- **The degree of the compositum is the product of the two degrees.** -/
theorem finrank_of_scholzSplit (hAB : A ⊔ B = ⊤) (h : A ⊓ B = ⊥) :
    finrank ℚ N = finrank ℚ ↥A * finrank ℚ ↥B := by
  rw [← finrank_sup_of_inf_eq_bot A B h]
  exact ((supEquivTop A B hAB).toLinearEquiv.finrank_eq).symm

end GaloisGroup

end InverseGalois.CFT
