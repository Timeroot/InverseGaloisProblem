import Mathlib
import InverseGalois.CFT.Cyclotomic.BuildingBlock

/-!
# Number fields with disjoint ramification are linearly disjoint

Two number fields inside a common field whose sets of ramified rational primes are disjoint
intersect in `ℚ`: the intersection is a number field whose ramified primes are ramified in both,
hence unramified everywhere, hence `ℚ` by Minkowski's theorem.  This is the mechanism that keeps
the auxiliary extensions of the Scholz–Reichardt induction independent from the field already
constructed, and it is what turns a supply of extensions ramified at one large prime into a supply
of *linearly disjoint* extensions.

## Main results

* `InverseGalois.CFT.finrank_eq_one_of_ramifiedSet_eq_empty`: an everywhere unramified number
  field is `ℚ`, phrased through the set of ramified rational primes.
* `InverseGalois.CFT.finrank_eq_one_of_ramifiedSet_disjoint`: a number field lying inside two
  number fields with disjoint ramification is `ℚ`.
* `InverseGalois.CFT.inf_eq_bot_of_ramifiedSet_disjoint`: the same for two intermediate fields of
  a number field.
* `InverseGalois.CFT.notMem_ramifiedSet_of_splitsCompletely`: a prime that splits completely is
  unramified.
* `InverseGalois.CFT.ramifiedSet_subset_singleton`: a field unramified away from one prime has
  that prime as its only ramified prime.
* `InverseGalois.CFT.inf_eq_bot_of_splitsCompletely`: the combination used in practice — a field
  in which `q` splits completely meets a field ramified only at `q` in `ℚ`.
* `InverseGalois.CFT.inf_eq_bot_of_ramifiedSet_disjoint'` and
  `InverseGalois.CFT.inf_eq_bot_of_splitsCompletely'`: the same two statements for intermediate
  fields of an arbitrary extension of `ℚ`, only the two fields themselves being number fields.
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Everywhere unramified means rational -/

/-- **Minkowski's theorem**, phrased through the set of ramified rational primes: a number field
in which no rational prime ramifies is `ℚ`. -/
theorem finrank_eq_one_of_ramifiedSet_eq_empty (E : Type*) [Field E] [NumberField E]
    (h : ramifiedSet E = ∅) : finrank ℚ E = 1 := by
  by_contra hne
  have hlt : 1 < finrank ℚ E :=
    lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne') (Ne.symm hne)
  obtain ⟨P, hPprime, hP0, hPram⟩ := exists_ne_bot_isPrime_not_isUnramifiedAt E hlt
  haveI := hPprime
  haveI : NeZero P := ⟨hP0⟩
  have hover : Ideal.span {((Ideal.absNorm (Ideal.under ℤ P) : ℕ) : ℤ)} = Ideal.under ℤ P :=
    Ideal.LiesOver.over
  refine Set.eq_empty_iff_forall_notMem.mp h (Ideal.absNorm (Ideal.under ℤ P)) ?_
  refine ⟨Nat.absNorm_under_prime P, P, ⟨hPprime, inferInstance⟩, fun he => hPram ?_⟩
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0, ← hover]
  exact he

/-- A number field mapping into two number fields with disjoint ramification is `ℚ`. -/
theorem finrank_eq_one_of_ramifiedSet_disjoint (E A B : Type*) [Field E] [NumberField E]
    [Field A] [NumberField A] [Field B] [NumberField B] [Algebra E A] [Algebra E B]
    (h : Disjoint (ramifiedSet A) (ramifiedSet B)) : finrank ℚ E = 1 := by
  refine finrank_eq_one_of_ramifiedSet_eq_empty E (Set.eq_empty_iff_forall_notMem.mpr ?_)
  exact fun p hp =>
    Set.disjoint_left.mp h (ramifiedSet_subset E A hp) (ramifiedSet_subset E B hp)

/-- **Two intermediate fields with disjoint ramification meet in `ℚ`.** -/
theorem inf_eq_bot_of_ramifiedSet_disjoint {L : Type*} [Field L] [NumberField L]
    (A B : IntermediateField ℚ L) (h : Disjoint (ramifiedSet A) (ramifiedSet B)) : A ⊓ B = ⊥ := by
  letI : Algebra ↥(A ⊓ B) ↥A := (IntermediateField.inclusion inf_le_left).toAlgebra
  letI : Algebra ↥(A ⊓ B) ↥B := (IntermediateField.inclusion inf_le_right).toAlgebra
  exact IntermediateField.finrank_eq_one_iff.mp
    (finrank_eq_one_of_ramifiedSet_disjoint ↥(A ⊓ B) ↥A ↥B h)

/-! ### Recognising disjoint ramification -/

/-- A rational prime that splits completely in a number field is unramified there. -/
theorem notMem_ramifiedSet_of_splitsCompletely {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (h : SplitsCompletely K p) : p ∉ ramifiedSet K := by
  rintro ⟨-, P, hPmem, hPe⟩
  exact hPe (h P hPmem).1

/-- A number field unramified at every nonzero prime not containing `q` is ramified at most at
the rational prime `q`. -/
theorem ramifiedSet_subset_singleton {F : Type*} [Field F] [NumberField F] {q : ℕ} (hq : q.Prime)
    (hunr : ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime], Q ≠ ⊥ → (q : 𝓞 F) ∉ Q →
      Algebra.IsUnramifiedAt ℤ Q) :
    ramifiedSet F ⊆ {q} := by
  rintro p ⟨hp, P, ⟨hPprime, hPover⟩, hPe⟩
  haveI := hPprime
  haveI := hPover
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_natCast hp hPover
  have hram : ¬ Algebra.IsUnramifiedAt ℤ P := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0, ← hPover.over]
    exact hPe
  have hmem : (q : 𝓞 F) ∈ P := by
    by_contra hmem
    exact hram (hunr P hP0 hmem)
  exact eq_of_natCast_mem hp hq hPover hmem

/-- **The disjointness criterion used in practice.**  A field in which the prime `q` splits
completely meets a field ramified only at `q` in `ℚ`. -/
theorem inf_eq_bot_of_splitsCompletely {L : Type*} [Field L] [NumberField L]
    (A B : IntermediateField ℚ L) {q : ℕ} (hA : SplitsCompletely (↥A) q)
    (hB : ramifiedSet ↥B ⊆ {q}) : A ⊓ B = ⊥ := by
  refine inf_eq_bot_of_ramifiedSet_disjoint A B (Set.disjoint_right.mpr fun p hp hpA => ?_)
  rw [Set.mem_singleton_iff.mp (hB hp)] at hpA
  exact notMem_ramifiedSet_of_splitsCompletely hA hpA

/-! ### Disjoint ramification inside an arbitrary extension of `ℚ` -/

/-- **Two intermediate fields with disjoint ramification meet in `ℚ`.**  Unlike
`InverseGalois.CFT.inf_eq_bot_of_ramifiedSet_disjoint`, the ambient field is not required to be
a number field, only the two intermediate fields themselves. -/
theorem inf_eq_bot_of_ramifiedSet_disjoint' {L : Type*} [Field L] [CharZero L]
    (A B : IntermediateField ℚ L) [NumberField A] [NumberField B]
    (h : Disjoint (ramifiedSet A) (ramifiedSet B)) : A ⊓ B = ⊥ := by
  haveI : FiniteDimensional ℚ ↥(A ⊓ B) := by
    have hincl := IntermediateField.inclusion (inf_le_left : A ⊓ B ≤ A)
    exact FiniteDimensional.of_injective hincl.toLinearMap hincl.injective
  haveI : NumberField ↥(A ⊓ B) := ⟨⟩
  letI : Algebra ↥(A ⊓ B) ↥A := (IntermediateField.inclusion inf_le_left).toAlgebra
  letI : Algebra ↥(A ⊓ B) ↥B := (IntermediateField.inclusion inf_le_right).toAlgebra
  exact IntermediateField.finrank_eq_one_iff.mp
    (finrank_eq_one_of_ramifiedSet_disjoint ↥(A ⊓ B) ↥A ↥B h)

/-- **The disjointness criterion, over an arbitrary ambient extension of `ℚ`.**  A field in which
the prime `q` splits completely meets a field ramified only at `q` in `ℚ`. -/
theorem inf_eq_bot_of_splitsCompletely' {L : Type*} [Field L] [CharZero L]
    (A B : IntermediateField ℚ L) [NumberField A] [NumberField B] {q : ℕ}
    (hA : SplitsCompletely (↥A) q) (hB : ramifiedSet ↥B ⊆ {q}) : A ⊓ B = ⊥ := by
  refine inf_eq_bot_of_ramifiedSet_disjoint' A B (Set.disjoint_right.mpr fun p hp hpA => ?_)
  rw [Set.mem_singleton_iff.mp (hB hp)] at hpA
  exact notMem_ramifiedSet_of_splitsCompletely hA hpA

end InverseGalois.CFT
