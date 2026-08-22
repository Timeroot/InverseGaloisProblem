import Mathlib
import InverseGalois.CFT.Cyclotomic.FrobeniusSplitting
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.Scholz.PrimeChoice
import InverseGalois.CFT.Scholz.SplitCase

/-!
# One split step of the Scholz–Reichardt induction

Let `L` be a Galois number field satisfying Serre's condition `(S_N)` for the prime `ℓ`.  This
file builds a Galois number field `M` containing `L` whose Galois group is the product of that of
`L` with a group of order `ℓ`, which again satisfies `(S_N)`, and which is ramified at exactly one
prime more than `L`.

The construction is the classical one.  A prime `q` is chosen that splits completely in `L`, is
congruent to one modulo `ℓ ^ N`, and has every prime ramified in `L` among its `ℓ`-th power
residues; such primes are infinite in number.  The cyclotomic field `ℚ(ζ_q)` then contains a
Galois extension of `ℚ` of degree `ℓ`, ramified only at `q`, in which a rational prime `p ≠ q`
splits completely exactly when `p ^ ((q - 1) / ℓ) = 1` modulo `q`, that is, exactly when `p` is an
`ℓ`-th power residue.  The two fields are placed inside `AlgebraicClosure ℚ` and `M` is their
compositum: `q` splits completely in `L`, so the two are linearly disjoint, and the primes
ramified in `L` split completely in the new factor, so Serre's condition survives.

## Main definitions

* `InverseGalois.CFT.stepPrime`: the prime at which the new factor ramifies.
* `InverseGalois.CFT.stepAux`: the degree-`ℓ` subfield of `ℚ(ζ_q)`.
* `InverseGalois.CFT.stepField`: the compositum `M`.

## Main results

* `InverseGalois.CFT.isScholz_stepField`: **the compositum satisfies `(S_N)`.**
* `InverseGalois.CFT.ramifiedSet_stepField`: it is ramified at the primes of `L` and at `q` only.
* `InverseGalois.CFT.finrank_stepField`: its degree is `ℓ` times that of `L`.
* `InverseGalois.CFT.galEquivStepField`: **its Galois group is `Gal(L/ℚ) × C_ℓ`.**
* `InverseGalois.CFT.nonempty_algHom_stepField`: it contains a copy of `L`.
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable (L : Type*) [Field L] [NumberField L] {ℓ : ℕ} (hℓ : ℓ.Prime) (N : ℕ)

/-! ### The branching prime -/

/-- The prime at which the new factor of the compositum ramifies: it splits completely in `L`, is
congruent to one modulo `ℓ ^ N`, and admits every prime ramified in `L` as an `ℓ`-th power
residue. -/
noncomputable def stepPrime : ℕ := (exists_scholzPrime_notMem L hℓ N).choose

/-- The defining properties of the branching prime. -/
theorem stepPrime_spec :
    (stepPrime L hℓ N).Prime ∧ stepPrime L hℓ N ∉ ramifiedSet L ∧
      SplitsCompletely L (stepPrime L hℓ N) ∧ ℓ ∣ stepPrime L hℓ N - 1 ∧
      ℓ ^ N ∣ stepPrime L hℓ N - 1 ∧
      ∀ p ∈ ramifiedSet L, ∃ y : ZMod (stepPrime L hℓ N),
        y ^ ℓ = (p : ZMod (stepPrime L hℓ N)) :=
  (exists_scholzPrime_notMem L hℓ N).choose_spec

/-- The branching prime is prime. -/
theorem prime_stepPrime : (stepPrime L hℓ N).Prime := (stepPrime_spec L hℓ N).1

instance fact_prime_stepPrime : Fact (stepPrime L hℓ N).Prime := ⟨prime_stepPrime L hℓ N⟩

/-- The branching prime is unramified in `L`. -/
theorem stepPrime_notMem_ramifiedSet : stepPrime L hℓ N ∉ ramifiedSet L :=
  (stepPrime_spec L hℓ N).2.1

/-- The branching prime splits completely in `L`. -/
theorem splitsCompletely_stepPrime : SplitsCompletely L (stepPrime L hℓ N) :=
  (stepPrime_spec L hℓ N).2.2.1

/-- The branching prime is congruent to one modulo `ℓ`. -/
theorem dvd_stepPrime_sub_one : ℓ ∣ stepPrime L hℓ N - 1 := (stepPrime_spec L hℓ N).2.2.2.1

/-- The branching prime is congruent to one modulo `ℓ ^ N`. -/
theorem pow_dvd_stepPrime_sub_one : ℓ ^ N ∣ stepPrime L hℓ N - 1 :=
  (stepPrime_spec L hℓ N).2.2.2.2.1

/-- The branching prime has level `N`. -/
theorem stepPrime_modEq : stepPrime L hℓ N ≡ 1 [MOD ℓ ^ N] :=
  ((Nat.modEq_iff_dvd' (prime_stepPrime L hℓ N).one_le).mpr
    (pow_dvd_stepPrime_sub_one L hℓ N)).symm

/-- Every prime ramified in `L` is an `ℓ`-th power residue modulo the branching prime. -/
theorem exists_pow_eq_stepPrime {p : ℕ} (hp : p ∈ ramifiedSet L) :
    ∃ y : ZMod (stepPrime L hℓ N), y ^ ℓ = (p : ZMod (stepPrime L hℓ N)) :=
  (stepPrime_spec L hℓ N).2.2.2.2.2 p hp

/-! ### The new factor -/

/-- The degree-`ℓ` subfield of the cyclotomic field of the branching prime. -/
noncomputable def stepAux : IntermediateField ℚ (CyclotomicField (stepPrime L hℓ N) ℚ) :=
  (exists_intermediateField_finrank_eq_prime_and_splitsCompletely (stepPrime L hℓ N) hℓ
    (dvd_stepPrime_sub_one L hℓ N) (CyclotomicField (stepPrime L hℓ N) ℚ)).choose

/-- The defining properties of the new factor. -/
theorem stepAux_spec :
    finrank ℚ ↥(stepAux L hℓ N) = ℓ ∧ IsGalois ℚ ↥(stepAux L hℓ N) ∧
      (∀ p : ℕ, p.Prime → p ≠ stepPrime L hℓ N →
        (SplitsCompletely ↥(stepAux L hℓ N) p ↔
          (p : ZMod (stepPrime L hℓ N)) ^ ((stepPrime L hℓ N - 1) / ℓ) = 1)) ∧
      (∀ (Q : Ideal (𝓞 ↥(stepAux L hℓ N))) [Q.IsPrime], Q ≠ ⊥ →
        ((stepPrime L hℓ N : ℕ) : 𝓞 ↥(stepAux L hℓ N)) ∉ Q → Algebra.IsUnramifiedAt ℤ Q) ∧
      ∃ Q : Ideal (𝓞 ↥(stepAux L hℓ N)), ∃ _ : Q.IsPrime, Q ≠ ⊥ ∧
        ((stepPrime L hℓ N : ℕ) : 𝓞 ↥(stepAux L hℓ N)) ∈ Q ∧ ¬ Algebra.IsUnramifiedAt ℤ Q :=
  (exists_intermediateField_finrank_eq_prime_and_splitsCompletely (stepPrime L hℓ N) hℓ
    (dvd_stepPrime_sub_one L hℓ N) (CyclotomicField (stepPrime L hℓ N) ℚ)).choose_spec

/-- The new factor has degree `ℓ`. -/
theorem finrank_stepAux : finrank ℚ ↥(stepAux L hℓ N) = ℓ := (stepAux_spec L hℓ N).1

instance isGalois_stepAux : IsGalois ℚ ↥(stepAux L hℓ N) := (stepAux_spec L hℓ N).2.1

/-- The splitting law in the new factor: a rational prime other than the branching prime splits
completely exactly when it is an `ℓ`-th power residue. -/
theorem splitsCompletely_stepAux_iff {p : ℕ} (hp : p.Prime) (hpq : p ≠ stepPrime L hℓ N) :
    SplitsCompletely ↥(stepAux L hℓ N) p ↔
      (p : ZMod (stepPrime L hℓ N)) ^ ((stepPrime L hℓ N - 1) / ℓ) = 1 :=
  (stepAux_spec L hℓ N).2.2.1 p hp hpq

/-- The new factor is ramified at the branching prime only. -/
theorem ramifiedSet_stepAux : ramifiedSet ↥(stepAux L hℓ N) ⊆ {stepPrime L hℓ N} :=
  ramifiedSet_subset_singleton (prime_stepPrime L hℓ N)
    fun Q _ h1 h2 => (stepAux_spec L hℓ N).2.2.2.1 Q h1 h2

/-! ### The compositum -/

variable [IsGalois ℚ L]

/-- The compositum, inside `AlgebraicClosure ℚ`, of a copy of `L` with a copy of the new
factor. -/
noncomputable def stepField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  embSubfield L ⊔ embSubfield ↥(stepAux L hℓ N)

instance finiteDimensional_stepField : FiniteDimensional ℚ ↥(stepField L hℓ N) := by
  unfold stepField
  infer_instance

instance numberField_stepField : NumberField ↥(stepField L hℓ N) := ⟨⟩

instance isGalois_stepField : IsGalois ℚ ↥(stepField L hℓ N) := by
  unfold stepField
  infer_instance

/-- The copy of `L`, viewed as an intermediate field of the compositum. -/
noncomputable def innerOld : IntermediateField ℚ ↥(stepField L hℓ N) :=
  IntermediateField.restrict (le_sup_left : embSubfield L ≤ stepField L hℓ N)

/-- The copy of the new factor, viewed as an intermediate field of the compositum. -/
noncomputable def innerNew : IntermediateField ℚ ↥(stepField L hℓ N) :=
  IntermediateField.restrict
    (le_sup_right : embSubfield ↥(stepAux L hℓ N) ≤ stepField L hℓ N)

omit [IsGalois ℚ L] in
/-- The two factors generate the compositum. -/
theorem innerOld_sup_innerNew : innerOld L hℓ N ⊔ innerNew L hℓ N = ⊤ :=
  restrict_sup_restrict (embSubfield L) (embSubfield ↥(stepAux L hℓ N))

/-- The inner copy of `L` really is a copy of `L`. -/
noncomputable def innerOldEquiv : L ≃ₐ[ℚ] ↥(innerOld L hℓ N) :=
  (embEquiv L).trans (IntermediateField.restrict_algEquiv _)

/-- The inner copy of the new factor really is a copy of it. -/
noncomputable def innerNewEquiv : ↥(stepAux L hℓ N) ≃ₐ[ℚ] ↥(innerNew L hℓ N) :=
  (embEquiv ↥(stepAux L hℓ N)).trans (IntermediateField.restrict_algEquiv _)

instance normal_innerOld : Normal ℚ ↥(innerOld L hℓ N) :=
  Normal.of_algEquiv (innerOldEquiv L hℓ N)

instance normal_innerNew : Normal ℚ ↥(innerNew L hℓ N) :=
  Normal.of_algEquiv (innerNewEquiv L hℓ N)

instance isGalois_innerOld : IsGalois ℚ ↥(innerOld L hℓ N) := ⟨⟩

instance isGalois_innerNew : IsGalois ℚ ↥(innerNew L hℓ N) := ⟨⟩

/-! ### The properties of the two factors inside the compositum -/

omit [IsGalois ℚ L] in
/-- The inner copy of `L` has the same ramified primes as `L`. -/
theorem ramifiedSet_innerOld : ramifiedSet ↥(innerOld L hℓ N) = ramifiedSet L :=
  (ramifiedSet_eq_of_ringEquiv (innerOldEquiv L hℓ N).toRingEquiv).symm

omit [IsGalois ℚ L] in
/-- The inner copy of the new factor is ramified at the branching prime only. -/
theorem ramifiedSet_innerNew : ramifiedSet ↥(innerNew L hℓ N) ⊆ {stepPrime L hℓ N} := by
  rw [← ramifiedSet_eq_of_ringEquiv (innerNewEquiv L hℓ N).toRingEquiv]
  exact ramifiedSet_stepAux L hℓ N

omit [IsGalois ℚ L] in
/-- The new factor has degree `ℓ` inside the compositum. -/
theorem finrank_innerNew : finrank ℚ ↥(innerNew L hℓ N) = ℓ := by
  rw [← (innerNewEquiv L hℓ N).toLinearEquiv.finrank_eq]
  exact finrank_stepAux L hℓ N

omit [IsGalois ℚ L] in
/-- The branching prime splits completely in the inner copy of `L`. -/
theorem splitsCompletely_innerOld : SplitsCompletely ↥(innerOld L hℓ N) (stepPrime L hℓ N) :=
  (splitsCompletely_algEquiv_iff (innerOldEquiv L hℓ N) (prime_stepPrime L hℓ N)).mp
    (splitsCompletely_stepPrime L hℓ N)

omit [IsGalois ℚ L] in
/-- **Every prime ramified in `L` splits completely in the new factor.**  It is an `ℓ`-th power
residue modulo the branching prime, hence killed by the exponent `(q - 1) / ℓ`, and the splitting
law of the degree-`ℓ` subfield of `ℚ(ζ_q)` applies. -/
theorem splitsCompletely_innerNew {p : ℕ} (hp : p ∈ ramifiedSet ↥(innerOld L hℓ N)) :
    SplitsCompletely ↥(innerNew L hℓ N) p := by
  rw [ramifiedSet_innerOld] at hp
  have hpp : p.Prime := hp.1
  have hpq : p ≠ stepPrime L hℓ N := fun h => stepPrime_notMem_ramifiedSet L hℓ N (h ▸ hp)
  haveI : Fact (stepPrime L hℓ N).Prime := fact_prime_stepPrime L hℓ N
  have hne : (p : ZMod (stepPrime L hℓ N)) ≠ 0 := by
    intro hc
    exact hpq ((Nat.prime_dvd_prime_iff_eq (prime_stepPrime L hℓ N) hpp).mp
      ((ZMod.natCast_eq_zero_iff _ _).mp hc)).symm
  have hpow := pow_div_eq_one_of_exists_pow_eq (prime_stepPrime L hℓ N)
    (dvd_stepPrime_sub_one L hℓ N) hne (exists_pow_eq_stepPrime L hℓ N hp)
  exact (splitsCompletely_algEquiv_iff (innerNewEquiv L hℓ N) hpp).mp
    ((splitsCompletely_stepAux_iff L hℓ N hpp hpq).mpr hpow)

omit [IsGalois ℚ L] in
/-- The two factors of the compositum meet in `ℚ`. -/
theorem inf_innerOld_innerNew : innerOld L hℓ N ⊓ innerNew L hℓ N = ⊥ :=
  inf_eq_bot_of_splitsCompletely _ _ (splitsCompletely_innerOld L hℓ N)
    (ramifiedSet_innerNew L hℓ N)

/-! ### The conclusions -/

/-- **The compositum satisfies Serre's condition `(S_N)`.** -/
theorem isScholz_stepField (hL : IsScholz ℓ N L) : IsScholz ℓ N ↥(stepField L hℓ N) :=
  isScholz_of_scholzSplit hℓ (innerOld_sup_innerNew L hℓ N)
    (IsScholz.of_ringEquiv (innerOldEquiv L hℓ N).toRingEquiv hL) (finrank_innerNew L hℓ N)
    (ramifiedSet_innerNew L hℓ N) (stepPrime_modEq L hℓ N) (splitsCompletely_innerOld L hℓ N)
    fun _ hp => splitsCompletely_innerNew L hℓ N hp

omit [IsGalois ℚ L] in
/-- **The compositum is ramified at one prime more than `L`.** -/
theorem ramifiedSet_stepField :
    ramifiedSet ↥(stepField L hℓ N) ⊆ ramifiedSet L ∪ {stepPrime L hℓ N} := by
  rw [← ramifiedSet_innerOld L hℓ N]
  exact ramifiedSet_subset_of_scholzSplit (innerOld_sup_innerNew L hℓ N)
    (ramifiedSet_innerNew L hℓ N)

/-- **The degree of the compositum is `ℓ` times the degree of `L`.** -/
theorem finrank_stepField : finrank ℚ ↥(stepField L hℓ N) = finrank ℚ L * ℓ := by
  rw [finrank_of_scholzSplit (innerOld L hℓ N) (innerNew L hℓ N) (innerOld_sup_innerNew L hℓ N)
      (inf_innerOld_innerNew L hℓ N), finrank_innerNew L hℓ N,
    (innerOldEquiv L hℓ N).toLinearEquiv.finrank_eq]

/-- **The Galois group of the compositum is the product of that of `L` with the Galois group of
the new factor**, a group of order `ℓ`. -/
noncomputable def galEquivStepField :
    Gal(↥(stepField L hℓ N)/ℚ) ≃* Gal(L/ℚ) × Gal(↥(stepAux L hℓ N)/ℚ) :=
  (galEquivProdTop (innerOld L hℓ N) (innerNew L hℓ N) (innerOld_sup_innerNew L hℓ N)
    (inf_innerOld_innerNew L hℓ N)).trans
      (MulEquiv.prodCongr (AlgEquiv.autCongr (innerOldEquiv L hℓ N)).symm
        (AlgEquiv.autCongr (innerNewEquiv L hℓ N)).symm)

omit [IsGalois ℚ L] in
/-- The Galois group of the new factor has order `ℓ`. -/
theorem card_gal_stepAux : Nat.card Gal(↥(stepAux L hℓ N)/ℚ) = ℓ := by
  rw [IsGalois.card_aut_eq_finrank ℚ ↥(stepAux L hℓ N)]
  exact finrank_stepAux L hℓ N

omit [IsGalois ℚ L] in
/-- **The compositum contains a copy of `L`.** -/
theorem nonempty_algHom_stepField : Nonempty (L →ₐ[ℚ] ↥(stepField L hℓ N)) :=
  ⟨(innerOld L hℓ N).val.comp (innerOldEquiv L hℓ N).toAlgHom⟩

end InverseGalois.CFT
