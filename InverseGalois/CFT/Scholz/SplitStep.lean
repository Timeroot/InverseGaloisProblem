import Mathlib
import InverseGalois.CFT.Cyclotomic.CyclotomicInertiaDeg
import InverseGalois.CFT.Cyclotomic.DivisorSubfield
import InverseGalois.CFT.Cyclotomic.FrobeniusSplitting
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.Scholz.PrimeChoice
import InverseGalois.CFT.Scholz.SplitCase

/-!
# One split step of the Scholz–Reichardt induction

Let `L` be a Galois number field satisfying Serre's condition `(S_N)` for the prime `ℓ`.  This
file builds a Galois number field `M` containing `L` whose Galois group is the product of that of
`L` with a cyclic group of order `ℓ ^ e`, which again satisfies `(S_N)`, and which is ramified at
exactly one prime more than `L`.

The construction is the classical one.  A prime `q` is chosen that splits completely in `L`, is
congruent to one modulo `ℓ ^ N` and modulo `ℓ ^ e`, and has every prime ramified in `L` among its
`ℓ ^ e`-th power residues; such primes are infinite in number.  The cyclotomic field `ℚ(ζ_q)` then
contains a cyclic extension of `ℚ` of degree `ℓ ^ e`, ramified only at `q`, in which a rational
prime `p ≠ q` splits completely exactly when `p ^ ((q - 1) / ℓ ^ e) = 1` modulo `q`, that is,
exactly when `p` is an `ℓ ^ e`-th power residue.  The two fields are placed inside
`AlgebraicClosure ℚ` and `M` is their compositum: `q` splits completely in `L`, so the two are
linearly disjoint, and the primes ramified in `L` split completely in the new factor, so Serre's
condition survives.  The residue-degree half of the condition for the new factor comes from the
conductor being totally ramified in `ℚ(ζ_q)`.

## Main definitions

* `InverseGalois.CFT.stepPrime`: the prime at which the new factor ramifies.
* `InverseGalois.CFT.stepAux`: the degree-`ℓ ^ e` subfield of `ℚ(ζ_q)`.
* `InverseGalois.CFT.stepField`: the compositum `M`.

## Main results

* `InverseGalois.CFT.isScholz_stepField`: **the compositum satisfies `(S_N)`.**
* `InverseGalois.CFT.ramifiedSet_stepField`: it is ramified at the primes of `L` and at `q` only.
* `InverseGalois.CFT.finrank_stepField`: its degree is `ℓ ^ e` times that of `L`.
* `InverseGalois.CFT.galEquivStepField`: **its Galois group is `Gal(L/ℚ) × C_{ℓ ^ e}`.**
* `InverseGalois.CFT.nonempty_algHom_stepField`: it contains a copy of `L`.
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable (L : Type*) [Field L] [NumberField L] {ℓ : ℕ} (hℓ : ℓ.Prime) (N e : ℕ)

/-! ### The branching prime -/

/-- The prime at which the new factor of the compositum ramifies: it splits completely in `L`, is
congruent to one modulo `ℓ ^ N` and modulo `ℓ ^ e`, and admits every prime ramified in `L` as an
`ℓ ^ e`-th power residue. -/
noncomputable def stepPrime : ℕ := (exists_scholzPrime_notMem L hℓ N e).choose

/-- The defining properties of the branching prime. -/
theorem stepPrime_spec :
    (stepPrime L hℓ N e).Prime ∧ stepPrime L hℓ N e ∉ ramifiedSet L ∧
      SplitsCompletely L (stepPrime L hℓ N e) ∧ ℓ ^ e ∣ stepPrime L hℓ N e - 1 ∧
      ℓ ^ N ∣ stepPrime L hℓ N e - 1 ∧
      ∀ p ∈ ramifiedSet L, ∃ y : ZMod (stepPrime L hℓ N e),
        y ^ ℓ ^ e = (p : ZMod (stepPrime L hℓ N e)) :=
  (exists_scholzPrime_notMem L hℓ N e).choose_spec

/-- The branching prime is prime. -/
theorem prime_stepPrime : (stepPrime L hℓ N e).Prime := (stepPrime_spec L hℓ N e).1

instance fact_prime_stepPrime : Fact (stepPrime L hℓ N e).Prime := ⟨prime_stepPrime L hℓ N e⟩

/-- The branching prime is unramified in `L`. -/
theorem stepPrime_notMem_ramifiedSet : stepPrime L hℓ N e ∉ ramifiedSet L :=
  (stepPrime_spec L hℓ N e).2.1

/-- The branching prime splits completely in `L`. -/
theorem splitsCompletely_stepPrime : SplitsCompletely L (stepPrime L hℓ N e) :=
  (stepPrime_spec L hℓ N e).2.2.1

/-- The branching prime is congruent to one modulo `ℓ ^ e`. -/
theorem deg_dvd_stepPrime_sub_one : ℓ ^ e ∣ stepPrime L hℓ N e - 1 :=
  (stepPrime_spec L hℓ N e).2.2.2.1

/-- The branching prime is congruent to one modulo `ℓ ^ N`. -/
theorem level_dvd_stepPrime_sub_one : ℓ ^ N ∣ stepPrime L hℓ N e - 1 :=
  (stepPrime_spec L hℓ N e).2.2.2.2.1

/-- The branching prime has level `N`. -/
theorem stepPrime_modEq : stepPrime L hℓ N e ≡ 1 [MOD ℓ ^ N] :=
  ((Nat.modEq_iff_dvd' (prime_stepPrime L hℓ N e).one_le).mpr
    (level_dvd_stepPrime_sub_one L hℓ N e)).symm

/-- Every prime ramified in `L` is an `ℓ ^ e`-th power residue modulo the branching prime. -/
theorem exists_pow_eq_stepPrime {p : ℕ} (hp : p ∈ ramifiedSet L) :
    ∃ y : ZMod (stepPrime L hℓ N e), y ^ ℓ ^ e = (p : ZMod (stepPrime L hℓ N e)) :=
  (stepPrime_spec L hℓ N e).2.2.2.2.2 p hp

/-! ### The new factor -/

/-- The degree-`ℓ ^ e` subfield of the cyclotomic field of the branching prime. -/
noncomputable def stepAux : IntermediateField ℚ (CyclotomicField (stepPrime L hℓ N e) ℚ) :=
  (exists_intermediateField_finrank_eq_pow_and_splitsCompletely (stepPrime L hℓ N e) hℓ
    (deg_dvd_stepPrime_sub_one L hℓ N e) (CyclotomicField (stepPrime L hℓ N e) ℚ)).choose

/-- The defining properties of the new factor. -/
theorem stepAux_spec :
    finrank ℚ ↥(stepAux L hℓ N e) = ℓ ^ e ∧ IsGalois ℚ ↥(stepAux L hℓ N e) ∧
      IsCyclic Gal(↥(stepAux L hℓ N e)/ℚ) ∧
      (∀ p : ℕ, p.Prime → p ≠ stepPrime L hℓ N e →
        (SplitsCompletely ↥(stepAux L hℓ N e) p ↔
          (p : ZMod (stepPrime L hℓ N e)) ^ ((stepPrime L hℓ N e - 1) / ℓ ^ e) = 1)) ∧
      (∀ (Q : Ideal (𝓞 ↥(stepAux L hℓ N e))) [Q.IsPrime], Q ≠ ⊥ →
        ((stepPrime L hℓ N e : ℕ) : 𝓞 ↥(stepAux L hℓ N e)) ∉ Q → Algebra.IsUnramifiedAt ℤ Q) :=
  (exists_intermediateField_finrank_eq_pow_and_splitsCompletely (stepPrime L hℓ N e) hℓ
    (deg_dvd_stepPrime_sub_one L hℓ N e) (CyclotomicField (stepPrime L hℓ N e) ℚ)).choose_spec

/-- The new factor has degree `ℓ ^ e`. -/
theorem finrank_stepAux : finrank ℚ ↥(stepAux L hℓ N e) = ℓ ^ e := (stepAux_spec L hℓ N e).1

instance isGalois_stepAux : IsGalois ℚ ↥(stepAux L hℓ N e) := (stepAux_spec L hℓ N e).2.1

instance isCyclic_gal_stepAux : IsCyclic Gal(↥(stepAux L hℓ N e)/ℚ) :=
  (stepAux_spec L hℓ N e).2.2.1

/-- The splitting law in the new factor: a rational prime other than the branching prime splits
completely exactly when it is an `ℓ ^ e`-th power residue. -/
theorem splitsCompletely_stepAux_iff {p : ℕ} (hp : p.Prime) (hpq : p ≠ stepPrime L hℓ N e) :
    SplitsCompletely ↥(stepAux L hℓ N e) p ↔
      (p : ZMod (stepPrime L hℓ N e)) ^ ((stepPrime L hℓ N e - 1) / ℓ ^ e) = 1 :=
  (stepAux_spec L hℓ N e).2.2.2.1 p hp hpq

/-- The new factor is ramified at the branching prime only. -/
theorem ramifiedSet_stepAux : ramifiedSet ↥(stepAux L hℓ N e) ⊆ {stepPrime L hℓ N e} :=
  ramifiedSet_subset_singleton (prime_stepPrime L hℓ N e)
    fun Q _ h1 h2 => (stepAux_spec L hℓ N e).2.2.2.2 Q h1 h2

/-- **The new factor has split inertia.**  Its only ramified prime is the conductor of the
cyclotomic field it sits inside, and the conductor is totally ramified there, so its residue
degree is one in every subfield. -/
theorem isSplitInertia_stepAux : IsSplitInertia ↥(stepAux L hℓ N e) := by
  intro p hp P hPprime hPover
  obtain rfl := Set.mem_singleton_iff.mp (ramifiedSet_stepAux L hℓ N e hp)
  haveI := hPprime
  haveI := hPover
  exact inertiaDeg_eq_one_of_intermediateField_cyclotomic (stepPrime L hℓ N e)
    (CyclotomicField (stepPrime L hℓ N e) ℚ) (stepAux L hℓ N e) P

/-! ### The compositum -/

variable [IsGalois ℚ L]

/-- The compositum, inside `AlgebraicClosure ℚ`, of a copy of `L` with a copy of the new
factor. -/
noncomputable def stepField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  embSubfield L ⊔ embSubfield ↥(stepAux L hℓ N e)

instance finiteDimensional_stepField : FiniteDimensional ℚ ↥(stepField L hℓ N e) := by
  unfold stepField
  infer_instance

instance numberField_stepField : NumberField ↥(stepField L hℓ N e) := ⟨⟩

instance isGalois_stepField : IsGalois ℚ ↥(stepField L hℓ N e) := by
  unfold stepField
  infer_instance

/-- The copy of `L`, viewed as an intermediate field of the compositum. -/
noncomputable def innerOld : IntermediateField ℚ ↥(stepField L hℓ N e) :=
  IntermediateField.restrict (le_sup_left : embSubfield L ≤ stepField L hℓ N e)

/-- The copy of the new factor, viewed as an intermediate field of the compositum. -/
noncomputable def innerNew : IntermediateField ℚ ↥(stepField L hℓ N e) :=
  IntermediateField.restrict
    (le_sup_right : embSubfield ↥(stepAux L hℓ N e) ≤ stepField L hℓ N e)

omit [IsGalois ℚ L] in
/-- The two factors generate the compositum. -/
theorem innerOld_sup_innerNew : innerOld L hℓ N e ⊔ innerNew L hℓ N e = ⊤ :=
  restrict_sup_restrict (embSubfield L) (embSubfield ↥(stepAux L hℓ N e))

/-- The inner copy of `L` really is a copy of `L`. -/
noncomputable def innerOldEquiv : L ≃ₐ[ℚ] ↥(innerOld L hℓ N e) :=
  (embEquiv L).trans (IntermediateField.restrict_algEquiv _)

/-- The inner copy of the new factor really is a copy of it. -/
noncomputable def innerNewEquiv : ↥(stepAux L hℓ N e) ≃ₐ[ℚ] ↥(innerNew L hℓ N e) :=
  (embEquiv ↥(stepAux L hℓ N e)).trans (IntermediateField.restrict_algEquiv _)

instance normal_innerOld : Normal ℚ ↥(innerOld L hℓ N e) :=
  Normal.of_algEquiv (innerOldEquiv L hℓ N e)

instance normal_innerNew : Normal ℚ ↥(innerNew L hℓ N e) :=
  Normal.of_algEquiv (innerNewEquiv L hℓ N e)

instance isGalois_innerOld : IsGalois ℚ ↥(innerOld L hℓ N e) := ⟨⟩

instance isGalois_innerNew : IsGalois ℚ ↥(innerNew L hℓ N e) := ⟨⟩

/-! ### The properties of the two factors inside the compositum -/

omit [IsGalois ℚ L] in
/-- The inner copy of `L` has the same ramified primes as `L`. -/
theorem ramifiedSet_innerOld : ramifiedSet ↥(innerOld L hℓ N e) = ramifiedSet L :=
  (ramifiedSet_eq_of_ringEquiv (innerOldEquiv L hℓ N e).toRingEquiv).symm

omit [IsGalois ℚ L] in
/-- The inner copy of the new factor is ramified at the branching prime only. -/
theorem ramifiedSet_innerNew : ramifiedSet ↥(innerNew L hℓ N e) ⊆ {stepPrime L hℓ N e} := by
  rw [← ramifiedSet_eq_of_ringEquiv (innerNewEquiv L hℓ N e).toRingEquiv]
  exact ramifiedSet_stepAux L hℓ N e

omit [IsGalois ℚ L] in
/-- The inner copy of the new factor has split inertia. -/
theorem isSplitInertia_innerNew : IsSplitInertia ↥(innerNew L hℓ N e) :=
  isSplitInertia_of_ringEquiv (innerNewEquiv L hℓ N e).toRingEquiv (isSplitInertia_stepAux L hℓ N e)

omit [IsGalois ℚ L] in
/-- The new factor has degree `ℓ ^ e` inside the compositum. -/
theorem finrank_innerNew : finrank ℚ ↥(innerNew L hℓ N e) = ℓ ^ e := by
  rw [← (innerNewEquiv L hℓ N e).toLinearEquiv.finrank_eq]
  exact finrank_stepAux L hℓ N e

omit [IsGalois ℚ L] in
/-- The branching prime splits completely in the inner copy of `L`. -/
theorem splitsCompletely_innerOld :
    SplitsCompletely ↥(innerOld L hℓ N e) (stepPrime L hℓ N e) :=
  (splitsCompletely_algEquiv_iff (innerOldEquiv L hℓ N e) (prime_stepPrime L hℓ N e)).mp
    (splitsCompletely_stepPrime L hℓ N e)

omit [IsGalois ℚ L] in
/-- **Every prime ramified in `L` splits completely in the new factor.**  It is an `ℓ ^ e`-th power
residue modulo the branching prime, hence killed by the exponent `(q - 1) / ℓ ^ e`, and the
splitting law of the degree-`ℓ ^ e` subfield of `ℚ(ζ_q)` applies. -/
theorem splitsCompletely_innerNew {p : ℕ} (hp : p ∈ ramifiedSet ↥(innerOld L hℓ N e)) :
    SplitsCompletely ↥(innerNew L hℓ N e) p := by
  rw [ramifiedSet_innerOld] at hp
  have hpp : p.Prime := hp.1
  have hpq : p ≠ stepPrime L hℓ N e := fun h => stepPrime_notMem_ramifiedSet L hℓ N e (h ▸ hp)
  haveI : Fact (stepPrime L hℓ N e).Prime := fact_prime_stepPrime L hℓ N e
  have hne : (p : ZMod (stepPrime L hℓ N e)) ≠ 0 := by
    intro hc
    exact hpq ((Nat.prime_dvd_prime_iff_eq (prime_stepPrime L hℓ N e) hpp).mp
      ((ZMod.natCast_eq_zero_iff _ _).mp hc)).symm
  have hpow := pow_div_eq_one_of_exists_pow_eq (prime_stepPrime L hℓ N e)
    (deg_dvd_stepPrime_sub_one L hℓ N e) hne (exists_pow_eq_stepPrime L hℓ N e hp)
  exact (splitsCompletely_algEquiv_iff (innerNewEquiv L hℓ N e) hpp).mp
    ((splitsCompletely_stepAux_iff L hℓ N e hpp hpq).mpr hpow)

omit [IsGalois ℚ L] in
/-- The two factors of the compositum meet in `ℚ`. -/
theorem inf_innerOld_innerNew : innerOld L hℓ N e ⊓ innerNew L hℓ N e = ⊥ :=
  inf_eq_bot_of_splitsCompletely _ _ (splitsCompletely_innerOld L hℓ N e)
    (ramifiedSet_innerNew L hℓ N e)

/-! ### The conclusions -/

/-- **The compositum satisfies Serre's condition `(S_N)`.** -/
theorem isScholz_stepField (hL : IsScholz ℓ N L) : IsScholz ℓ N ↥(stepField L hℓ N e) :=
  isScholz_of_scholzSplit_of_isSplitInertia (innerOld_sup_innerNew L hℓ N e)
    (IsScholz.of_ringEquiv (innerOldEquiv L hℓ N e).toRingEquiv hL)
    (isSplitInertia_innerNew L hℓ N e) (ramifiedSet_innerNew L hℓ N e) (stepPrime_modEq L hℓ N e)
    (splitsCompletely_innerOld L hℓ N e) fun _ hp => splitsCompletely_innerNew L hℓ N e hp

omit [IsGalois ℚ L] in
/-- **The compositum is ramified at one prime more than `L`.** -/
theorem ramifiedSet_stepField :
    ramifiedSet ↥(stepField L hℓ N e) ⊆ ramifiedSet L ∪ {stepPrime L hℓ N e} := by
  rw [← ramifiedSet_innerOld L hℓ N e]
  exact ramifiedSet_subset_of_scholzSplit (innerOld_sup_innerNew L hℓ N e)
    (ramifiedSet_innerNew L hℓ N e)

/-- **The degree of the compositum is `ℓ ^ e` times the degree of `L`.** -/
theorem finrank_stepField : finrank ℚ ↥(stepField L hℓ N e) = finrank ℚ L * ℓ ^ e := by
  rw [finrank_of_scholzSplit (innerOld L hℓ N e) (innerNew L hℓ N e)
      (innerOld_sup_innerNew L hℓ N e) (inf_innerOld_innerNew L hℓ N e),
    finrank_innerNew L hℓ N e, (innerOldEquiv L hℓ N e).toLinearEquiv.finrank_eq]

/-- **The Galois group of the compositum is the product of that of `L` with the Galois group of
the new factor**, a cyclic group of order `ℓ ^ e`. -/
noncomputable def galEquivStepField :
    Gal(↥(stepField L hℓ N e)/ℚ) ≃* Gal(L/ℚ) × Gal(↥(stepAux L hℓ N e)/ℚ) :=
  (galEquivProdTop (innerOld L hℓ N e) (innerNew L hℓ N e) (innerOld_sup_innerNew L hℓ N e)
    (inf_innerOld_innerNew L hℓ N e)).trans
      (MulEquiv.prodCongr (AlgEquiv.autCongr (innerOldEquiv L hℓ N e)).symm
        (AlgEquiv.autCongr (innerNewEquiv L hℓ N e)).symm)

omit [IsGalois ℚ L] in
/-- The Galois group of the new factor has order `ℓ ^ e`. -/
theorem card_gal_stepAux : Nat.card Gal(↥(stepAux L hℓ N e)/ℚ) = ℓ ^ e := by
  rw [IsGalois.card_aut_eq_finrank ℚ ↥(stepAux L hℓ N e)]
  exact finrank_stepAux L hℓ N e

omit [IsGalois ℚ L] in
/-- **The compositum contains a copy of `L`.** -/
theorem nonempty_algHom_stepField : Nonempty (L →ₐ[ℚ] ↥(stepField L hℓ N e)) :=
  ⟨(innerOld L hℓ N e).val.comp (innerOldEquiv L hℓ N e).toAlgHom⟩

end InverseGalois.CFT
