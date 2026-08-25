/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaRestrict
import InverseGalois.CFT.InertiaSubgroup
import InverseGalois.CFT.Scholz.Tame
import InverseGalois.CFT.Units.FrobeniusPlace

/-!
# Local invariants of a base change along a linearly disjoint factor

The local criterion for solving a central embedding problem is applied over the field obtained
from a number field `A` by adjoining the roots of unity, so its hypotheses have to be read off
from the arithmetic of `A` itself.  Both fields sit inside a common Galois number field `N`, and
what makes the transfer work is that restriction to `A` is injective on the Galois group of `N`
over the new base `k`: the two factors generate `N`, and an automorphism over `k` already fixes
`k` pointwise.

Under that injectivity every local invariant over `k` is bounded by the corresponding invariant of
`A` over `ℚ`.  A place of `N` unramified over `ℚ` in `A` is unramified over `k`; the decomposition
group over `k` embeds into the decomposition group of `A` over `ℚ`, so it is cyclic whenever the
latter is, and its order divides.  Combining this with Serre's condition `(S_N)` on `A` gives the
two group-theoretic hypotheses the criterion asks of every ramified place; the residue field of
the completion is prime because the prime below splits completely in the base field.

## Main definitions

* `InverseGalois.CFT.galRestrictOver`: restriction to `A` of an automorphism of `N` over `k`.
* `InverseGalois.CFT.baseSubfield`: the image of the base field inside `N`.
* `InverseGalois.CFT.stabilizerRestrictOver`: the induced map on decomposition groups.

## Main results

* `InverseGalois.CFT.galRestrictOver_injective`: **restriction to `A` is injective on the Galois
  group over `k`** when `A` and the base field generate `N`.
* `InverseGalois.CFT.isUnramifiedAt_base_of_inertia_eq_bot`: **a place with trivial inertia in `A`
  is unramified over `k`.**
* `InverseGalois.CFT.mem_ramifiedSet_of_not_isUnramifiedAt_base`: **a place ramified over `k` lies
  over a prime that ramifies in `A`.**
* `InverseGalois.CFT.isCyclic_stabilizer_base`, `InverseGalois.CFT.card_stabilizer_dvd_base`: the
  decomposition group over `k` is cyclic, of order dividing that of the decomposition group of `A`
  over `ℚ`.
* `InverseGalois.CFT.isCyclic_and_mul_card_stabilizer_dvd_base`,
  `InverseGalois.CFT.isCyclic_and_mul_card_stabilizer_dvd_base_place`: **the two group-theoretic
  hypotheses of the local criterion hold at every place ramified over `k`**, for a field `A`
  satisfying Serre's condition at level one more than the order of its Galois group.
* `InverseGalois.CFT.isCyclic_and_exists_hasResidueChar_base`: **the complete local hypothesis of
  the criterion for solving a central embedding problem**, at a place ramified over `k`.

## Tags

number field, base change, decomposition group, inertia group, ramification, cyclic
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField InverseGalois.NumberTheory

open scoped Pointwise

set_option synthInstance.maxHeartbeats 400000

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N]
  {k : Type*} [Field k] [NumberField k] [Algebra k N] [IsScalarTower ℚ k N] [IsGalois k N]

omit [IsGalois ℚ N] [IsGalois k N] in
/-- Restricting scalars does not change the action on the ring of integers. -/
theorem restrictScalars_smul (σ : Gal(N/k)) (x : 𝓞 N) :
    (σ.restrictScalars ℚ : Gal(N/ℚ)) • x = σ • x := rfl

omit [IsGalois ℚ N] [IsGalois k N] in
/-- Restricting scalars does not change the action on ideals of the ring of integers. -/
theorem restrictScalars_smul_ideal (σ : Gal(N/k)) (P : Ideal (𝓞 N)) :
    (σ.restrictScalars ℚ : Gal(N/ℚ)) • P = σ • P := rfl

variable (A : IntermediateField ℚ N) [Normal ℚ ↥A]

/-- **Restriction to a normal subextension of an automorphism over a larger base.**  An
automorphism of `N` over `k` is in particular one over `ℚ`, and `A` is normal over `ℚ`. -/
noncomputable def galRestrictOver : Gal(N/k) →* Gal(↥A/ℚ) where
  toFun σ := AlgEquiv.restrictNormalHom ↥A (σ.restrictScalars ℚ)
  map_one' := by
    rw [show AlgEquiv.restrictScalars ℚ (1 : Gal(N/k)) = 1 from rfl, map_one]
  map_mul' σ τ := by
    show AlgEquiv.restrictNormalHom ↥A ((σ * τ).restrictScalars ℚ) = _
    rw [show (σ * τ).restrictScalars ℚ = σ.restrictScalars ℚ * τ.restrictScalars ℚ from rfl,
      map_mul]

variable {A}

omit [IsGalois ℚ N] [IsGalois k N] in
/-- Restriction sends inertia over `k` into inertia over `ℚ`. -/
theorem galRestrictOver_mem_inertia (P : Ideal (𝓞 N)) {σ : Gal(N/k)}
    (hσ : σ ∈ Ideal.inertia Gal(N/k) P) :
    galRestrictOver A σ ∈ Ideal.inertia Gal(↥A/ℚ) (P.under (𝓞 ↥A)) :=
  restrictNormal_mem_inertia A P (σ := σ.restrictScalars ℚ) hσ

omit [IsGalois ℚ N] [IsGalois k N] in
/-- Restriction sends the decomposition group over `k` into the decomposition group over `ℚ`. -/
theorem galRestrictOver_mem_stabilizer (P : Ideal (𝓞 N)) {σ : Gal(N/k)}
    (hσ : σ ∈ stabilizer Gal(N/k) P) :
    galRestrictOver A σ ∈ stabilizer Gal(↥A/ℚ) (P.under (𝓞 ↥A)) :=
  restrictNormal_mem_stabilizer A P (σ := σ.restrictScalars ℚ) hσ

/-! ### Injectivity of the restriction -/

/-- **The image of the base field inside `N`**, viewed as a subextension of `ℚ`. -/
abbrev baseSubfield (F E : Type*) [Field F] [Field E] [Algebra ℚ F] [Algebra ℚ E] [Algebra F E]
    [IsScalarTower ℚ F E] : IntermediateField ℚ E :=
  IntermediateField.restrictScalars ℚ (⊥ : IntermediateField F E)

omit [IsGalois ℚ N] [IsGalois k N] in
/-- An automorphism over `k` fixes the image of `k` pointwise. -/
theorem mem_fixingSubgroup_baseSubfield (σ : Gal(N/k)) :
    (σ.restrictScalars ℚ : Gal(N/ℚ)) ∈ (baseSubfield k N).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_bot] at hx
  obtain ⟨y, rfl⟩ := hx
  exact σ.commutes y

omit [IsGalois ℚ N] [IsGalois k N] in
/-- **Restriction to `A` is injective on the Galois group over `k`** as soon as `A` and the base
field together generate `N`: an automorphism over `k` restricting trivially to `A` fixes both
factors pointwise, hence fixes their compositum. -/
theorem galRestrictOver_injective (hAB : A ⊔ baseSubfield k N = ⊤) :
    Function.Injective (galRestrictOver (k := k) A) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hmem : (σ.restrictScalars ℚ : Gal(N/ℚ)) ∈ (⊤ : IntermediateField ℚ N).fixingSubgroup := by
    rw [← hAB, IntermediateField.fixingSubgroup_sup]
    exact ⟨mem_fixingSubgroup_of_restrictNormal_eq_one hσ, mem_fixingSubgroup_baseSubfield σ⟩
  rw [IntermediateField.fixingSubgroup_top] at hmem
  have h1 : (σ.restrictScalars ℚ : Gal(N/ℚ)) = 1 := by simpa using hmem
  exact AlgEquiv.ext fun x => congrArg (fun τ : Gal(N/ℚ) => τ x) h1

/-! ### Unramifiedness -/

omit [IsGalois ℚ N] in
/-- **A place with trivial inertia in one factor is unramified over the other.**  An element of the
inertia group over `k` restricts to an element of the inertia group of `A`, hence restricts
trivially, hence is the identity. -/
theorem isUnramifiedAt_base_of_inertia_eq_bot
    (hinj : Function.Injective (galRestrictOver (k := k) A)) (P : Ideal (𝓞 N)) [P.IsPrime]
    (hP : P ≠ ⊥) (hA : Ideal.inertia Gal(↥A/ℚ) (P.under (𝓞 ↥A)) = ⊥) :
    Algebra.IsUnramifiedAt (𝓞 k) P := by
  refine (inertia_eq_bot_iff_isUnramifiedAt_base (k := k) P hP).mp ?_
  rw [eq_bot_iff]
  intro σ hσ
  refine Subgroup.mem_bot.mpr (hinj ?_)
  rw [map_one]
  exact Subgroup.mem_bot.mp (hA ▸ galRestrictOver_mem_inertia (A := A) P hσ)

/-- **A place ramified over `k` lies over a rational prime that ramifies in `A`.** -/
theorem mem_ramifiedSet_of_not_isUnramifiedAt_base
    (hinj : Function.Injective (galRestrictOver (k := k) A)) (P : Ideal (𝓞 N)) [P.IsPrime]
    (hP : P ≠ ⊥) {p : ℕ} (hp : p.Prime) [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hnr : ¬ Algebra.IsUnramifiedAt (𝓞 k) P) : p ∈ ramifiedSet ↥A := by
  haveI : NumberField ↥A := ⟨⟩
  haveI : IsGalois ℚ ↥A := ⟨⟩
  haveI : (P.under (𝓞 ↥A)).LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    rw [Ideal.under_under]
    exact Ideal.LiesOver.over
  by_contra hmem
  exact hnr (isUnramifiedAt_base_of_inertia_eq_bot hinj P hP
    (inertia_eq_bot_of_notMem_ramifiedSet hp (P.under (𝓞 ↥A)) hmem))

/-! ### Decomposition groups -/

variable (A) in
/-- **The restriction homomorphism on decomposition groups**, from the decomposition group over
the larger base `k` to the decomposition group of the prime below in `A`. -/
noncomputable def stabilizerRestrictOver (P : Ideal (𝓞 N)) :
    stabilizer Gal(N/k) P →* stabilizer Gal(↥A/ℚ) (P.under (𝓞 ↥A)) where
  toFun σ := ⟨galRestrictOver A σ.1, galRestrictOver_mem_stabilizer P σ.2⟩
  map_one' := Subtype.ext (map_one (galRestrictOver (k := k) A))
  map_mul' _ _ := Subtype.ext (map_mul (galRestrictOver (k := k) A) _ _)

omit [IsGalois ℚ N] [IsGalois k N] in
/-- Restriction is injective on decomposition groups as soon as it is injective on the whole
Galois group. -/
theorem stabilizerRestrictOver_injective
    (hinj : Function.Injective (galRestrictOver (k := k) A)) (P : Ideal (𝓞 N)) :
    Function.Injective (stabilizerRestrictOver (k := k) A P) := fun _ _ h =>
  Subtype.ext (hinj (congrArg Subtype.val h))

omit [IsGalois ℚ N] [IsGalois k N] in
/-- **The decomposition group over `k` is cyclic** whenever the decomposition group of the prime
below in `A` is. -/
theorem isCyclic_stabilizer_base (hinj : Function.Injective (galRestrictOver (k := k) A))
    (P : Ideal (𝓞 N)) (hA : IsCyclic ↥(stabilizer Gal(↥A/ℚ) (P.under (𝓞 ↥A)))) :
    IsCyclic ↥(stabilizer Gal(N/k) P) :=
  haveI := hA
  isCyclic_of_injective _ (stabilizerRestrictOver_injective hinj P)

omit [IsGalois ℚ N] [IsGalois k N] in
/-- **The order of the decomposition group over `k` divides** the order of the decomposition group
of the prime below in `A`. -/
theorem card_stabilizer_dvd_base (hinj : Function.Injective (galRestrictOver (k := k) A))
    (P : Ideal (𝓞 N)) :
    Nat.card ↥(stabilizer Gal(N/k) P) ∣
      Nat.card ↥(stabilizer Gal(↥A/ℚ) (P.under (𝓞 ↥A))) :=
  Subgroup.card_dvd_of_injective _ (stabilizerRestrictOver_injective hinj P)

/-! ### The hypotheses of the local criterion -/

/-- **The two group-theoretic hypotheses of the local criterion hold at every place ramified over
the new base.**  The decomposition group over `k` embeds into the decomposition group of `A` at the
prime below, which is cyclic of order dividing `ℓ ^ M` by Serre's condition, while the level
condition at `M + 1` makes `ℓ ^ (M + 1)` divide `p - 1`. -/
theorem isCyclic_and_mul_card_stabilizer_dvd_base
    (hinj : Function.Injective (galRestrictOver (k := k) A)) {ℓ M : ℕ} (hℓ : ℓ.Prime)
    (hG : IsPGroup ℓ Gal(↥A/ℚ)) (hs : IsScholz ℓ (M + 1) ↥A)
    (hdvd : Nat.card Gal(↥A/ℚ) ∣ ℓ ^ M) (P : Ideal (𝓞 N)) [P.IsPrime] (hP : P ≠ ⊥) {p : ℕ}
    (hp : p.Prime) [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hnr : ¬ Algebra.IsUnramifiedAt (𝓞 k) P) :
    IsCyclic ↥(stabilizer Gal(N/k) P) ∧
      ℓ * Nat.card ↥(stabilizer Gal(N/k) P) ∣ p - 1 := by
  haveI : NumberField ↥A := ⟨⟩
  haveI : IsGalois ℚ ↥A := ⟨⟩
  haveI : (P.under (𝓞 ↥A)).LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    rw [Ideal.under_under]
    exact Ideal.LiesOver.over
  have hmem : p ∈ ramifiedSet ↥A :=
    mem_ramifiedSet_of_not_isUnramifiedAt_base hinj P hP hp hnr
  refine ⟨isCyclic_stabilizer_base hinj P
    (IsScholz.isCyclic_stabilizer hℓ (Nat.succ_ne_zero M) hG hs hmem (P.under (𝓞 ↥A))), ?_⟩
  refine dvd_trans (mul_dvd_mul_left ℓ (card_stabilizer_dvd_base hinj P)) ?_
  exact mul_card_stabilizer_dvd_sub_one (IsScholz.isLevel hs) hdvd hmem (P.under (𝓞 ↥A))

/-- **The same two hypotheses, read at a finite place** rather than at a prime ideal, which is the
form in which the local criterion asks for them. -/
theorem isCyclic_and_mul_card_stabilizer_dvd_base_place
    (hinj : Function.Injective (galRestrictOver (k := k) A)) {ℓ M : ℕ} (hℓ : ℓ.Prime)
    (hG : IsPGroup ℓ Gal(↥A/ℚ)) (hs : IsScholz ℓ (M + 1) ↥A)
    (hdvd : Nat.card Gal(↥A/ℚ) ∣ ℓ ^ M) (v : HeightOneSpectrum (𝓞 N)) {p : ℕ} (hp : p.Prime)
    (hv : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
    (hnr : ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal) :
    IsCyclic ↥(stabilizer Gal(N/k) v) ∧
      ℓ * Nat.card ↥(stabilizer Gal(N/k) v) ∣ p - 1 := by
  haveI := v.isPrime
  haveI := hv
  rw [stabilizer_eq_stabilizer_asIdeal]
  exact isCyclic_and_mul_card_stabilizer_dvd_base hinj hℓ hG hs hdvd v.asIdeal v.ne_bot hp hnr

/-! ### The full local hypothesis -/

/-- **The complete local hypothesis of the criterion for solving a central embedding problem**, at
a place of `N` ramified over the base field.  Such a place lies over a rational prime that ramifies
in `A`, so Serre's condition makes its decomposition group in `A` cyclic, of order dividing
`ℓ ^ M`, and its residue degree one; the prime splits completely in the base field, so the residue
degree stays one in the compositum and the residue field of the completion is prime. -/
theorem isCyclic_and_exists_hasResidueChar_base [Normal ℚ ↥(baseSubfield k N)]
    (hAB : A ⊔ baseSubfield k N = ⊤) {ℓ M : ℕ} (hℓ : ℓ.Prime) (hG : IsPGroup ℓ Gal(↥A/ℚ))
    (hs : IsScholz ℓ (M + 1) ↥A) (hdvd : Nat.card Gal(↥A/ℚ) ∣ ℓ ^ M)
    (hsplit : ∀ p ∈ ramifiedSet ↥A, SplitsCompletely ↥(baseSubfield k N) p)
    (v : HeightOneSpectrum (𝓞 N)) (hnr : ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal) :
    IsCyclic ↥(stabilizer Gal(N/k) v) ∧ ∃ p e : ℕ,
      HasResidueChar (v.adicCompletion N) p e ∧
        (∀ x : v.adicCompletion N, Valued.v x ≤ 1 →
          ∃ b : ℤ, Valued.v (x - (b : v.adicCompletion N)) < 1) ∧
        ℓ * Nat.card ↥(stabilizer Gal(N/k) v) ∣ p - 1 := by
  haveI : NumberField ↥A := ⟨⟩
  haveI : IsGalois ℚ ↥A := ⟨⟩
  haveI := v.isPrime
  obtain ⟨p, hp, hlo⟩ := exists_prime_liesOver v
  haveI := hlo
  have hinj := galRestrictOver_injective hAB
  obtain ⟨hcyc, hdvd'⟩ :=
    isCyclic_and_mul_card_stabilizer_dvd_base_place hinj hℓ hG hs hdvd v hp hlo hnr
  refine ⟨hcyc, ?_⟩
  have hmem : p ∈ ramifiedSet ↥A :=
    mem_ramifiedSet_of_not_isUnramifiedAt_base hinj v.asIdeal v.ne_bot hp hnr
  haveI : (v.asIdeal.under (𝓞 ↥A)).LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    rw [Ideal.under_under]
    exact Ideal.LiesOver.over
  have hdeg : (Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal = 1 :=
    inertiaDeg_eq_one_of_sup A (baseSubfield k N) hAB hp v.asIdeal (hsplit p hmem)
      (hs.2 p hmem (v.asIdeal.under (𝓞 ↥A)) inferInstance inferInstance)
  exact exists_hasResidueChar_and_primeResidue hp v hdeg hdvd'

end InverseGalois.CFT
