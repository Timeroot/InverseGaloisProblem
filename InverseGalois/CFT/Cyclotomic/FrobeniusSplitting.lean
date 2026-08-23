/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Decomposition
import InverseGalois.CFT.Cyclotomic.Chebotarev
import InverseGalois.CFT.Cyclotomic.CyclicSubfield
import InverseGalois.CFT.Cyclotomic.OnePrimeRamified
import InverseGalois.CFT.Cyclotomic.Splitting

/-!
# The Frobenius criterion for splitting completely

Let `K` be a number field Galois over `ℚ` and let `P` be a prime of `𝓞 K` above a rational prime
`p`.  The decomposition of `p` is read off from the decomposition group of `P`: the ramification
index is the order of the inertia subgroup and, once inertia is trivial, the residue degree is the
order of the arithmetic Frobenius.  Hence `p` splits completely in `K` exactly when the Frobenius
at `P` is the identity, the primes above `p` being conjugate and therefore all carrying the same
invariants.

Passing to an intermediate field `F` with `F / ℚ` normal, the Frobenius at the prime of `𝓞 F` below
`P` is the restriction of the Frobenius at `P`.  Consequently `p` splits completely in `F` exactly
when the Frobenius at `P` fixes `F` pointwise, that is, exactly when it lies in the subgroup of
`Gal(K/ℚ)` corresponding to `F`.

Applied to `K = ℚ(ζ_q)` for a prime `q`, whose Galois group is cyclic of order `q - 1` and is
identified with `(ℤ/qℤ)ˣ` in such a way that the Frobenius at `p` becomes the class of `p`, this
gives the classical splitting law for the unique subfield of degree `ℓ` of `ℚ(ζ_q)`, for `ℓ` a
prime divisor of `q - 1`: a rational prime `p ≠ q` splits completely in it if and only if `p` is an
`ℓ`-th power modulo `q`, that is, if and only if `p ^ ((q - 1) / ℓ) = 1` in `ZMod q`.

## Main results

* `InverseGalois.CFT.splitsCompletely_iff_of_liesOver`: splitting completely is detected at a single
  prime above `p`.
* `InverseGalois.CFT.eq_arithFrobAt_of_isArithFrobAt`: at an unramified prime the Frobenius element
  is unique.
* `InverseGalois.CFT.splitsCompletely_iff_arithFrobAt_eq_one`: at an unramified prime, `p` splits
  completely if and only if the arithmetic Frobenius is trivial.
* `InverseGalois.CFT.splitsCompletely_iff_inertia_eq_bot_and_arithFrobAt_eq_one`: the same criterion
  with no unramifiedness hypothesis, the triviality of inertia becoming part of the condition.
* `InverseGalois.CFT.splitsCompletely_intermediateField_iff` and
  `InverseGalois.CFT.splitsCompletely_intermediateField_iff_mem_fixingSubgroup`: a rational prime
  splits completely in a normal intermediate field exactly when the Frobenius restricts to the
  identity there, equivalently when it lies in the fixing subgroup of that field.
* `InverseGalois.CFT.exists_intermediateField_finrank_eq_prime_and_splitsCompletely`: for a prime
  `q` and a prime `ℓ` dividing `q - 1`, the cyclotomic field `ℚ(ζ_q)` contains a Galois extension
  of `ℚ` of degree `ℓ`, ramified exactly at `q`, in which a rational prime `p ≠ q` splits completely
  precisely when `p ^ ((q - 1) / ℓ) = 1` in `ZMod q`.
-/

open NumberField IsCyclotomicExtension InverseGalois.NumberTheory

namespace InverseGalois.CFT

attribute [local instance] Int.ideal_span_isMaximal_of_prime

/-! ### The criterion over the top field -/

section TopField

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **Splitting completely is a condition at a single prime.**  In a Galois extension the primes
above a rational prime are conjugate, so their ramification indices agree and their residue degrees
agree; it therefore suffices to test the two invariants at one prime above `p`. -/
theorem splitsCompletely_iff_of_liesOver (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    SplitsCompletely K p ↔
      Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P = 1 ∧
        (Ideal.span {(p : ℤ)}).inertiaDeg P = 1 := by
  constructor
  · intro h
    exact h P ⟨inferInstance, inferInstance⟩
  · rintro ⟨he, hf⟩ P' ⟨h1, h2⟩
    haveI : P'.IsPrime := h1
    haveI : P'.LiesOver (Ideal.span {(p : ℤ)}) := h2
    exact ⟨(Ideal.ramificationIdx_eq_of_isGaloisGroup _ P' P Gal(K/ℚ)).trans he,
      (Ideal.inertiaDeg_eq_of_isGaloisGroup _ P' P Gal(K/ℚ)).trans hf⟩

/-- **At an unramified prime the Frobenius element is unique.**  Two Frobenius elements at the same
prime differ by an element of the inertia group, which is trivial. -/
theorem eq_arithFrobAt_of_isArithFrobAt (P : Ideal (𝓞 K)) [P.IsPrime] [Finite (𝓞 K ⧸ P)]
    (hPne : P ≠ ⊥) (hunr : Algebra.IsUnramifiedAt ℤ P) {σ : Gal(K/ℚ)}
    (hσ : IsArithFrobAt ℤ σ P) : σ = arithFrobAt ℤ Gal(K/ℚ) P := by
  have h := hσ.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt ℤ Gal(K/ℚ) P)
  rw [(inertia_eq_bot_iff_isUnramifiedAt P hPne).mpr hunr, Subgroup.mem_bot,
    mul_inv_eq_one] at h
  exact h

/-- **The Frobenius criterion for splitting completely.**  A rational prime `p` unramified in a
Galois number field `K` splits completely in `K` if and only if the arithmetic Frobenius at a prime
of `𝓞 K` above `p` is the identity, that Frobenius having order the residue degree. -/
theorem splitsCompletely_iff_arithFrobAt_eq_one (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 K)) [P.IsPrime] [Finite (𝓞 K ⧸ P)] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hunr : Algebra.IsUnramifiedAt ℤ P) :
    SplitsCompletely K p ↔ arithFrobAt ℤ Gal(K/ℚ) P = 1 := by
  have hPne : P ≠ ⊥ := ne_bot_of_liesOver p P
  have hover : Ideal.span {(p : ℤ)} = P.under ℤ := Ideal.over_def P _
  have he : Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (P.under ℤ) P = 1 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ) hPne).mp hunr
  rw [splitsCompletely_iff_of_liesOver p P, arithFrobAt_eq_one_iff P hPne hunr, hover,
    and_iff_right he]

/-- **The Frobenius criterion, with no unramifiedness hypothesis.**  A rational prime splits
completely in a Galois number field exactly when, at a prime above it, both the inertia group and
the arithmetic Frobenius are trivial. -/
theorem splitsCompletely_iff_inertia_eq_bot_and_arithFrobAt_eq_one (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 K)) [P.IsPrime] [Finite (𝓞 K ⧸ P)] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    SplitsCompletely K p ↔
      Ideal.inertia Gal(K/ℚ) P = ⊥ ∧ arithFrobAt ℤ Gal(K/ℚ) P = 1 := by
  have hPne : P ≠ ⊥ := ne_bot_of_liesOver p P
  constructor
  · intro h
    have hunr : Algebra.IsUnramifiedAt ℤ P := by
      rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ) hPne,
        ← Ideal.over_def P (Ideal.span {(p : ℤ)})]
      exact (h P ⟨inferInstance, inferInstance⟩).1
    exact ⟨(inertia_eq_bot_iff_isUnramifiedAt P hPne).mpr hunr,
      (splitsCompletely_iff_arithFrobAt_eq_one p P hunr).mp h⟩
  · rintro ⟨hi, hf⟩
    exact (splitsCompletely_iff_arithFrobAt_eq_one p P
      ((inertia_eq_bot_iff_isUnramifiedAt P hPne).mp hi)).mpr hf

/-- **The Frobenius criterion for an arbitrary Frobenius element.**  At an unramified prime any
element of the Galois group which is a Frobenius at that prime detects splitting completely by
being trivial. -/
theorem splitsCompletely_iff_eq_one_of_isArithFrobAt (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 K)) [P.IsPrime] [Finite (𝓞 K ⧸ P)] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hunr : Algebra.IsUnramifiedAt ℤ P) {σ : Gal(K/ℚ)} (hσ : IsArithFrobAt ℤ σ P) :
    SplitsCompletely K p ↔ σ = 1 := by
  rw [splitsCompletely_iff_arithFrobAt_eq_one p P hunr,
    eq_arithFrobAt_of_isArithFrobAt P (ne_bot_of_liesOver p P) hunr hσ]

/-- **The Frobenius criterion for an intermediate field.**  A rational prime unramified in `K`
splits completely in a normal intermediate field `F` exactly when the arithmetic Frobenius at a
prime of `𝓞 K` above `p` restricts to the identity of `F`; the restriction is a Frobenius at the
prime of `𝓞 F` underneath. -/
theorem splitsCompletely_intermediateField_iff (F : IntermediateField ℚ K) [Normal ℚ F]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsPrime] [Finite (𝓞 K ⧸ P)]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (hunr : Algebra.IsUnramifiedAt ℤ P) :
    SplitsCompletely F p ↔ AlgEquiv.restrictNormalHom F (arithFrobAt ℤ Gal(K/ℚ) P) = 1 := by
  haveI : IsGalois ℚ ↥F := ⟨⟩
  haveI : Algebra.IsUnramifiedAt ℤ P := hunr
  haveI : (P.under (𝓞 F)).LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨by rw [Ideal.under_under]; exact Ideal.over_def P _⟩
  haveI : Algebra.IsUnramifiedAt ℤ (P.under (𝓞 F)) :=
    Algebra.IsUnramifiedAt.of_liesOver ℤ (P.under (𝓞 F)) P
  haveI : Finite (𝓞 F ⧸ P.under (𝓞 F)) :=
    finite_quotient_of_ne_bot _ (ne_bot_of_liesOver (K := F) p _)
  exact splitsCompletely_iff_eq_one_of_isArithFrobAt (K := F) p (P.under (𝓞 F)) ‹_›
    (isArithFrobAt_restrictNormal F _ P (IsArithFrobAt.arithFrobAt ℤ Gal(K/ℚ) P))

/-- **Splitting completely in an intermediate field is membership of the Frobenius in the
corresponding subgroup.**  Under the Galois correspondence the automorphisms restricting to the
identity of `F` are exactly those fixing `F` pointwise. -/
theorem splitsCompletely_intermediateField_iff_mem_fixingSubgroup (F : IntermediateField ℚ K)
    [Normal ℚ F] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsPrime] [Finite (𝓞 K ⧸ P)]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (hunr : Algebra.IsUnramifiedAt ℤ P) :
    SplitsCompletely F p ↔ arithFrobAt ℤ Gal(K/ℚ) P ∈ F.fixingSubgroup := by
  rw [splitsCompletely_intermediateField_iff F p P hunr, ← MonoidHom.mem_ker,
    IntermediateField.restrictNormalHom_ker]

end TopField

/-! ### Two computations in the Galois correspondence -/

/-- The image of the `m`-th power map on a finite cyclic group of order `n`, for `m` dividing `n`,
has `n / m` elements: it is generated by the `m`-th power of a generator. -/
theorem card_range_powMonoidHom {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] {m : ℕ}
    (hm : m ≠ 0) (hdvd : m ∣ Nat.card G) :
    Nat.card ((powMonoidHom m : G →* G).range) = Nat.card G / m := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hrange : (powMonoidHom m : G →* G).range = Subgroup.zpowers (g ^ m) := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨g, rfl⟩)
    rintro _ ⟨y, rfl⟩
    obtain ⟨k, rfl⟩ := hg y
    exact ⟨k, by simp [powMonoidHom, ← zpow_natCast, ← zpow_mul, mul_comm]⟩
  rw [hrange, Nat.card_zpowers, orderOf_pow_of_dvd hm (hord ▸ hdvd), hord]

/-- The fixed field of a subgroup of the Galois group of a finite Galois extension has degree over
the base equal to the index of that subgroup. -/
theorem finrank_fixedField_eq_index {k L : Type*} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L] (H : Subgroup Gal(L/k)) :
    Module.finrank k (IntermediateField.fixedField H) = H.index := by
  have hcard : Nat.card Gal(L/k) = Module.finrank k L := IsGalois.card_aut_eq_finrank k L
  have htower : Module.finrank k (IntermediateField.fixedField H) *
      Module.finrank (IntermediateField.fixedField H) L = Module.finrank k L :=
    Module.finrank_mul_finrank k (IntermediateField.fixedField H) L
  rw [IntermediateField.finrank_fixedField_eq_card H, ← hcard, ← H.card_mul_index,
    Nat.mul_comm (Nat.card H)] at htower
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos htower

/-! ### The degree `ℓ` subfield of `ℚ(ζ_q)` and its splitting law -/

/-- **The subfield of prime degree of a cyclotomic field of prime conductor, and its splitting
law.**  Let `q` be a prime and let `ℓ` be a prime dividing `q - 1`.  The Galois group of `ℚ(ζ_q)`
is cyclic of order `q - 1`, identified with `(ℤ/qℤ)ˣ` so that the Frobenius at a rational prime
`p ≠ q` is the class of `p`; the kernel of the `((q - 1) / ℓ)`-th power map is a subgroup of index
`ℓ`, and its fixed field `F` is a Galois extension of `ℚ` of degree `ℓ`.  A rational prime `p ≠ q`
splits completely in `F` exactly when the Frobenius lies in that kernel, that is, exactly when
`p ^ ((q - 1) / ℓ) = 1` in `ZMod q`.  The extension is unramified away from `q`, and ramified at
`q`. -/
theorem exists_intermediateField_finrank_eq_prime_and_splitsCompletely (q : ℕ) [hq : Fact q.Prime]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hdvd : ℓ ∣ q - 1) (E : Type*) [Field E] [NumberField E]
    [IsCyclotomicExtension {q} ℚ E] :
    ∃ F : IntermediateField ℚ E, Module.finrank ℚ F = ℓ ∧ IsGalois ℚ F ∧
      (∀ p : ℕ, p.Prime → p ≠ q →
        (SplitsCompletely F p ↔ (p : ZMod q) ^ ((q - 1) / ℓ) = 1)) ∧
      (∀ (Q : Ideal (𝓞 F)) [Q.IsPrime], Q ≠ ⊥ → (q : 𝓞 F) ∉ Q →
        Algebra.IsUnramifiedAt ℤ Q) ∧
      ∃ Q : Ideal (𝓞 F), ∃ _ : Q.IsPrime, Q ≠ ⊥ ∧ (q : 𝓞 F) ∈ Q ∧
        ¬ Algebra.IsUnramifiedAt ℤ Q := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {q} ℚ E
  haveI : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime hq.out
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq.out]
  have hq1 : q - 1 ≠ 0 := by
    have := hq.out.two_le
    omega
  have hmne : (q - 1) / ℓ ≠ 0 :=
    Nat.div_ne_zero_iff_of_dvd hdvd |>.mpr ⟨hq1, hℓ.ne_zero⟩
  have hmdvd : (q - 1) / ℓ ∣ q - 1 := Nat.div_dvd_of_dvd hdvd
  set H := Subgroup.comap (Rat.galEquivZMod q E).toMonoidHom
    (MonoidHom.ker (powMonoidHom ((q - 1) / ℓ) : (ZMod q)ˣ →* (ZMod q)ˣ)) with hH
  haveI : H.Normal := Subgroup.Normal.comap (MonoidHom.normal_ker _) _
  have hindex : H.index = ℓ := by
    rw [hH, Subgroup.index_comap_of_surjective (f := (Rat.galEquivZMod q E).toMonoidHom) _
        (Rat.galEquivZMod q E).surjective,
      Subgroup.index_ker, card_range_powMonoidHom hmne (hcard ▸ hmdvd), hcard,
      Nat.div_div_self hdvd hq1]
  have hrank : Module.finrank ℚ ↥(IntermediateField.fixedField H) = ℓ := by
    rw [finrank_fixedField_eq_index, hindex]
  -- the unramifiedness away from `q`, which also identifies the ramified prime
  have hunram : ∀ (Q : Ideal (𝓞 ↥(IntermediateField.fixedField H))) [Q.IsPrime], Q ≠ ⊥ →
      (q : 𝓞 ↥(IntermediateField.fixedField H)) ∉ Q → Algebra.IsUnramifiedAt ℤ Q := by
    intro Q _ hQ hqQ
    refine isUnramifiedAt_of_forall_prime_not_dvd_of_algebra q E Q hQ fun r hr hrQ hrdvd => ?_
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hq.out).mp hrdvd
    exact hqQ hrQ
  refine ⟨IntermediateField.fixedField H, hrank, inferInstance, ?_, hunram, ?_⟩
  · -- the splitting law
    intro p hp hpq
    haveI : Fact p.Prime := ⟨hp⟩
    have hpn : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq.out).mp h)
    obtain ⟨⟨P, hP⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)))
    haveI : P.IsPrime := hP.1
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
    have hPne : P ≠ ⊥ := ne_bot_of_liesOver p P
    haveI : Finite (𝓞 E ⧸ P) := finite_quotient_of_ne_bot P hPne
    have hunr : Algebra.IsUnramifiedAt ℤ P := by
      rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ) hPne,
        ← Ideal.over_def P (Ideal.span {(p : ℤ)})]
      exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p E P hpn
    rw [splitsCompletely_intermediateField_iff_mem_fixingSubgroup _ p P hunr,
      IntermediateField.fixingSubgroup_fixedField, hH, Subgroup.mem_comap, MonoidHom.mem_ker,
      MulEquiv.coe_toMonoidHom,
      galEquivZMod_arithFrobAt q E hp hpn P (Ideal.over_def P (Ideal.span {(p : ℤ)})).symm,
      powMonoidHom_apply, ← Units.val_eq_one, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  · -- ramification at `q`
    obtain ⟨Q, hQp, hQbot, hQram⟩ := exists_ne_bot_isPrime_not_isUnramifiedAt
      (↥(IntermediateField.fixedField H)) (by rw [hrank]; exact hℓ.one_lt)
    refine ⟨Q, hQp, hQbot, ?_, hQram⟩
    by_contra hmem
    exact hQram (hunram Q hQbot hmem)

end InverseGalois.CFT
