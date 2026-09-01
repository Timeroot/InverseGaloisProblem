/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceCyclic
import InverseGalois.CFT.Brauer.PlaceFrobenius
import InverseGalois.CFT.Units.CompletionCyclic

/-!
# The invariant of a cyclic algebra in terms of the global Frobenius

The invariant of a cyclic algebra at a finite place is the invariant of its coefficient raised to
the exponent which expresses the Frobenius as a power of a chosen generator of the Galois group of
the completions.  That exponent is a local quantity, and the arithmetic of the sum of the invariants
over all places needs a global one: the exponent expressing the *restriction* of the Frobenius as a
power of a generator of the Galois group of the extension.

The two are related by the index of the decomposition group.  Restriction to the extension is a
homomorphism, and it carries the chosen generator of the Galois group of the completions to that
power of the generator downstairs, so it carries the Frobenius to the corresponding power.  The
index times the local degree is the degree, so dividing by the local degree upstairs is dividing by
the degree downstairs after multiplying by the index, and the invariant becomes the classical
`c` times the value of the coefficient, divided by the degree, with `c` read off from the restricted
Frobenius.

## Main definitions

* `InverseGalois.CFT.placeValue`: the value of a unit of a number field at a finite place, divided
  by a generator of the value group of the completion.

## Main results

* `InverseGalois.CFT.restrictToBase_eq_restrictScalars_localDecompositionEquiv`: restriction to the
  extension is the identification of the Galois group of the completions with the Galois group over
  the decomposition field.
* `InverseGalois.CFT.index_mul_finrank_adicCompletion`: **the index of the decomposition group times
  the local degree is the degree.**
* `InverseGalois.CFT.restrictToBase_divisionFrobenius_eq_pow`: **the Frobenius of a completion
  restricts to the power of a generator given by the index times the local exponent.**
* `InverseGalois.CFT.placeInvariant_cyclicBrauerHom_eq_intQModZ`: **the invariant at a finite place
  of a cyclic algebra is the discrete logarithm of the restricted Frobenius times the value of the
  coefficient, divided by the degree.**

## Tags

number field, completion, decomposition group, Frobenius, cyclic algebra, local invariant, class
field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField

/-! ### Two fractions with the same class -/

section Arithmetic

private theorem nsmul_qModZ_mk (s : ℕ) (x : ℚ) :
    s • (QuotientAddGroup.mk x : QModZ) = QuotientAddGroup.mk (s • x) := by
  induction s with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, ih]; rfl

/-- **Two descriptions of the same class of rationals modulo the integers.**  The exponent `c` is
congruent to the index `e` times the local exponent `s` modulo the degree `n`, and the degree is the
index times the local degree `d`, so dividing by the local degree gives the same class as
multiplying by the exponent and dividing by the degree. -/
private theorem qModZ_mk_div_eq {V : ℤ} {c e s d n : ℕ} (hed : e * d = n) (hdpos : 0 < d)
    (hepos : 0 < e) {t : ℤ} (ht : (c : ℤ) - (e : ℤ) * (s : ℤ) = (n : ℤ) * t) :
    (QuotientAddGroup.mk ((s : ℚ) * (V : ℚ) / (d : ℚ)) : QModZ)
      = QuotientAddGroup.mk ((((c : ℤ) * V : ℤ) : ℚ) / (n : ℚ)) := by
  have hdq : ((d : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  have heq : ((e : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hepos.ne'
  have hedq : ((e : ℚ)) * (d : ℚ) = (n : ℚ) := by exact_mod_cast hed
  have hcq : ((c : ℚ)) = (e : ℚ) * (s : ℚ) + (n : ℚ) * (t : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) ht
    push_cast at h
    linarith
  have hsub : (s : ℚ) * (V : ℚ) / (d : ℚ) - (((c : ℤ) * V : ℤ) : ℚ) / (n : ℚ)
      = ((-(t * V) : ℤ) : ℚ) := by
    push_cast
    rw [hcq, ← hedq]
    field_simp
    ring
  have hmk : (QuotientAddGroup.mk ((s : ℚ) * (V : ℚ) / (d : ℚ)
        - (((c : ℤ) * V : ℤ) : ℚ) / (n : ℚ)) : QModZ)
      = QuotientAddGroup.mk ((s : ℚ) * (V : ℚ) / (d : ℚ))
        - QuotientAddGroup.mk ((((c : ℤ) * V : ℤ) : ℚ) / (n : ℚ)) := rfl
  have hzero : (QuotientAddGroup.mk ((s : ℚ) * (V : ℚ) / (d : ℚ)
      - (((c : ℤ) * V : ℤ) : ℚ) / (n : ℚ)) : QModZ) = 0 := by
    rw [hsub]
    exact QModZ.mk_intCast _
  rw [hmk] at hzero
  exact sub_eq_zero.1 hzero

end Arithmetic

/-! ### The value of a unit at a finite place -/

section PlaceValue

variable {k : Type} [Field k] [NumberField k]

/-- **The value of a unit of a number field at a finite place**, divided by a generator of the value
group of the completion, so that a uniformiser has value one. -/
noncomputable def placeValue (v : HeightOneSpectrum (𝓞 k)) (a : kˣ) : ℤ :=
  unitValDiv (isUnitValGen_one (valued_adicCompletion_surjective v))
    (Additive.ofMul (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a))

theorem placeValue_def (v : HeightOneSpectrum (𝓞 k)) (a : kˣ) :
    placeValue v a = unitValDiv (isUnitValGen_one (valued_adicCompletion_surjective v))
      (Additive.ofMul (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)) := rfl

/-- **A unit whose image in the completion has valuation one has value zero at the place.** -/
theorem placeValue_eq_zero (v : HeightOneSpectrum (𝓞 k)) {a : kˣ}
    (ha : Valued.v (algebraMap k (v.adicCompletion k) (a : k)) = 1) : placeValue v a = 0 := by
  have hmem : Additive.ofMul (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
      ∈ (unitVal (A := v.adicCompletion k)).ker := by
    rw [mem_ker_unitVal]
    simpa using ha
  rw [← ker_unitValDiv (isUnitValGen_one (valued_adicCompletion_surjective v))] at hmem
  exact AddMonoidHom.mem_ker.mp hmem

end PlaceValue

/-! ### The restriction of the Frobenius -/

section PlaceExponent

attribute [local instance] isGalois_adicCompletion

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **Restriction of an automorphism of the completion to the extension is the identification of the
Galois group of the completions with the Galois group over the decomposition field.**  Both are
determined by their effect on the image of the extension in the completion. -/
theorem restrictToBase_eq_restrictScalars_localDecompositionEquiv
    (τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) :
    restrictToBase k w τ = (localDecompositionEquiv k w τ).restrictScalars k := by
  refine AlgEquiv.ext fun x => FaithfulSMul.algebraMap_injective K (w.adicCompletion K) ?_
  rw [algebraMap_adicCompletion_eq, toAdicCompletion_restrictToBase]
  exact algebraMap_localDecompositionEquiv k w τ x

variable (k) in
/-- **The index of the decomposition group times the local degree is the degree.**  The Galois group
of the completions is the decomposition group, and the degree of an extension of local fields is the
order of its Galois group. -/
theorem index_mul_finrank_adicCompletion :
    (stabilizer Gal(K/k) w).index
        * finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
      = Nat.card Gal(K/k) := by
  have hfr : finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
      = Nat.card (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k]
        w.adicCompletion K) := (IsGalois.card_aut_eq_finrank _ _).symm
  rw [hfr, Nat.card_congr (localDecompositionEquiv k w).toEquiv,
    ← Nat.card_congr (decompositionFieldEquiv k w).toEquiv]
  exact Subgroup.index_mul_card _

variable (k) in
/-- **The Frobenius of a completion restricts to the power of a generator of the Galois group given
by the index of the decomposition group times the local exponent.**  Restriction to the extension is
a homomorphism carrying the chosen generator upstairs to that power of the generator downstairs. -/
theorem restrictToBase_divisionFrobenius_eq_pow {σ₀ : Gal(K/k)}
    {σ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K}
    (hres : (localDecompositionEquiv k w σ).restrictScalars k
      = σ₀ ^ (stabilizer Gal(K/k) w).index)
    (hur : ∀ z : w.adicCompletion K, z ≠ 0 → ∃ c : (primeUnder (𝓞 k) w).adicCompletion k,
      c ≠ 0 ∧ divisionNorm ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) z = ‖c‖)
    {s : ℕ}
    (hs : divisionFrobenius ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) hur
      = σ ^ s) :
    restrictToBase k w (divisionFrobenius ((primeUnder (𝓞 k) w).adicCompletion k)
        (w.adicCompletion K) hur)
      = σ₀ ^ ((stabilizer Gal(K/k) w).index * s) := by
  rw [hs, ← restrictToBaseHom_apply, map_pow, restrictToBaseHom_apply,
    restrictToBase_eq_restrictScalars_localDecompositionEquiv k w σ, hres, ← pow_mul]

/-! ### The invariant in terms of the restricted Frobenius -/

variable (k) in
/-- **The invariant at a finite place of a cyclic algebra is the discrete logarithm of the
restricted Frobenius times the value of the coefficient, divided by the degree.**  The exponent is
the one expressing the Frobenius of the place as a power of the chosen generator of the Galois
group of the extension, so this is the description of the local invariant by a global datum. -/
theorem placeInvariant_cyclicBrauerHom_eq_intQModZ {σ₀ : Gal(K/k)}
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀)
    {σ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K}
    (hσ : ∀ x : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K,
      x ∈ Subgroup.zpowers σ)
    (hres : (localDecompositionEquiv k w σ).restrictScalars k
      = σ₀ ^ (stabilizer Gal(K/k) w).index)
    (hur : ∀ z : w.adicCompletion K, z ≠ 0 → ∃ c : (primeUnder (𝓞 k) w).adicCompletion k,
      c ≠ 0 ∧ divisionNorm ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) z = ‖c‖)
    {s : ℕ}
    (hs : divisionFrobenius ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) hur
      = σ ^ s) {c : ℕ}
    (hc : restrictToBase k w (divisionFrobenius ((primeUnder (𝓞 k) w).adicCompletion k)
      (w.adicCompletion K) hur) = σ₀ ^ c) (a : kˣ) :
    placeInvariant k (primeUnder (𝓞 k) w) (cyclicBrauerHom hσ₀ a)
      = Multiplicative.ofAdd (intQModZ (Nat.card Gal(K/k))
        ((c : ℤ) * placeValue (primeUnder (𝓞 k) w) a)) := by
  -- the index of the decomposition group times the local degree is the degree
  have hed := index_mul_finrank_adicCompletion k w
  have hnpos : 0 < Nat.card Gal(K/k) := Nat.card_pos
  have hepos : 0 < (stabilizer Gal(K/k) w).index := by
    rcases Nat.eq_zero_or_pos (stabilizer Gal(K/k) w).index with h | h
    · rw [h, zero_mul] at hed
      omega
    · exact h
  have hdpos : 0 < finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) := by
    rcases Nat.eq_zero_or_pos
      (finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)) with h | h
    · rw [h, mul_zero] at hed
      omega
    · exact h
  -- the two exponents agree modulo the degree
  have horder : orderOf σ₀ = Nat.card Gal(K/k) := by
    have htop : Subgroup.zpowers σ₀ = ⊤ := (Subgroup.eq_top_iff' _).2 hσ₀
    rw [← Nat.card_zpowers, htop]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hpow : σ₀ ^ ((stabilizer Gal(K/k) w).index * s) = σ₀ ^ c := by
    rw [← restrictToBase_divisionFrobenius_eq_pow k w hres hur hs]
    exact hc
  have hmod : (stabilizer Gal(K/k) w).index * s ≡ c [MOD Nat.card Gal(K/k)] := by
    rw [← horder]
    exact pow_eq_pow_iff_modEq.1 hpow
  obtain ⟨t, ht⟩ : ((Nat.card Gal(K/k) : ℤ)) ∣
      (c : ℤ) - ((stabilizer Gal(K/k) w).index : ℤ) * (s : ℤ) := by
    have h := hmod.dvd
    push_cast at h
    exact h
  -- assemble
  rw [placeValue_def, placeInvariant_cyclicBrauerHom k w hσ₀ hσ hres hur hs a, baseInvariant_apply,
    unitInvariant_apply, ← ofAdd_nsmul, intQModZ_apply]
  refine congrArg Multiplicative.ofAdd ?_
  rw [nsmul_qModZ_mk, nsmul_eq_mul, ← mul_div_assoc]
  exact qModZ_mk_div_eq hed hdpos hepos ht

end PlaceExponent

end InverseGalois.CFT
