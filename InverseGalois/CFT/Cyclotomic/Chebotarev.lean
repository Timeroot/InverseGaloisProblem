import Mathlib
import InverseGalois.CFT.Cyclotomic.Frobenius

/-!
# Chebotarev's theorem for subfields of cyclotomic fields

Every element of the Galois group of a subfield of a cyclotomic field is the arithmetic Frobenius
of infinitely many rational primes.  This is Dirichlet's theorem on primes in arithmetic
progressions transported through the reciprocity law of
`InverseGalois/CFT/Cyclotomic/Frobenius.lean`: the Frobenius at `p` corresponds to the class of `p`
in `(ℤ/nℤ)ˣ`, so realising a prescribed element of `Gal(ℚ(ζₙ)/ℚ)` amounts to finding a prime in a
prescribed residue class modulo `n`.  No analytic density and no general form of Chebotarev's
density theorem enters.

## Main results

* `InverseGalois.CFT.isArithFrobAt_restrictNormal`: the restriction of an arithmetic Frobenius to a
  normal intermediate field is the arithmetic Frobenius at the prime below.
* `InverseGalois.CFT.exists_prime_isArithFrobAt`: every element of `Gal(ℚ(ζₙ)/ℚ)` is the arithmetic
  Frobenius at a prime above an arbitrarily large rational prime.
* `InverseGalois.CFT.exists_prime_isArithFrobAt_intermediateField`: the same statement for any
  intermediate field of `ℚ(ζₙ)/ℚ`.
* `InverseGalois.CFT.infinite_setOf_prime_isArithFrobAt`: the set of such primes is infinite.
-/

open NumberField IsCyclotomicExtension

namespace InverseGalois.CFT

/-- An arithmetic Frobenius restricts to an arithmetic Frobenius: if `σ` is a Frobenius at a prime
`P` of `𝓞 K`, then its restriction to a normal intermediate field `F` is a Frobenius at the prime
of `𝓞 F` lying below `P`. -/
theorem isArithFrobAt_restrictNormal {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (F : IntermediateField ℚ K) [Normal ℚ F] (σ : Gal(K/ℚ)) (P : Ideal (𝓞 K))
    (hσ : IsArithFrobAt ℤ σ P) :
    IsArithFrobAt ℤ (AlgEquiv.restrictNormalHom F σ) (P.under (𝓞 F)) := by
  have key : ∀ y : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) ((AlgEquiv.restrictNormalHom F σ) • y)
      = σ • algebraMap (𝓞 F) (𝓞 K) y := by
    intro y
    have hK : ∀ z : 𝓞 K, algebraMap (𝓞 K) K (σ • z) = σ (algebraMap (𝓞 K) K z) := fun _ => rfl
    have hF : ∀ w : 𝓞 F, algebraMap (𝓞 F) F ((AlgEquiv.restrictNormalHom F σ) • w)
        = (AlgEquiv.restrictNormalHom F σ) (algebraMap (𝓞 F) F w) := fun _ => rfl
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [hK, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
      ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
      IsScalarTower.algebraMap_apply (𝓞 F) F K, IsScalarTower.algebraMap_apply (𝓞 F) F K, hF]
    exact AlgEquiv.restrictNormal_commutes σ F _
  intro x
  rw [Ideal.under_under, Ideal.under, Ideal.mem_comap, map_sub, map_pow]
  have h2 : σ • algebraMap (𝓞 F) (𝓞 K) x
      - algebraMap (𝓞 F) (𝓞 K) x ^ Nat.card (ℤ ⧸ Ideal.under ℤ P) ∈ P :=
    hσ (algebraMap (𝓞 F) (𝓞 K) x)
  rw [← key x] at h2
  exact h2

/-- **Chebotarev's theorem for cyclotomic fields.**  Every element of `Gal(ℚ(ζₙ)/ℚ)` is the
arithmetic Frobenius at a prime of `𝓞 K` lying above a rational prime `p > B` not dividing `n`. -/
theorem exists_prime_isArithFrobAt (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (σ : Gal(K/ℚ)) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ¬ p ∣ n ∧ ∃ P : Ideal (𝓞 K), P.IsPrime ∧
      P.under ℤ = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ P := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  set a : (ZMod n)ˣ := Rat.galEquivZMod n K σ with ha
  have hcop : Nat.Coprime ((a : ZMod n).val) n := ZMod.val_coe_unit_coprime a
  obtain ⟨p, hpB, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B n) (NeZero.ne n) hcop
  have hpn : ¬ p ∣ n := fun hdvd =>
    absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hdvd)
      (not_le.mpr (lt_of_le_of_lt (le_max_right B n) hpB))
  have hnebot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal := IsPrime.to_maximal_ideal hnebot
  obtain ⟨P, hPmax, hPcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := ℤ) (S := 𝓞 K) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]
        exact bot_le)
  haveI : P.IsMaximal := hPmax
  haveI : P.IsPrime := hPmax.isPrime
  have hPunder : P.under ℤ = Ideal.span {(p : ℤ)} := hPcomap
  refine ⟨p, lt_of_le_of_lt (le_max_left B n) hpB, hp, hpn, P, inferInstance, hPunder, ?_⟩
  have heq : Rat.galEquivZMod n K (arithFrobAt ℤ Gal(K/ℚ) P) = a := by
    rw [galEquivZMod_arithFrobAt n K hp hpn P hPunder]
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hpmod,
      ZMod.natCast_val, ZMod.cast_id]
  rw [← (Rat.galEquivZMod n K).injective (heq.trans ha)]
  exact IsArithFrobAt.arithFrobAt ℤ Gal(K/ℚ) P

/-- **Chebotarev's theorem for subfields of cyclotomic fields.**  Every element of the Galois group
of an intermediate field of `ℚ(ζₙ)/ℚ` is the arithmetic Frobenius at a prime lying above a rational
prime `p > B` not dividing `n`. -/
theorem exists_prime_isArithFrobAt_intermediateField (n : ℕ) [NeZero n] (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {n} ℚ K] (F : IntermediateField ℚ K)
    (σ : Gal(F/ℚ)) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ¬ p ∣ n ∧ ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ Q := by
  haveI : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {n} ℚ K
  haveI : IsGalois ℚ K := inferInstance
  haveI : IsAbelianGalois ℚ F := inferInstance
  haveI : Normal ℚ F := inferInstance
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := ↥F) (E := K) σ
  obtain ⟨p, hpB, hp, hpn, P, _, hPunder, hPfrob⟩ := exists_prime_isArithFrobAt n K τ B
  refine ⟨p, hpB, hp, hpn, P.under (𝓞 F), inferInstance, ?_, ?_⟩
  · rw [Ideal.under_under, hPunder]
  · rw [← hτ]
    exact isArithFrobAt_restrictNormal F τ P hPfrob

/-- Infinitely many rational primes have a prescribed element of the Galois group of a subfield of
a cyclotomic field as their arithmetic Frobenius. -/
theorem infinite_setOf_prime_isArithFrobAt (n : ℕ) [NeZero n] (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {n} ℚ K] (F : IntermediateField ℚ K)
    (σ : Gal(F/ℚ)) :
    {p : ℕ | p.Prime ∧ ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ Q}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun B => ?_
  obtain ⟨p, hpB, hp, -, Q, hQ⟩ := exists_prime_isArithFrobAt_intermediateField n K F σ B
  exact ⟨p, ⟨hp, Q, hQ⟩, hpB⟩

end InverseGalois.CFT
