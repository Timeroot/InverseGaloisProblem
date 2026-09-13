/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedEquivariant

/-!
# The product over the stabiliser, and the places the obstruction is free at

An element of order one at a place and none at the other named places need not be fixed by the
automorphisms fixing that place, but its **product over the stabiliser** is.  The vector of orders
is equivariant, so the product has order the size of the stabiliser at the place it belongs to and
none at the other named places: translating an element by an automorphism fixing the place moves
its order to the same place it was already at.

Since the orders are only read modulo the exponent, that product may be raised to a power inverse to
the size of the stabiliser modulo the exponent whenever the two are coprime.  So the element asked
for by the equivariant splitting **exists for free at every place whose stabiliser has order prime
to the exponent**, and the arithmetic of the obstruction is spent only at the places whose
decomposition group has order divisible by it.

For a prime exponent that is a statement about elements of that order: by Cauchy's theorem the
stabiliser has order divisible by the prime exactly when it contains an element of order the prime,
so the obstruction costs nothing at a place no automorphism of order the prime fixes.

## Main results

* `InverseGalois.CFT.exists_stabilizer_fixed_of_coprime`: **the product over the stabiliser supplies
  the element of the equivariant splitting at a place whose stabiliser has order prime to the
  exponent.**
* `InverseGalois.CFT.tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_order`: **the unit
  the obstruction is bought with is only asked for at the places some automorphism of order the
  prime fixes.**

## Tags

group cohomology, S-unit, confined unit, decomposition group, stabiliser, obstruction
-/

set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField TensorProduct groupCohomology

/-! ### The product over the stabiliser -/

section Product

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {X : Type} [MulAction Q X]

/-- **The product over the stabiliser of a place supplies the element of the equivariant splitting
there, as soon as the stabiliser has order prime to the exponent.**

The vector of orders being onto, an element of order one at the place and none at the other named
places exists; the product of its translates by the automorphisms fixing the place is fixed by them,
and its order is the size of the stabiliser at that place and none at the others, since a translate
of the element by an automorphism fixing the place has its order at that same place.  The orders
being read only modulo the exponent, raising the product to a power inverse to the size of the
stabiliser modulo the exponent brings the order at the place back to one. -/
theorem exists_stabilizer_fixed_of_coprime (g : Additive A →+ (X →₀ ℤ))
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hg : Function.Surjective g) (n : ℕ) [NeZero n] (x : X) [Finite ↥(stabilizer Q x)]
    (hcop : Nat.Coprime (Nat.card ↥(stabilizer Q x)) n) :
    ∃ a : A, (∀ z : X, (n : ℤ) ∣ g (Additive.ofMul a) z - Finsupp.single x 1 z) ∧
      ∀ σ : Q, σ • x = x → σ • a = a := by
  classical
  haveI : Fintype ↥(stabilizer Q x) := Fintype.ofFinite _
  obtain ⟨a₁, ha₁⟩ := hg (Finsupp.single x 1)
  have ha₀ : g (Additive.ofMul a₁.toMul) = Finsupp.single x 1 := ha₁
  have hgprod : ∀ (s : Finset ↥(stabilizer Q x)) (f : ↥(stabilizer Q x) → A),
      g (Additive.ofMul (∏ i ∈ s, f i)) = ∑ i ∈ s, g (Additive.ofMul (f i)) := by
    intro s f
    induction s using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih =>
        rw [Finset.prod_cons, Finset.sum_cons, _root_.ofMul_mul, _root_.map_add, ih]
  obtain ⟨b, hgb, hbfix⟩ : ∃ b : A,
      g (Additive.ofMul b) = (Nat.card ↥(stabilizer Q x)) • Finsupp.single x (1 : ℤ) ∧
        ∀ τ : Q, τ • x = x → τ • b = b := by
    refine ⟨∏ σ : ↥(stabilizer Q x), (σ : Q) • a₁.toMul, ?_, fun τ hτ => ?_⟩
    · have hterm : ∀ σ : ↥(stabilizer Q x),
          g (Additive.ofMul ((σ : Q) • a₁.toMul)) = Finsupp.single x (1 : ℤ) := by
        intro σ
        refine Finsupp.ext fun z => ?_
        rw [hgeq, ha₀]
        have hfix : x = (σ : Q)⁻¹ • z ↔ x = z := by
          rw [eq_inv_smul_iff, MulAction.mem_stabilizer_iff.1 σ.2]
        simp only [Finsupp.single_apply, hfix]
      rw [hgprod, Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card]
    · rw [Finset.smul_prod']
      refine Fintype.prod_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : ↥(stabilizer Q x)))
        (fun σ => τ • ((σ : Q) • a₁.toMul)) (fun σ => (σ : Q) • a₁.toMul) fun σ => ?_
      show τ • ((σ : Q) • a₁.toMul)
        = ((⟨τ, hτ⟩ * σ : ↥(stabilizer Q x)) : Q) • a₁.toMul
      rw [← mul_smul]
      rfl
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℤ) ∣ (Nat.card ↥(stabilizer Q x) : ℤ) * (m : ℤ) - 1 := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have ht : 0 < Nat.totient n := Nat.totient_pos.mpr hn
    refine ⟨Nat.card ↥(stabilizer Q x) ^ (Nat.totient n - 1), ?_⟩
    have hmod : Nat.card ↥(stabilizer Q x) ^ Nat.totient n ≡ 1 [MOD n] :=
      Nat.ModEq.pow_totient hcop
    have hdvd : (n : ℤ) ∣ (1 : ℤ) - (Nat.card ↥(stabilizer Q x) : ℤ) ^ Nat.totient n := by
      have h := (Nat.modEq_iff_dvd).1 hmod
      push_cast at h
      exact h
    have hpow : (Nat.card ↥(stabilizer Q x) : ℤ)
        * (Nat.card ↥(stabilizer Q x) : ℤ) ^ (Nat.totient n - 1)
        = (Nat.card ↥(stabilizer Q x) : ℤ) ^ Nat.totient n := by
      rw [← pow_succ']
      congr 1
      omega
    have hgoal : (Nat.card ↥(stabilizer Q x) : ℤ)
        * ((Nat.card ↥(stabilizer Q x) ^ (Nat.totient n - 1) : ℕ) : ℤ) - 1
        = -((1 : ℤ) - (Nat.card ↥(stabilizer Q x) : ℤ) ^ Nat.totient n) := by
      push_cast
      rw [hpow]
      ring
    rw [hgoal]
    exact dvd_neg.2 hdvd
  refine ⟨b ^ m, fun z => ?_, fun τ hτ => ?_⟩
  · have hz : g (Additive.ofMul (b ^ m)) z
        = ((Nat.card ↥(stabilizer Q x) : ℤ) * (m : ℤ)) * Finsupp.single x (1 : ℤ) z := by
      rw [_root_.ofMul_pow, map_nsmul, hgb, Finsupp.smul_apply, Finsupp.smul_apply,
        nsmul_eq_mul, nsmul_eq_mul]
      ring
    rw [hz, ← sub_one_mul]
    exact hm.mul_right _
  · rw [smul_pow', hbfix τ hτ]

end Product

/-! ### The obstruction is free where no automorphism of order the prime fixes the place -/

section Confined

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [FiniteDimensional k K]
variable {C : Type} [CommGroup C] [MulDistribMulAction Gal(K/k) C]
variable (n : ℕ) [Fact n.Prime] (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite ↥Xs] [DecidableEq ↥Xs]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y] [IsGaloisStablePlaces k K Xs]

/-- **The unit the obstruction is bought with is only asked for at the places some automorphism of
order the prime fixes.**

Where no automorphism of order the prime fixes the place, the stabiliser has order prime to it by
Cauchy's theorem, and the product of a preimage of the generator at the place over that stabiliser,
raised to a power inverse to its size modulo the prime, already supplies a unit fixed by the
automorphisms fixing the place, of order one there and none at the other named places, each read up
to a multiple of the prime. -/
theorem tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_order
    (hexp : ∀ c : C, c ^ n = 1) (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hstab : ∀ y : ↥Xs, (∃ σ : Gal(K/k), σ ≠ 1 ∧ σ ^ n = 1 ∧ σ • y = y) →
      ∃ u : ↥(confinedUnits K n Tz Y),
        (∀ z : ↥Xs, (n : ℤ) ∣ confinedOrd n Tz Y Xs (Additive.ofMul u) z - Finsupp.single y 1 z) ∧
          ∀ σ : Gal(K/k), σ • y = y → σ • u = u)
    {t : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C}
    (ht : ∀ σ : Gal(K/k), tensorVal C (confinedOrd n Tz Y Xs) (σ • t)
      = tensorVal C (confinedOrd n Tz Y Xs) t) :
    tensorInvariantClass C (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs) hsurj
      (mem_confinedSUnits_iff n Tz Y Xs) ht = 0 := by
  have hp : n.Prime := Fact.out
  haveI : NeZero n := ⟨hp.ne_zero⟩
  refine tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod n Tz Y Xs hexp hsurj
    (fun y => ?_) ht
  by_cases hy : ∃ σ : Gal(K/k), σ ≠ 1 ∧ σ ^ n = 1 ∧ σ • y = y
  · exact hstab y hy
  · haveI : Finite Gal(K/k) := Finite.of_fintype _
    haveI : Finite ↥(stabilizer Gal(K/k) y) := Subtype.finite
    haveI : Fintype ↥(stabilizer Gal(K/k) y) := Fintype.ofFinite _
    refine exists_stabilizer_fixed_of_coprime (confinedOrd n Tz Y Xs)
      (confinedOrd_smul_apply n Tz Y Xs) hsurj n y ?_
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => hy ?_)
    rw [Nat.card_eq_fintype_card] at hdvd
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card n hdvd
    have hσ1 : σ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hσ
      exact hp.one_lt.ne hσ
    refine ⟨(σ : Gal(K/k)), fun h => hσ1 (OneMemClass.coe_eq_one.1 h), ?_,
      MulAction.mem_stabilizer_iff.1 σ.2⟩
    rw [← hσ, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]

end Confined

end InverseGalois.CFT
