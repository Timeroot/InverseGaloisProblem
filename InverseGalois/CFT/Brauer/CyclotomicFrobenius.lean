/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceCyclotomic

/-!
# The Frobenius of a cyclotomic field as a global automorphism

The Galois group of the cyclotomic field of conductor `n` over the rationals is the group of units
of the integers modulo `n`, an automorphism corresponding to the class of an exponent to which it
raises every root of unity of order dividing `n`.  For a natural number prime to the conductor this
names an automorphism directly, and it is the one the Frobenius of any place away from the conductor
lying over that number restricts to.

The invariant of a cyclic algebra over the rationals at a place of a cyclotomic field away from the
conductor is therefore computed by a single global datum: the exponent expressing the automorphism
raising the roots of unity to the power of the rational prime below the place as a power of the
chosen generator of the Galois group.

## Main definitions

* `InverseGalois.CFT.cyclotomicPowerAut`: **the automorphism of a cyclotomic field over the
  rationals raising every root of unity of order dividing the conductor to a given power prime to
  the conductor.**

## Main results

* `InverseGalois.CFT.cyclotomicPowerAut_apply`: it does raise every such root of unity to that
  power.
* `InverseGalois.CFT.placeInvariant_cyclicBrauerHom_cyclotomic`: **the invariant of a cyclic algebra
  over the rationals at a place of a cyclotomic field away from the conductor**, in terms of the
  exponent of that automorphism.

## Tags

cyclotomic field, Frobenius, Brauer group, local invariant, cyclic algebra, reciprocity
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Powers of a root of unity -/

section Pow

/-- A power of a root of unity only depends on the exponent modulo its order. -/
theorem pow_mod_eq_pow_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {n : ℕ} (hx : x ^ n = 1)
    (p : ℕ) : x ^ (p % n) = x ^ p := by
  conv_rhs => rw [← Nat.div_add_mod p n]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

end Pow

/-! ### The automorphism raising the roots of unity to a given power -/

section PowerAut

variable (n : ℕ) [NeZero n] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]

/-- **The automorphism of a cyclotomic field over the rationals raising every root of unity of
order dividing the conductor to a given power.**  The power is asked to be prime to the conductor,
so that it names a unit of the integers modulo the conductor and hence, through the cyclotomic
description of the Galois group, an automorphism. -/
noncomputable def cyclotomicPowerAut {p : ℕ} (hp : Nat.Coprime p n) : Gal(K/ℚ) :=
  (IsCyclotomicExtension.Rat.galEquivZMod n K).symm (ZMod.unitOfCoprime p hp)

/-- **The automorphism named by a power prime to the conductor raises every root of unity of order
dividing the conductor to that power.** -/
theorem cyclotomicPowerAut_apply {p : ℕ} (hp : Nat.Coprime p n) {x : K} (hx : x ^ n = 1) :
    cyclotomicPowerAut n K hp x = x ^ p := by
  rw [cyclotomicPowerAut, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n K _ hx,
    MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime, ZMod.val_natCast,
    pow_mod_eq_pow_of_pow_eq_one hx]

/-- The chosen primitive root of unity of a cyclotomic field generates it over the rationals. -/
theorem adjoin_zeta_rat_eq_top :
    Algebra.adjoin ℚ ({IsCyclotomicExtension.zeta n ℚ K} : Set K) = ⊤ :=
  IsCyclotomicExtension.adjoin_primitive_root_eq_top (IsCyclotomicExtension.zeta_spec n ℚ K)

end PowerAut

/-! ### The invariant at a place of a cyclotomic field -/

section Invariant

attribute [local instance] isGalois_adicCompletion

variable (n : ℕ) [NeZero n] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
  [IsGalois ℚ K]

/-- **The invariant of a cyclic algebra over the rationals at a place of a cyclotomic field away
from the conductor.**  The place is unramified there, and the Frobenius restricts to the
automorphism raising the roots of unity to the power of the rational prime below the place, so the
invariant is the exponent of that automorphism times the value of the coefficient, divided by the
degree. -/
theorem placeInvariant_cyclicBrauerHom_cyclotomic {σ₀ : Gal(K/ℚ)}
    (hσ₀ : ∀ x : Gal(K/ℚ), x ∈ Subgroup.zpowers σ₀) (w : HeightOneSpectrum (𝓞 K)) {q : ℕ}
    [hq : Fact q.Prime] [w.asIdeal.LiesOver (Ideal.span {(q : ℤ)})] (hqn : Nat.Coprime q n) {c : ℕ}
    (hc : cyclotomicPowerAut n K hqn = σ₀ ^ c) (a : ℚˣ) :
    placeInvariant ℚ (primeUnder (𝓞 ℚ) w) (cyclicBrauerHom hσ₀ a)
      = Multiplicative.ofAdd (intQModZ (Nat.card Gal(K/ℚ))
        ((c : ℤ) * placeValue (primeUnder (𝓞 ℚ) w) a)) :=
  placeInvariant_cyclicBrauerHom_rat_of_adjoin_not_dvd w hσ₀ n K
    ((Nat.Prime.coprime_iff_not_dvd hq.out).mp hqn) (NeZero.ne n)
    ((Nat.Prime.coprime_iff_not_dvd hq.out).mp hqn)
    (IsCyclotomicExtension.zeta_spec n ℚ K).pow_eq_one (adjoin_zeta_rat_eq_top n K)
    (cyclotomicPowerAut_apply n K hqn (IsCyclotomicExtension.zeta_spec n ℚ K).pow_eq_one) hc a

end Invariant

end InverseGalois.CFT
