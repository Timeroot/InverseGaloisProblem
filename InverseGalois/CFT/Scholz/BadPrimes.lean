/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TameFrobenius
import InverseGalois.CFT.InertiaSubgroup
import InverseGalois.CFT.Level

/-!
# Where a Galois extension with central inertia of prime exponent can ramify

Let `ℓ` be a prime and let `K` be a Galois number field at which the inertia subgroup of a prime
above the rational prime `p` is central in `Gal(K/ℚ)` and killed by `ℓ`.  Such an inertia subgroup
has order a power of `ℓ`, so it is tame as soon as `p ≠ ℓ`, and then conjugation by an arithmetic
Frobenius raises its elements to the `p`-th power while leaving their central images alone.  An
element of the inertia subgroup is therefore killed by both `ℓ` and `p - 1`, and if those two
numbers are coprime it is trivial.

So the ramification is confined to `ℓ` and to the primes congruent to one modulo `ℓ`.  This is the
arithmetic behind Serre's condition on the primes at which a Scholz realization is allowed to
ramify: the solution of a central embedding problem with kernel of order `ℓ` acquires no new
ramification except at such primes, and those are exactly the primes carrying a cyclic degree-`ℓ`
cyclotomic character with which the new ramification can be cancelled.

## Main results

* `InverseGalois.CFT.not_dvd_card_of_forall_pow_eq_one`: a finite group killed by a prime `ℓ` has
  order divisible by no other prime.
* `InverseGalois.CFT.inertia_eq_bot_of_le_center`: **a central inertia subgroup killed by `ℓ` at a
  prime `p ≠ ℓ` with `ℓ ∤ p - 1` is trivial.**
* `InverseGalois.CFT.notMem_ramifiedSet_of_inertia_le_center`: **such a prime is unramified.**
* `InverseGalois.CFT.modEq_one_of_mem_ramifiedSet`: **a ramified prime other than `ℓ` is congruent
  to one modulo `ℓ`.**
* `InverseGalois.CFT.isLevel_one_of_inertia_le_center`: **a Galois number field with central
  inertia of exponent `ℓ` which is unramified at `ℓ` has level one.**

## Tags

inertia subgroup, ramified prime, tame ramification, Scholz condition, level
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] {ℓ p : ℕ}

/-! ### The order of a group of prime exponent -/

/-- **A finite group killed by a prime `ℓ` has order divisible by no other prime.**  Such a group
is an `ℓ`-group, so its order is a power of `ℓ`. -/
theorem not_dvd_card_of_forall_pow_eq_one {H : Type*} [Group H] [Finite H] (hℓ : ℓ.Prime)
    (hp : p.Prime) (hne : p ≠ ℓ) (h : ∀ x : H, x ^ ℓ = 1) :
    ¬ p ∣ Nat.card H := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨n, hn⟩ :=
    (IsPGroup.iff_card (p := ℓ) (G := H)).mp fun g => ⟨1, by rw [pow_one]; exact h g⟩
  rw [hn]
  exact fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hdvd))

/-! ### The primes that survive -/

/-- **A central inertia subgroup killed by a prime `ℓ` at a rational prime `p ≠ ℓ` which is not
congruent to one modulo `ℓ` is trivial.**  The inertia subgroup is an `ℓ`-group, hence tame at `p`,
so conjugation by an arithmetic Frobenius raises its elements to the `p`-th power; on a central
element that conjugation is invisible, so the element is killed by `p - 1` as well as by `ℓ`. -/
theorem inertia_eq_bot_of_le_center (hℓ : ℓ.Prime) (hp : p.Prime) (hne : p ≠ ℓ)
    (hnd : ¬ ℓ ∣ p - 1) (P : Ideal (𝓞 K)) [P.IsPrime] (hPo : P.LiesOver (Ideal.span {(p : ℤ)}))
    (hcen : Ideal.inertia Gal(K/ℚ) P ≤ Subgroup.center Gal(K/ℚ))
    (hexp : ∀ τ ∈ Ideal.inertia Gal(K/ℚ) P, τ ^ ℓ = 1) :
    Ideal.inertia Gal(K/ℚ) P = ⊥ := by
  have htame : ¬ p ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P) :=
    not_dvd_card_of_forall_pow_eq_one hℓ hp hne fun x => Subtype.ext (by simpa using hexp x.1 x.2)
  have hcop : Nat.Coprime ℓ (p - 1) := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hnd
  refine (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => ?_
  simpa using eq_one_of_mem_center_of_liesOver p hp hPo htame (MonoidHom.id Gal(K/ℚ)) ⟨τ, hτ⟩
    (by simpa using hcen hτ) (by simpa using hexp τ hτ) hcop

/-- **A rational prime other than `ℓ` and not congruent to one modulo `ℓ`, at which every inertia
subgroup is central and killed by `ℓ`, is unramified.** -/
theorem notMem_ramifiedSet_of_inertia_le_center (hℓ : ℓ.Prime) (hp : p.Prime) (hne : p ≠ ℓ)
    (hnd : ¬ ℓ ∣ p - 1)
    (hcen : ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
      Ideal.inertia Gal(K/ℚ) P ≤ Subgroup.center Gal(K/ℚ))
    (hexp : ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
      ∀ τ ∈ Ideal.inertia Gal(K/ℚ) P, τ ^ ℓ = 1) :
    p ∉ ramifiedSet K := by
  intro hmem
  obtain ⟨-, Q, ⟨hQprime, hQover⟩, -⟩ := id hmem
  haveI := hQprime
  haveI := hQover
  exact (inertia_ne_bot_iff_mem_ramifiedSet hp Q).mpr hmem
    (inertia_eq_bot_of_le_center hℓ hp hne hnd Q hQover (hcen Q hQprime hQover)
      (hexp Q hQprime hQover))

/-- **A ramified prime other than `ℓ` is congruent to one modulo `ℓ`**, for a Galois number field
whose inertia subgroups are central and killed by `ℓ`. -/
theorem modEq_one_of_mem_ramifiedSet (hℓ : ℓ.Prime)
    (hcen : ∀ P : Ideal (𝓞 K), P.IsPrime → Ideal.inertia Gal(K/ℚ) P ≤ Subgroup.center Gal(K/ℚ))
    (hexp : ∀ P : Ideal (𝓞 K), P.IsPrime → ∀ τ ∈ Ideal.inertia Gal(K/ℚ) P, τ ^ ℓ = 1)
    (hmem : p ∈ ramifiedSet K) (hne : p ≠ ℓ) :
    p ≡ 1 [MOD ℓ] := by
  have hp : p.Prime := hmem.1
  by_contra hc
  refine notMem_ramifiedSet_of_inertia_le_center hℓ hp hne ?_
    (fun P h1 _ => hcen P h1) (fun P h1 _ => hexp P h1) hmem
  exact fun hdvd => hc ((Nat.modEq_iff_dvd' hp.one_lt.le).mpr hdvd).symm

/-- **A Galois number field whose inertia subgroups are central and killed by `ℓ`, and which is
unramified at `ℓ`, has level one at `ℓ`.** -/
theorem isLevel_one_of_inertia_le_center (hℓ : ℓ.Prime) (hℓram : ℓ ∉ ramifiedSet K)
    (hcen : ∀ P : Ideal (𝓞 K), P.IsPrime → Ideal.inertia Gal(K/ℚ) P ≤ Subgroup.center Gal(K/ℚ))
    (hexp : ∀ P : Ideal (𝓞 K), P.IsPrime → ∀ τ ∈ Ideal.inertia Gal(K/ℚ) P, τ ^ ℓ = 1) :
    IsLevel ℓ 1 K := by
  intro q hq
  rw [pow_one]
  exact modEq_one_of_mem_ramifiedSet hℓ hcen hexp hq (fun h => hℓram (h ▸ hq))

end InverseGalois.CFT
