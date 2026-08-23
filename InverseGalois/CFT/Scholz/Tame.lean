import Mathlib
import InverseGalois.CFT.KroneckerWeber
import InverseGalois.CFT.Scholz.Condition

/-!
# Fields of prime-power degree and level `N` are tamely ramified

Every field that occurs in the Scholz–Reichardt induction has degree a power of `ℓ` and satisfies
the level condition: each ramified rational prime is congruent to one modulo `ℓ ^ N`.  Those two
requirements are incompatible with wild ramification.  Indeed the ramification index at a prime
`p` is the order of the inertia subgroup, hence a power of `ℓ`, so `p` could only divide it by
being equal to `ℓ`; but `ℓ` divides `p - 1`, and `ℓ` does not divide `ℓ - 1`.

The consequence is that the Kronecker–Weber theorem is available for these fields without any of
the wild theory: the tame case, `InverseGalois.CFT.exists_algHom_cyclotomicField_of_tame`, already
applies.

## Main results

* `InverseGalois.CFT.isTamelyRamified_of_isLevel`: **a field of `ℓ`-power degree and level `N ≥ 1`
  is tamely ramified.**
* `InverseGalois.CFT.IsScholz.isTamelyRamified`: the same for a field satisfying Serre's
  condition `(S_N)`.
* `InverseGalois.CFT.exists_algHom_cyclotomicField_of_isLevel`: **Kronecker–Weber for these
  fields** — an abelian one of `ℓ`-power degree and level `N ≥ 1` embeds into a cyclotomic field.
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **A field of `ℓ`-power degree whose ramified primes are congruent to one modulo `ℓ ^ N` is
tamely ramified**, provided `N ≥ 1`.  The ramification index at a ramified prime `p` is the order
of the inertia subgroup, so it is a power of `ℓ`; were `p` to divide it, `p` would equal `ℓ`, and
then `ℓ` would divide `ℓ - 1`. -/
theorem isTamelyRamified_of_isLevel {ℓ N : ℕ} (hℓ : ℓ.Prime) (hN : N ≠ 0)
    (hG : IsPGroup ℓ Gal(K/ℚ)) (h : IsLevel ℓ N K) : IsTamelyRamified K := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  intro p hp P hPprime hPover hdvd
  haveI := hPprime
  haveI := hPover
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_natCast hp hPover
  have hunder : P.under ℤ = Ideal.span {(p : ℤ)} := hPover.over.symm
  have hcard : Nat.card (Ideal.inertia Gal(K/ℚ) P)
      = Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P := by
    rw [card_inertia_eq_ramificationIdx P hP0, hunder]
  -- the ramification index is a power of `ℓ`
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hG.to_subgroup (Ideal.inertia Gal(K/ℚ) P))
  have hpow : Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P = ℓ ^ j :=
    hcard.symm.trans hj
  -- so `p` divides a power of `ℓ`, forcing `p = ℓ`
  rw [hpow] at hdvd
  have hpl : p = ℓ := (Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hdvd)
  -- but `p` is ramified, hence congruent to one modulo `ℓ ^ N`
  have hmem : p ∈ ramifiedSet K := by
    refine ⟨hp, P, ⟨inferInstance, inferInstance⟩, fun he => ?_⟩
    rw [hpow] at he
    rw [he] at hdvd
    exact hp.ne_one (Nat.dvd_one.mp hdvd)
  have hdvdpow : ℓ ^ N ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_le).mp (h p hmem).symm
  have hdvdl : ℓ ∣ p - 1 := dvd_trans (dvd_pow_self ℓ hN) hdvdpow
  rw [hpl] at hdvdl
  have h2 := hℓ.two_le
  have := Nat.le_of_dvd (by omega) hdvdl
  omega

/-- **A field of `ℓ`-power degree satisfying Serre's condition `(S_N)` is tamely ramified.** -/
theorem IsScholz.isTamelyRamified {ℓ N : ℕ} (hℓ : ℓ.Prime) (hN : N ≠ 0)
    (hG : IsPGroup ℓ Gal(K/ℚ)) (h : IsScholz ℓ N K) : IsTamelyRamified K :=
  isTamelyRamified_of_isLevel hℓ hN hG h.1

/-- **Kronecker–Weber for the fields of the Scholz–Reichardt induction.**  An abelian number field
of `ℓ`-power degree whose ramified primes are congruent to one modulo `ℓ ^ N`, with `N ≥ 1`,
embeds into a cyclotomic field.  No wild ramification theory is needed: such a field is tamely
ramified. -/
theorem exists_algHom_cyclotomicField_of_isLevel [IsMulCommutative Gal(K/ℚ)] {ℓ N : ℕ}
    (hℓ : ℓ.Prime) (hN : N ≠ 0) (hG : IsPGroup ℓ Gal(K/ℚ)) (h : IsLevel ℓ N K) :
    ∃ m : ℕ, m ≠ 0 ∧ Nonempty (K →ₐ[ℚ] CyclotomicField m ℚ) :=
  exists_algHom_cyclotomicField_of_tame K (isTamelyRamified_of_isLevel hℓ hN hG h)

end InverseGalois.CFT
