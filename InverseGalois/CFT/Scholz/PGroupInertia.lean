/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TameCyclic
import InverseGalois.CFT.TameFrobenius
import InverseGalois.CFT.InertiaFixedField

/-!
# Inertia away from `ℓ` in an extension of `ℓ`-power degree

In a Galois number field whose Galois group is an `ℓ`-group, every inertia subgroup is an
`ℓ`-group, so at a rational prime other than `ℓ` the ramification is tame and the inertia subgroup
is cyclic.  Tameness makes the arithmetic Frobenius act on the inertia subgroup by raising to the
`p`-th power, and that action is invisible on a central element; so a homomorphism which maps the
inertia subgroup into a central subgroup of order `ℓ` kills it, unless `ℓ` divides `p - 1`.

This is the source of Serre's restriction on the primes at which a Scholz realization ramifies.  A
solution of a central embedding problem with kernel of order `ℓ` is unramified, at every prime
where the problem it solves is unramified, except at `ℓ` and at the primes congruent to one modulo
`ℓ` — and those are exactly the primes carrying a cyclic cyclotomic character of degree `ℓ` with
which the unwanted ramification can be cancelled.

## Main results

* `InverseGalois.CFT.isCyclic_inertia_of_isPGroup`: **inertia away from `ℓ` in an extension of
  `ℓ`-power degree is cyclic.**
* `InverseGalois.CFT.eq_one_of_mem_inertia_of_isPGroup`: **a homomorphism carrying such an inertia
  subgroup into a central subgroup of order `ℓ` kills it**, when the prime is neither `ℓ` nor
  congruent to one modulo `ℓ`.
* `InverseGalois.CFT.inertia_map_le_ker_of_notMem_ramifiedSet`: a solution of an embedding problem
  takes values in the kernel on inertia at a prime unramified in the field cut out by the problem.
* `InverseGalois.CFT.eq_or_dvd_sub_one_of_mem_ramifiedSet`: **the primes at which a solution of a
  central embedding problem with kernel of order `ℓ` ramifies unnecessarily are `ℓ` and the primes
  congruent to one modulo `ℓ`.**

## Tags

inertia subgroup, tame ramification, `p`-group, embedding problem, Scholz condition
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] {ℓ p : ℕ}

/-! ### Tameness -/

omit [IsGalois ℚ N] in
/-- **Inertia in an extension of `ℓ`-power degree is tame away from `ℓ`.**  The inertia subgroup is
a subgroup of an `ℓ`-group, so its order is a power of `ℓ`, which no other prime divides. -/
theorem not_dvd_card_inertia_of_isPGroup (hℓ : ℓ.Prime) (hp : p.Prime) (hne : p ≠ ℓ)
    (hG : IsPGroup ℓ Gal(N/ℚ)) (P : Ideal (𝓞 N)) :
    ¬ p ∣ Nat.card (Ideal.inertia Gal(N/ℚ) P) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hG.to_subgroup (Ideal.inertia Gal(N/ℚ) P))
  rw [hj]
  exact fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hdvd))

/-- **Inertia in an extension of `ℓ`-power degree is cyclic away from `ℓ`**, being tame there. -/
theorem isCyclic_inertia_of_isPGroup (hℓ : ℓ.Prime) (hp : p.Prime) (hne : p ≠ ℓ)
    (hG : IsPGroup ℓ Gal(N/ℚ)) (P : Ideal (𝓞 N)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    IsCyclic ↥(Ideal.inertia Gal(N/ℚ) P) :=
  isCyclic_inertia_of_not_dvd hp P (not_dvd_card_inertia_of_isPGroup hℓ hp hne hG P)

/-! ### Homomorphisms into a central subgroup of order `ℓ` -/

variable {G : Type*} [Group G]

/-- **A homomorphism of an `ℓ`-group Galois group into a central subgroup of order `ℓ` kills the
inertia subgroup at a prime which is neither `ℓ` nor congruent to one modulo `ℓ`.**  Inertia is
tame there, so the arithmetic Frobenius raises its elements to the `p`-th power; the value of the
homomorphism is central, so that conjugation leaves it alone, and it is therefore killed by
`p - 1` as well as by `ℓ`. -/
theorem eq_one_of_mem_inertia_of_isPGroup (hℓ : ℓ.Prime) (hp : p.Prime) (hne : p ≠ ℓ)
    (hnd : ¬ ℓ ∣ p - 1) (hG : IsPGroup ℓ Gal(N/ℚ)) (P : Ideal (𝓞 N)) [P.IsPrime]
    (hPo : P.LiesOver (Ideal.span {(p : ℤ)})) (ψ : Gal(N/ℚ) →* G) (C : Subgroup G)
    (hC : C ≤ Subgroup.center G) (hcard : Nat.card ↥C = ℓ)
    (hψ : (Ideal.inertia Gal(N/ℚ) P).map ψ ≤ C) {σ : Gal(N/ℚ)}
    (hσ : σ ∈ Ideal.inertia Gal(N/ℚ) P) :
    ψ σ = 1 := by
  have hmem : ψ σ ∈ C := hψ ⟨σ, hσ, rfl⟩
  have hpow : ψ σ ^ ℓ = 1 := by
    have h1 : (⟨ψ σ, hmem⟩ : ↥C) ^ ℓ = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    simpa using congrArg Subtype.val h1
  exact eq_one_of_mem_center_of_liesOver p hp hPo
    (not_dvd_card_inertia_of_isPGroup hℓ hp hne hG P) ψ ⟨σ, hσ⟩ (hC hmem) hpow
    ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hnd)

/-! ### The primes at which a solution of an embedding problem can ramify -/

variable {H : Type*} [Group H]

/-- **A solution of an embedding problem takes values in the kernel on inertia at a prime
unramified in the field cut out by the problem.** -/
theorem inertia_map_le_ker_of_notMem_ramifiedSet (f : G →* H) (ψ : Gal(N/ℚ) →* G) (hp : p.Prime)
    (h : p ∉ ramifiedSet ↥(IntermediateField.fixedField (f.comp ψ).ker)) (P : Ideal (𝓞 N))
    [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (Ideal.inertia Gal(N/ℚ) P).map ψ ≤ f.ker := by
  rintro - ⟨σ, hσ, rfl⟩
  exact MonoidHom.mem_ker.mpr (eq_one_of_notMem_ramifiedSet_fixedField_ker (f.comp ψ) hp h P hσ)

/-- **A prime other than `ℓ` at which a solution of a central embedding problem with kernel of
order `ℓ` ramifies unnecessarily is congruent to one modulo `ℓ`.**  The solution takes values in
the kernel on inertia there, and the kernel is central of order `ℓ`, so the solution would kill
inertia altogether were the prime not congruent to one modulo `ℓ`. -/
theorem dvd_sub_one_of_mem_ramifiedSet (hℓ : ℓ.Prime) (hG : IsPGroup ℓ Gal(N/ℚ)) {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hcard : Nat.card ↥f.ker = ℓ) (ψ : Gal(N/ℚ) →* G)
    (hmem : p ∈ ramifiedSet ↥(IntermediateField.fixedField ψ.ker))
    (hunr : p ∉ ramifiedSet ↥(IntermediateField.fixedField (f.comp ψ).ker)) (hne : p ≠ ℓ) :
    ℓ ∣ p - 1 := by
  have hp : p.Prime := hmem.1
  by_contra hnd
  refine notMem_ramifiedSet_fixedField_ker ψ hp (fun P h1 h2 σ hσ => ?_) hmem
  haveI := h1
  haveI := h2
  exact eq_one_of_mem_inertia_of_isPGroup hℓ hp hne hnd hG P h2 ψ f.ker hZ hcard
    (inertia_map_le_ker_of_notMem_ramifiedSet f ψ hp hunr P) hσ

/-- **The primes at which a solution of a central embedding problem with kernel of order `ℓ`
ramifies unnecessarily are `ℓ` and the primes congruent to one modulo `ℓ`**, which are exactly the
primes carrying a cyclic cyclotomic character of degree `ℓ`. -/
theorem eq_or_dvd_sub_one_of_mem_ramifiedSet (hℓ : ℓ.Prime) (hG : IsPGroup ℓ Gal(N/ℚ)) {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hcard : Nat.card ↥f.ker = ℓ) (ψ : Gal(N/ℚ) →* G)
    (hmem : p ∈ ramifiedSet ↥(IntermediateField.fixedField ψ.ker))
    (hunr : p ∉ ramifiedSet ↥(IntermediateField.fixedField (f.comp ψ).ker)) :
    p = ℓ ∨ ℓ ∣ p - 1 := by
  by_cases hne : p = ℓ
  · exact Or.inl hne
  · exact Or.inr (dvd_sub_one_of_mem_ramifiedSet hℓ hG hZ hcard ψ hmem hunr hne)

end InverseGalois.CFT
