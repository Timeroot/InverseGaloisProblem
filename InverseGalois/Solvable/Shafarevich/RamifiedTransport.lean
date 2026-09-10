/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.RamifiedFamily
import InverseGalois.Solvable.Shafarevich.RamifiedHom

/-!
# The ramification restriction is a condition at finitely many named primes

The restriction the ladder asks of a solution quantifies over every prime of the whole extension,
of which there are infinitely many, but its three clauses only ever speak of the decomposition and
inertia subgroups of the prime and of the values two homomorphisms take on them.  Moving a prime by
an automorphism conjugates both subgroups, so it conjugates all three clauses: the base realization
still kills the decomposition subgroup, the values on the decomposition subgroup are still values on
inertia, and the element bounding the local image is replaced by its conjugate, whose order — the
only thing the roots of unity rider reads off it — is unchanged.

Only finitely many orbits of primes ramify, and one prime of each is named.  So checking the three
clauses at the named primes checks them everywhere, and the restriction becomes a finite condition.

## Main definitions

* `InverseGalois.Shafarevich.IsSplitTotallyRamifiedAt` — the three clauses of the restriction, at
  one prime.

## Main results

* `InverseGalois.Shafarevich.IsSplitTotallyRamifiedAt.smul` — **the clauses of the restriction move
  with the prime.**
* `InverseGalois.Shafarevich.isSplitTotallyRamifiedHom_of_family` — **the restriction holds as soon
  as it holds at a family of primes meeting every orbit at which the homomorphism ramifies.**

## Tags

Shafarevich's theorem, embedding problem, ramification, inertia subgroup, decomposition group
-/

namespace InverseGalois.Shafarevich

open MulAction NumberField

open InverseGalois.CFT

open scoped Pointwise

variable (ℓ : ℕ) {U W : Type*} [Group U] [Group W] {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-! ### The restriction at one prime -/

/-- The three clauses of the ramification restriction, at one prime: the base realization kills the
decomposition subgroup, the homomorphism takes no value there which it does not already take on
inertia, and its values are bounded by the powers of a single element whose order, times the prime,
names roots of unity the decomposition subgroup fixes. -/
def IsSplitTotallyRamifiedAt (φ : Gal(Ω/k) →* U) (Φ : Gal(Ω/k) →* W) (P : Ideal (𝓞 Ω)) : Prop :=
  (∀ x ∈ stabilizer Gal(Ω/k) P, φ x = 1) ∧
    (∀ x ∈ stabilizer Gal(Ω/k) P, ∃ y ∈ Ideal.inertia Gal(Ω/k) P, Φ x = Φ y) ∧
      ∃ c, (∀ x ∈ stabilizer Gal(Ω/k) P, Φ x ∈ Subgroup.zpowers c) ∧
        ∀ ζ : Ωˣ, ζ ^ (ℓ * orderOf c) = 1 → ∀ x ∈ stabilizer Gal(Ω/k) P, x • ζ = ζ

variable {ℓ}

/-- The restriction is the conjunction, over the primes where the homomorphism ramifies over the
base realization, of its clauses at that prime. -/
theorem isSplitTotallyRamifiedHom_iff_forall_at {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W} :
    IsSplitTotallyRamifiedHom ℓ φ Φ ↔ ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      (∃ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 ∧ Φ x ≠ 1) → IsSplitTotallyRamifiedAt ℓ φ Φ P :=
  Iff.rfl

/-! ### Moving the prime -/

/-- An element whose conjugate is trivial is trivial. -/
private theorem eq_one_of_conj_eq_one {G : Type*} [Group G] {a b : G} (h : a⁻¹ * b * a = 1) :
    b = 1 := by
  have hb : b = a * (a⁻¹ * b * a) * a⁻¹ := by group
  rw [hb, h, mul_one, mul_inv_cancel]

/-- **The clauses of the restriction move with the prime.**

The decomposition and inertia subgroups of a moved prime are the conjugates of those of the prime,
so each clause is the conjugate of the clause at the prime: the base realization killing a subgroup
is preserved by conjugation, a value on the decomposition subgroup is the conjugate of a value there
and hence of a value on inertia, and the element bounding the local image is replaced by its
conjugate.  The roots of unity rider reads only the order of that element, which conjugation does
not change, and the root of unity itself is moved back by the automorphism. -/
theorem IsSplitTotallyRamifiedAt.smul {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W} {P : Ideal (𝓞 Ω)}
    (h : IsSplitTotallyRamifiedAt ℓ φ Φ P) (ρ : Gal(Ω/k)) :
    IsSplitTotallyRamifiedAt ℓ φ Φ (ρ • P) := by
  obtain ⟨hsplit, htot, c, hc, hμ⟩ := h
  have key : ∀ x ∈ stabilizer Gal(Ω/k) (ρ • P), ρ⁻¹ * x * ρ ∈ stabilizer Gal(Ω/k) P :=
    fun _ hx => mem_stabilizer_smul_iff.1 hx
  have hconj : ∀ x : Gal(Ω/k), Φ x = Φ ρ * Φ (ρ⁻¹ * x * ρ) * (Φ ρ)⁻¹ := by
    intro x
    simp only [_root_.map_mul, _root_.map_inv]
    group
  have hord : orderOf (Φ ρ * c * (Φ ρ)⁻¹) = orderOf c := by
    simpa using
      orderOf_injective (MulAut.conj (Φ ρ)).toMonoidHom (MulAut.conj (Φ ρ)).injective c
  refine ⟨fun x hx => ?_, fun x hx => ?_, Φ ρ * c * (Φ ρ)⁻¹, fun x hx => ?_, fun ζ hζ x hx => ?_⟩
  · refine eq_one_of_conj_eq_one (a := φ ρ) ?_
    have hx1 := hsplit _ (key x hx)
    simpa only [_root_.map_mul, _root_.map_inv] using hx1
  · obtain ⟨y, hyI, hy⟩ := htot _ (key x hx)
    refine ⟨ρ * y * ρ⁻¹, ?_, ?_⟩
    · refine mem_inertia_smul_iff.2 ?_
      have hyy : ρ⁻¹ * (ρ * y * ρ⁻¹) * ρ = y := by group
      rwa [hyy]
    · rw [hconj x, hy, _root_.map_mul, _root_.map_mul, _root_.map_inv]
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hc _ (key x hx))
    refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
    rw [conj_zpow, hi, ← hconj x]
  · have hζ' : (ρ⁻¹ • ζ) ^ (ℓ * orderOf c) = 1 := by
      rw [← smul_pow', ← hord, hζ, smul_one]
    have hfix := hμ (ρ⁻¹ • ζ) hζ' _ (key x hx)
    refine smul_left_cancel ρ⁻¹ ?_
    rw [← hfix, mul_smul, mul_smul, smul_inv_smul]

/-! ### The restriction from a family -/

/-- **The restriction holds as soon as it holds at a family of primes meeting every orbit at which
the homomorphism ramifies.**  A prime where the homomorphism ramifies over the base realization is
carried by an automorphism to a member of the family, and the clauses travel with it. -/
theorem isSplitTotallyRamifiedHom_of_family {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W} {ι : Type*}
    {Pr : ι → Ideal (𝓞 Ω)}
    (hfam : ∀ Q : Ideal (𝓞 Ω), Q.IsPrime → Q ≠ ⊥ →
      (∃ x ∈ Ideal.inertia Gal(Ω/k) Q, φ x = 1 ∧ Φ x ≠ 1) →
        ∃ (ν : ι) (ρ : Gal(Ω/k)), Q = ρ • Pr ν)
    (h : ∀ ν, IsSplitTotallyRamifiedAt ℓ φ Φ (Pr ν)) : IsSplitTotallyRamifiedHom ℓ φ Φ := by
  intro Q hQp hQbot hram
  obtain ⟨ν, ρ, rfl⟩ := hfam Q hQp hQbot hram
  exact (h ν).smul ρ

end InverseGalois.Shafarevich
