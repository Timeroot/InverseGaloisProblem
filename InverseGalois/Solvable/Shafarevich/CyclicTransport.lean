/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.RamifiedFamily
import InverseGalois.Solvable.Shafarevich.RamifiedHom

/-!
# Confinement and cyclicity are a condition at finitely many named primes

What the arithmetic is left to arrange for a lift is that its new ramification over the base
realization be *confined* — occurring only where the solution below already ramifies or else kills
the whole decomposition subgroup — and that its local image be cyclic where it does occur.  Both
conditions quantify over every prime of the whole extension, and neither mentions anything but the
decomposition and inertia subgroups of a prime and the values three homomorphisms take on them.

Moving a prime by an automorphism conjugates both subgroups, so it conjugates every clause:
ramifying is preserved, killing a subgroup is preserved, and the element bounding the local image is
replaced by its conjugate, which is again a value on the moved decomposition subgroup.  Only
finitely many orbits of primes carry any ramification of the lift at all, and one prime of each can
be named, so both conditions become checks at finitely many primes.

## Main definitions

* `InverseGalois.Shafarevich.RamifiesAt` — the lift ramifies over the base realization at a prime.
* `InverseGalois.Shafarevich.IsCyclicSplitAt` — the base realization splits completely at a prime
  and the local image of the lift is cyclic there.
* `InverseGalois.Shafarevich.IsConfinedAt` — at a prime, the solution below either ramifies over
  the base realization or kills the whole decomposition subgroup.
* `InverseGalois.Shafarevich.IsConfinedRamifiedHom` — **the new ramification of a lift is
  confined.**

## Main results

* `InverseGalois.Shafarevich.RamifiesAt.smul`, `InverseGalois.Shafarevich.IsCyclicSplitAt.smul`,
  `InverseGalois.Shafarevich.IsConfinedAt.smul` — **the clauses move with the prime.**
* `InverseGalois.Shafarevich.isCyclicSplitHom_of_family`,
  `InverseGalois.Shafarevich.isConfinedRamifiedHom_of_family` — either condition holds as soon as
  it holds at a family of primes meeting every orbit at which the lift ramifies.
* `InverseGalois.Shafarevich.exists_family_cyclicSplit_confined` — **confinement and cyclicity are
  a check at finitely many primes**, for a lift with open kernel.

## Tags

Shafarevich's theorem, embedding problem, ramification, inertia subgroup, decomposition group
-/

namespace InverseGalois.Shafarevich

open MulAction NumberField

open InverseGalois.CFT

open scoped Pointwise

variable {U W W' : Type*} [Group U] [Group W] [Group W'] {k Ω : Type*} [Field k] [Field Ω]
  [Algebra k Ω]

/-! ### Conjugating a value -/

/-- A conjugate of a nontrivial element is nontrivial. -/
private theorem conj_ne_one {G : Type*} [Group G] {a b : G} (hb : b ≠ 1) : a * b * a⁻¹ ≠ 1 := by
  intro h
  refine hb ?_
  have hbb : b = a⁻¹ * (a * b * a⁻¹) * a := by group
  rw [hbb, h]
  group

/-! ### Ramifying at a prime -/

/-- **The homomorphism ramifies over the base realization at a prime**: some element of inertia
which the base realization kills is not killed by the homomorphism. -/
def RamifiesAt (φ : Gal(Ω/k) →* U) (Φ : Gal(Ω/k) →* W) (P : Ideal (𝓞 Ω)) : Prop :=
  ∃ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 ∧ Φ x ≠ 1

/-- **Ramifying moves with the prime**, inertia at a moved prime being the conjugate of inertia. -/
theorem RamifiesAt.smul {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W} {P : Ideal (𝓞 Ω)}
    (h : RamifiesAt φ Φ P) (ρ : Gal(Ω/k)) : RamifiesAt φ Φ (ρ • P) := by
  obtain ⟨x, hxI, hxφ, hxΦ⟩ := h
  refine ⟨ρ * x * ρ⁻¹, ?_, ?_, ?_⟩
  · exact mem_inertia_smul_iff.2 (by rwa [show ρ⁻¹ * (ρ * x * ρ⁻¹) * ρ = x from by group])
  · rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, hxφ, mul_one, mul_inv_cancel]
  · rw [_root_.map_mul, _root_.map_mul, _root_.map_inv]
    exact conj_ne_one hxΦ

/-- Ramifying at a moved prime is ramifying at the prime. -/
theorem ramifiesAt_smul_iff {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W} {P : Ideal (𝓞 Ω)}
    {ρ : Gal(Ω/k)} : RamifiesAt φ Φ (ρ • P) ↔ RamifiesAt φ Φ P :=
  ⟨fun h => by simpa using h.smul ρ⁻¹, fun h => h.smul ρ⟩

/-! ### Splitting with a cyclic local image, at one prime -/

/-- The base realization kills the decomposition subgroup of a prime and the values of the
homomorphism there lie in the powers of one of them. -/
def IsCyclicSplitAt (φ : Gal(Ω/k) →* U) (Φ : Gal(Ω/k) →* W) (P : Ideal (𝓞 Ω)) : Prop :=
  (∀ x ∈ stabilizer Gal(Ω/k) P, φ x = 1) ∧
    ∃ x₀ ∈ stabilizer Gal(Ω/k) P, ∀ x ∈ stabilizer Gal(Ω/k) P, Φ x ∈ Subgroup.zpowers (Φ x₀)

/-- The condition is the conjunction, over the primes where the homomorphism ramifies over the base
realization, of its clauses at that prime. -/
theorem isCyclicSplitHom_iff_forall_at {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W} :
    IsCyclicSplitHom φ Φ ↔ ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → RamifiesAt φ Φ P →
      IsCyclicSplitAt φ Φ P :=
  Iff.rfl

/-- **Splitting with a cyclic local image moves with the prime.**  The generator is replaced by its
conjugate, which is again a value on the moved decomposition subgroup, and every value there is the
conjugate of a value on the original one. -/
theorem IsCyclicSplitAt.smul {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W} {P : Ideal (𝓞 Ω)}
    (h : IsCyclicSplitAt φ Φ P) (ρ : Gal(Ω/k)) : IsCyclicSplitAt φ Φ (ρ • P) := by
  obtain ⟨hsplit, x₀, hx₀, hgen⟩ := h
  have key : ∀ x ∈ stabilizer Gal(Ω/k) (ρ • P), ρ⁻¹ * x * ρ ∈ stabilizer Gal(Ω/k) P :=
    fun _ hx => mem_stabilizer_smul_iff.1 hx
  have hconj : ∀ x : Gal(Ω/k), Φ x = Φ ρ * Φ (ρ⁻¹ * x * ρ) * (Φ ρ)⁻¹ := by
    intro x
    simp only [_root_.map_mul, _root_.map_inv]
    group
  refine ⟨fun x hx => ?_, ρ * x₀ * ρ⁻¹, ?_, fun x hx => ?_⟩
  · have hx1 := hsplit _ (key x hx)
    have hxx : φ ρ * φ (ρ⁻¹ * x * ρ) * (φ ρ)⁻¹ = φ x := by
      simp only [_root_.map_mul, _root_.map_inv]
      group
    rw [← hxx, hx1, mul_one, mul_inv_cancel]
  · exact mem_stabilizer_smul_iff.2 (by rwa [show ρ⁻¹ * (ρ * x₀ * ρ⁻¹) * ρ = x₀ from by group])
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hgen _ (key x hx))
    refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
    rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, conj_zpow, hi, ← hconj x]

/-- **Splitting with a cyclic local image holds as soon as it holds at a family of primes meeting
every orbit at which the homomorphism ramifies.** -/
theorem isCyclicSplitHom_of_family {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W} {ι : Type*}
    {Pr : ι → Ideal (𝓞 Ω)}
    (hfam : ∀ Q : Ideal (𝓞 Ω), Q.IsPrime → Q ≠ ⊥ → RamifiesAt φ Φ Q →
      ∃ (ν : ι) (ρ : Gal(Ω/k)), Q = ρ • Pr ν)
    (h : ∀ ν, RamifiesAt φ Φ (Pr ν) → IsCyclicSplitAt φ Φ (Pr ν)) : IsCyclicSplitHom φ Φ := by
  intro Q hQp hQbot hram
  obtain ⟨ν, ρ, rfl⟩ := hfam Q hQp hQbot hram
  exact (h ν (ramifiesAt_smul_iff.1 hram)).smul ρ

/-! ### Confinement, at one prime -/

/-- At a prime, the solution below either ramifies over the base realization or takes no value at
all on the decomposition subgroup. -/
def IsConfinedAt (φ : Gal(Ω/k) →* U) (Φ : Gal(Ω/k) →* W) (P : Ideal (𝓞 Ω)) : Prop :=
  RamifiesAt φ Φ P ∨ ∀ x ∈ stabilizer Gal(Ω/k) P, Φ x = 1

/-- **The new ramification of a lift is confined**: at every prime where the lift ramifies over the
base realization, the solution below either ramifies there too or kills the whole decomposition
subgroup. -/
def IsConfinedRamifiedHom (φ : Gal(Ω/k) →* U) (Φ : Gal(Ω/k) →* W) (Ψ : Gal(Ω/k) →* W') : Prop :=
  ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → RamifiesAt φ Ψ P → IsConfinedAt φ Φ P

/-- **Confinement moves with the prime.** -/
theorem IsConfinedAt.smul {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W} {P : Ideal (𝓞 Ω)}
    (h : IsConfinedAt φ Φ P) (ρ : Gal(Ω/k)) : IsConfinedAt φ Φ (ρ • P) := by
  rcases h with hram | h1
  · exact Or.inl (hram.smul ρ)
  · refine Or.inr fun x hx => ?_
    have hx1 := h1 _ (mem_stabilizer_smul_iff.1 hx)
    have hxx : Φ ρ * Φ (ρ⁻¹ * x * ρ) * (Φ ρ)⁻¹ = Φ x := by
      simp only [_root_.map_mul, _root_.map_inv]
      group
    rw [← hxx, hx1, mul_one, mul_inv_cancel]

/-- **Confinement holds as soon as it holds at a family of primes meeting every orbit at which the
lift ramifies.** -/
theorem isConfinedRamifiedHom_of_family {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W}
    {Ψ : Gal(Ω/k) →* W'} {ι : Type*} {Pr : ι → Ideal (𝓞 Ω)}
    (hfam : ∀ Q : Ideal (𝓞 Ω), Q.IsPrime → Q ≠ ⊥ → RamifiesAt φ Ψ Q →
      ∃ (ν : ι) (ρ : Gal(Ω/k)), Q = ρ • Pr ν)
    (h : ∀ ν, RamifiesAt φ Ψ (Pr ν) → IsConfinedAt φ Φ (Pr ν)) :
    IsConfinedRamifiedHom φ Φ Ψ := by
  intro Q hQp hQbot hram
  obtain ⟨ν, ρ, rfl⟩ := hfam Q hQp hQbot hram
  exact (h ν (ramifiesAt_smul_iff.1 hram)).smul ρ

/-! ### Both conditions are a finite check -/

section Finite

variable [NumberField k] [IsGalois k Ω]

/-- **Confinement and cyclicity are a check at finitely many primes.**

The primes at which the lift ramifies at all meet finitely many orbits, one prime of each can be
named, and both conditions carry from a named prime to its whole orbit. -/
theorem exists_family_cyclicSplit_confined {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W}
    {Ψ : Gal(Ω/k) →* W'} (hΨ : IsOpenNormal Ψ.ker) :
    ∃ (s : ℕ) (Pr : Fin s → Ideal (𝓞 Ω)), (∀ ν, (Pr ν).IsPrime) ∧ (∀ ν, Pr ν ≠ ⊥) ∧
      ((∀ ν, RamifiesAt φ Ψ (Pr ν) → IsCyclicSplitAt φ Ψ (Pr ν) ∧ IsConfinedAt φ Φ (Pr ν)) →
        IsCyclicSplitHom φ Ψ ∧ IsConfinedRamifiedHom φ Φ Ψ) := by
  obtain ⟨s, Pr, hp, hbot, hfam⟩ := exists_ramified_family hΨ
  have hfam' : ∀ Q : Ideal (𝓞 Ω), Q.IsPrime → Q ≠ ⊥ → RamifiesAt φ Ψ Q →
      ∃ (ν : Fin s) (ρ : Gal(Ω/k)), Q = ρ • Pr ν := by
    rintro Q hQp hQbot ⟨x, hxI, -, hxΨ⟩
    exact hfam Q hQp hQbot ⟨x, hxI, hxΨ⟩
  exact ⟨s, Pr, hp, hbot, fun h => ⟨isCyclicSplitHom_of_family hfam' fun ν hν => (h ν hν).1,
    isConfinedRamifiedHom_of_family hfam' fun ν hν => (h ν hν).2⟩⟩

end Finite

end InverseGalois.Shafarevich
