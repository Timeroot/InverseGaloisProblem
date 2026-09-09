/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The ramification restriction, read for a homomorphism to an arbitrary group

The restriction the ladder of Shafarevich's theorem asks a solution to carry is a statement about
the values a homomorphism out of the Galois group takes on the decomposition and inertia subgroups
of a prime.  Nothing in it mentions the group the homomorphism lands in, so it is stated here for an
arbitrary target and specialised afterwards to the groups of the ladder.

Stating it for an arbitrary target is what lets a solution be assembled in a group which is
convenient for the arithmetic — a wreath product, say, whose kernel is a group of functions and
whose Kummer theory is transparent — and only then pushed forward to the group the ladder names.
Every clause is a statement about values, so following a homomorphism can only identify values and
the restriction is inherited.

## Main definitions

* `InverseGalois.Shafarevich.IsSplitTotallyRamifiedHom` — **at a prime where the homomorphism
  ramifies over the base realization, the base realization splits completely, the homomorphism is
  cyclic and totally ramified there, and the local field carries the roots of unity the next layer
  calls for.**

## Main results

* `InverseGalois.Shafarevich.IsSplitTotallyRamifiedHom.comp` — the restriction is inherited by the
  image of a homomorphism under any homomorphism of the target.
* `InverseGalois.Shafarevich.isSplitTotallyRamifiedHom_of_ker_le` — a homomorphism which is trivial
  wherever the base realization is carries the restriction.

## Tags

Shafarevich's theorem, embedding problem, ramification, inertia subgroup, decomposition group
-/

namespace InverseGalois.Shafarevich

open MulAction NumberField

open scoped Pointwise

variable (ℓ : ℕ) {U W W' : Type*} [Group U] [Group W] [Group W'] {k Ω : Type*} [Field k] [Field Ω]
  [Algebra k Ω]

/-- **At a prime where the homomorphism ramifies over the base realization, the base realization
splits completely there and the homomorphism is cyclic and totally ramified.**

The three clauses are read off the two subgroups a prime of the ring of integers of the whole
extension carries: its stabiliser, which is the decomposition subgroup, and its inertia subgroup,
the automorphisms acting trivially on the residue ring.  Ramifying over the base realization is
having an element of inertia which the base realization kills and the homomorphism does not;
splitting completely is the base realization killing the whole decomposition subgroup; being totally
ramified is the homomorphism taking no value on the decomposition subgroup which it does not already
take on inertia; and being cyclic is asked in the form that bounds it, the values on the
decomposition subgroup lying in the powers of a single element.  That element carries a rider: the
roots of unity of the prime times its order are fixed by the decomposition subgroup, which is to say
that the local field at the prime already contains the roots of unity the next layer will call
for. -/
def IsSplitTotallyRamifiedHom (φ : Gal(Ω/k) →* U) (Φ : Gal(Ω/k) →* W) : Prop :=
  ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
    (∃ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 ∧ Φ x ≠ 1) →
      (∀ x ∈ stabilizer Gal(Ω/k) P, φ x = 1) ∧
        (∀ x ∈ stabilizer Gal(Ω/k) P, ∃ y ∈ Ideal.inertia Gal(Ω/k) P, Φ x = Φ y) ∧
          ∃ c, (∀ x ∈ stabilizer Gal(Ω/k) P, Φ x ∈ Subgroup.zpowers c) ∧
            ∀ ζ : Ωˣ, ζ ^ (ℓ * orderOf c) = 1 → ∀ x ∈ stabilizer Gal(Ω/k) P, x • ζ = ζ

variable {ℓ}

/-- **The restriction is inherited by the image of a homomorphism under any homomorphism of the
target.**  Every clause is a statement about the values the homomorphism takes, and following a
homomorphism can only identify values: a prime where the image ramifies is a prime where the
homomorphism already ramified, and there the clauses transport one by one, the order of the
generator of the local image only dropping to a divisor. -/
theorem IsSplitTotallyRamifiedHom.comp {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W}
    (h : IsSplitTotallyRamifiedHom ℓ φ Φ) (g : W →* W') :
    IsSplitTotallyRamifiedHom ℓ φ (g.comp Φ) := by
  rintro P hPp hPbot ⟨x, hxI, hxφ, hxg⟩
  obtain ⟨hsplit, htot, c, hc, hμ⟩ := h P hPp hPbot
    ⟨x, hxI, hxφ, fun hx => hxg (by rw [MonoidHom.comp_apply, hx, _root_.map_one])⟩
  refine ⟨hsplit, fun y hy => ?_, g c, fun y hy => ?_, fun ζ hζ y hy => ?_⟩
  · obtain ⟨z, hzI, hz⟩ := htot y hy
    exact ⟨z, hzI, by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hz]⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hc y hy)
    exact Subgroup.mem_zpowers_iff.2 ⟨i, by rw [← _root_.map_zpow, hi, MonoidHom.comp_apply]⟩
  · obtain ⟨s, hs⟩ := mul_dvd_mul_left ℓ (orderOf_map_dvd g c)
    refine hμ ζ ?_ y hy
    rw [hs, pow_mul, hζ, one_pow]

/-- **A homomorphism which is trivial wherever the base realization is carries the restriction**,
there being nothing to check: no prime ramifies over the base realization at all. -/
theorem isSplitTotallyRamifiedHom_of_ker_le {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W}
    (h : ∀ x, φ x = 1 → Φ x = 1) : IsSplitTotallyRamifiedHom ℓ φ Φ := by
  rintro P - - ⟨x, -, hxφ, hxΦ⟩
  exact absurd (h x hxφ) hxΦ

end InverseGalois.Shafarevich
