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
* `InverseGalois.Shafarevich.IsCyclicRamifiedHom` — the same restriction with the roots of unity
  rider dropped, a condition purely about the values the homomorphism takes.

## Main results

* `InverseGalois.Shafarevich.IsSplitTotallyRamifiedHom.comp` — the restriction is inherited by the
  image of a homomorphism under any homomorphism of the target.
* `InverseGalois.Shafarevich.isSplitTotallyRamifiedHom_of_ker_le` — a homomorphism which is trivial
  wherever the base realization is carries the restriction.
* `InverseGalois.Shafarevich.isSplitTotallyRamifiedHom_of_le_zpowers` — **a homomorphism whose
  values on a decomposition subgroup lie in the powers of a single element killed by the prime
  carries the restriction**, the totally ramified clause coming for free from the prime order.
* `InverseGalois.Shafarevich.isSplitTotallyRamifiedHom_of_isCyclicRamifiedHom` — **a uniform bound
  on the order of the values restores the roots of unity rider.**

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

/-- A nontrivial power of an element killed by a prime exponent has that element among its own
powers, the exponent it is reached by being prime to the prime. -/
theorem mem_zpowers_of_pow_prime {G : Type*} [Group G] {ℓ : ℕ} (hℓ : ℓ.Prime) {c a : G}
    (hc : c ^ ℓ = 1) (ha : a ∈ Subgroup.zpowers c) (ha1 : a ≠ 1) : c ∈ Subgroup.zpowers a := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hcz : c ^ (ℓ : ℤ) = 1 := by rw [zpow_natCast, hc]
  have hnd : ¬ ℓ ∣ i.natAbs := by
    intro hd
    refine ha1 ?_
    obtain ⟨j, hj⟩ : (ℓ : ℤ) ∣ i := Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 hd)
    rw [← hi, hj, zpow_mul, hcz, one_zpow]
  have hcop : IsCoprime i (ℓ : ℤ) := by
    refine Int.isCoprime_iff_gcd_eq_one.2 ?_
    have h1 : Nat.Coprime ℓ i.natAbs := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hnd
    have h2 : Nat.gcd i.natAbs ℓ = 1 := h1.symm
    simpa [Int.gcd] using h2
  obtain ⟨s, t, hst⟩ := hcop
  refine Subgroup.mem_zpowers_iff.2 ⟨s, ?_⟩
  have hkey : i * s = 1 - ℓ * t := by linear_combination hst
  rw [← hi, ← zpow_mul, hkey, sub_eq_add_neg, zpow_add, zpow_neg, zpow_mul, hcz, one_zpow, inv_one,
    mul_one, zpow_one]

/-- **A homomorphism whose values on a decomposition subgroup lie in the powers of a single element
killed by the prime carries the restriction.**

The clause asking the homomorphism to be totally ramified is the one which would otherwise call for
an arithmetic input, and here it costs nothing: the element of inertia witnessing the ramification
already generates the whole local image, because the image is bounded by an element of prime order,
so every value on the decomposition subgroup is a power of the witness and therefore a value on
inertia.  What is left to supply is that the base realization kills the decomposition subgroup, that
the local image is bounded by the powers of an element the prime kills, and the roots of unity
rider, which for such an element asks only for the roots of unity of the prime squared. -/
theorem isSplitTotallyRamifiedHom_of_le_zpowers {φ : Gal(Ω/k) →* U} {Φ : Gal(Ω/k) →* W}
    (hℓ : ℓ.Prime)
    (h : ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      ∀ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 → Φ x ≠ 1 →
        ∃ c : W, (∀ y ∈ stabilizer Gal(Ω/k) P, φ y = 1) ∧
          (∀ y ∈ stabilizer Gal(Ω/k) P, Φ y ∈ Subgroup.zpowers c) ∧ c ^ ℓ = 1 ∧
            ∀ ζ : Ωˣ, ζ ^ (ℓ * ℓ) = 1 → ∀ y ∈ stabilizer Gal(Ω/k) P, y • ζ = ζ) :
    IsSplitTotallyRamifiedHom ℓ φ Φ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  rintro P hPp hPbot ⟨x, hxI, hxφ, hxΦ⟩
  obtain ⟨c, hsplit, hle, hcpow, hμ⟩ := h P hPp hPbot x hxI hxφ hxΦ
  have hxmem : Φ x ∈ Subgroup.zpowers c := hle x (Ideal.inertia_le_stabilizer P hxI)
  have hcmem : c ∈ Subgroup.zpowers (Φ x) := mem_zpowers_of_pow_prime hℓ hcpow hxmem hxΦ
  have hcne : c ≠ 1 := fun hc => hxΦ (by
    rw [hc, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hxmem
    exact hxmem)
  have horder : orderOf c = ℓ := orderOf_eq_prime hcpow hcne
  refine ⟨hsplit, fun y hy => ?_, c, hle, fun ζ hζ y hy => ?_⟩
  · obtain ⟨i, hi⟩ :=
      Subgroup.mem_zpowers_iff.1 (Subgroup.zpowers_le.2 hcmem (hle y hy))
    exact ⟨x ^ i, zpow_mem hxI i, by rw [_root_.map_zpow, hi]⟩
  · exact hμ ζ (by rwa [horder] at hζ) y hy

/-! ### The restriction with the roots of unity taken out of it -/

variable (ℓ) in
/-- **At a prime where the homomorphism ramifies over the base realization, the base realization
splits completely there and the homomorphism is cyclic and totally ramified** — the restriction
with the roots of unity rider dropped.

The rider is the only clause of the restriction which mentions the field rather than the values of
the homomorphism, and it is the only one which cannot be read off a single prime in isolation: it
asks the local field to carry the roots of unity of the prime times the order of the local image,
an order which grows as the ladder is climbed.  Dropping it leaves a condition purely about values,
and the rider is then restored once and for all from a single bound on the order of every value —
which is what the exponent of the test group supplies.  The element bounding the local image is
asked to be one of the values, so that the bound applies to it. -/
def IsCyclicRamifiedHom (φ : Gal(Ω/k) →* U) (Φ : Gal(Ω/k) →* W) : Prop :=
  ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
    (∃ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 ∧ Φ x ≠ 1) →
      (∀ x ∈ stabilizer Gal(Ω/k) P, φ x = 1) ∧
        (∀ x ∈ stabilizer Gal(Ω/k) P, ∃ y ∈ Ideal.inertia Gal(Ω/k) P, Φ x = Φ y) ∧
          ∃ x₀ ∈ stabilizer Gal(Ω/k) P,
            ∀ x ∈ stabilizer Gal(Ω/k) P, Φ x ∈ Subgroup.zpowers (Φ x₀)

/-- **A uniform bound on the order of the values restores the roots of unity rider.**

Where the homomorphism ramifies over the base realization the base realization kills the whole
decomposition subgroup, so every value there is killed by the bound; in particular the value
bounding the local image is, and the roots of unity the rider asks for are among those of order the
prime times the bound, which the base realization is asked to fix outright. -/
theorem isSplitTotallyRamifiedHom_of_isCyclicRamifiedHom {M : ℕ} {φ : Gal(Ω/k) →* U}
    {Φ : Gal(Ω/k) →* W} (htors : ∀ x, φ x = 1 → Φ x ^ M = 1)
    (hmu : ∀ ζ : Ωˣ, ζ ^ (ℓ * M) = 1 → ∀ σ ∈ φ.ker, σ • ζ = ζ)
    (h : IsCyclicRamifiedHom φ Φ) : IsSplitTotallyRamifiedHom ℓ φ Φ := by
  intro P hPp hPbot hram
  obtain ⟨hsplit, htot, x₀, hx₀, hgen⟩ := h P hPp hPbot hram
  refine ⟨hsplit, htot, Φ x₀, hgen, fun ζ hζ x hx => ?_⟩
  refine hmu ζ ?_ x (hsplit x hx)
  obtain ⟨d, hd⟩ : ℓ * orderOf (Φ x₀) ∣ ℓ * M :=
    mul_dvd_mul_left ℓ (orderOf_dvd_of_pow_eq_one (htors x₀ (hsplit x₀ hx₀)))
  rw [hd, pow_mul, hζ, one_pow]

end InverseGalois.Shafarevich
