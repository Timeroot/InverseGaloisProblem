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
* `InverseGalois.Shafarevich.IsCyclicSplitHom` — the same restriction with total ramification
  dropped as well, leaving splitting and a cyclic local image.

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
* `InverseGalois.Shafarevich.isCyclicRamifiedHom_of_isCyclicSplitHom` — **a cyclic local image over
  a totally ramified one is itself totally ramified**, so a construction never has to arrange total
  ramification by hand.

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

/-- **An element of prime power order lies in a subgroup of its own powers as soon as the subgroup
is nontrivial and comes within a factor the prime kills of it.**

If the element differs from a member of the subgroup by one the prime kills, then the `ℓ`-th power
of the element already lies in the subgroup, the two `ℓ`-th powers agreeing.  Either the factor is
itself an `ℓ`-th power of the element, and then it lies in the subgroup along with it; or it is not,
and then the order of the element is at most the prime, so any nontrivial member of the subgroup
generates the element outright. -/
theorem mem_of_pow_prime_pow {G : Type*} [Group G] {ℓ : ℕ} (hℓ : ℓ.Prime) {g : G} {a : ℕ}
    (hg : g ^ ℓ ^ a = 1) {H : Subgroup G} (hH : H ≤ Subgroup.zpowers g) (hHne : H ≠ ⊥)
    {y : G} (hyH : y ∈ H) (hy : (g * y⁻¹) ^ ℓ = 1) : g ∈ H := by
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.1 (hH hyH)
  obtain ⟨t, ht⟩ : ∃ t : ℤ, g ^ t = g * y⁻¹ :=
    Subgroup.mem_zpowers_iff.1 (mul_mem (Subgroup.mem_zpowers g) (inv_mem (hH hyH)))
  have hsum : g ^ (t + s) = g := by
    rw [zpow_add, ht, hs]
    group
  have htl : g ^ (t * (ℓ : ℤ)) = 1 := by rw [zpow_mul, ht, zpow_natCast, hy]
  have hts : g ^ (t + s - 1) = 1 := by rw [zpow_sub, hsum, zpow_one, mul_inv_cancel]
  have hgl : g ^ (ℓ : ℕ) ∈ H := by
    have h1 : g ^ ((s - 1) * (ℓ : ℤ)) = 1 := by
      have he : (s - 1) * (ℓ : ℤ) = (t + s - 1) * ℓ - t * ℓ := by ring
      rw [he, zpow_sub, zpow_mul, hts, one_zpow, htl, mul_inv_cancel]
    have hyl : y ^ (ℓ : ℕ) = g ^ (ℓ : ℕ) := by
      have he : s * (ℓ : ℤ) = (s - 1) * ℓ + ℓ := by ring
      rw [← hs, ← zpow_natCast (g ^ s) ℓ, ← zpow_mul, ← zpow_natCast g ℓ, he, zpow_add, h1,
        one_mul]
    rw [← hyl]
    exact pow_mem hyH ℓ
  by_cases hdvd : (ℓ : ℤ) ∣ t
  · obtain ⟨u, hu⟩ := hdvd
    have hmem : g * y⁻¹ ∈ H := by
      rw [← ht, hu, zpow_mul, zpow_natCast]
      exact zpow_mem hgl u
    simpa using mul_mem hmem hyH
  · obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hℓ).1 (orderOf_dvd_of_pow_eq_one hg)
    have hordz : ((ℓ : ℤ) ^ b) ∣ t * (ℓ : ℤ) := by
      have h := orderOf_dvd_iff_zpow_eq_one.2 htl
      rwa [hb, Nat.cast_pow] at h
    have hb1 : b ≤ 1 := by
      by_contra hcon
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
      have hlne : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hℓ.ne_zero
      have h2 : ((ℓ : ℤ) ^ (c + 1)) * (ℓ : ℤ) ∣ t * (ℓ : ℤ) := by rwa [pow_succ] at hordz
      exact hdvd ((dvd_pow_self (ℓ : ℤ) (Nat.succ_ne_zero c)).trans
        ((mul_dvd_mul_iff_right hlne).1 h2))
    have hgpow : g ^ (ℓ : ℕ) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [hb]; simpa using pow_dvd_pow ℓ hb1)
    obtain ⟨z, hzH, hz1⟩ : ∃ z ∈ H, z ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hHne (le_bot_iff.1 fun z hz => Subgroup.mem_bot.2 (hcon z hz))
    exact Subgroup.zpowers_le.2 hzH (mem_zpowers_of_pow_prime hℓ hgpow (hH hzH) hz1)

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

/-! ### The restriction with total ramification taken out of it as well -/

/-- **At a prime where the homomorphism ramifies over the base realization, the base realization
splits completely there and the local image is cyclic** — the restriction with both the roots of
unity rider and total ramification dropped.

What is left is what a construction has to arrange by hand: the base realization must split
completely wherever the homomorphism newly ramifies, and the local image there must be generated by
a single value.  Total ramification is not an extra demand on the construction, being a consequence
of cyclicity once the layer below is totally ramified. -/
def IsCyclicSplitHom (φ : Gal(Ω/k) →* U) (Φ : Gal(Ω/k) →* W) : Prop :=
  ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
    (∃ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 ∧ Φ x ≠ 1) →
      (∀ x ∈ stabilizer Gal(Ω/k) P, φ x = 1) ∧
        ∃ x₀ ∈ stabilizer Gal(Ω/k) P,
          ∀ x ∈ stabilizer Gal(Ω/k) P, Φ x ∈ Subgroup.zpowers (Φ x₀)

/-- **A cyclic local image over a totally ramified one is itself totally ramified.**

At a prime where the homomorphism ramifies over the base realization, the base realization kills the
whole decomposition subgroup, so every value there has order a power of the prime, and the local
image is generated by the value at a single element.  The homomorphism below is totally ramified
there, so that element agrees below with one of the inertia subgroup, and the two values differ by
one the prime kills.  That is exactly the situation in which an element of prime power order is
forced into a nontrivial subgroup of its own powers, and the inertia subgroup has nontrivial image
because the homomorphism ramifies there — so the generator lies in the image of inertia, and with it
the whole local image. -/
theorem isCyclicRamifiedHom_of_isCyclicSplitHom (hℓ : ℓ.Prime) {φ : Gal(Ω/k) →* U}
    {Φ : Gal(Ω/k) →* W} {Ψ : Gal(Ω/k) →* W'} {π : W' →* W} (hover : ∀ x, π (Ψ x) = Φ x)
    (hker : ∀ y : W', π y = 1 → y ^ ℓ = 1)
    (hord : ∀ x : Gal(Ω/k), φ x = 1 → ∃ a : ℕ, Ψ x ^ ℓ ^ a = 1)
    (hbelow : ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      (∃ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 ∧ Ψ x ≠ 1) →
        ∀ x ∈ stabilizer Gal(Ω/k) P, ∃ y ∈ Ideal.inertia Gal(Ω/k) P, Φ x = Φ y)
    (h : IsCyclicSplitHom φ Ψ) : IsCyclicRamifiedHom φ Ψ := by
  intro P hPp hPbot hram
  obtain ⟨hsplit, x₀, hx₀, hgen⟩ := h P hPp hPbot hram
  refine ⟨hsplit, fun x hx => ?_, x₀, hx₀, hgen⟩
  set H : Subgroup W' := (Ideal.inertia Gal(Ω/k) P).map Ψ with hHdef
  have hHle : H ≤ Subgroup.zpowers (Ψ x₀) := by
    rintro - ⟨y, hy, rfl⟩
    exact hgen y (Ideal.inertia_le_stabilizer P hy)
  obtain ⟨z, hzI, -, hz1⟩ := hram
  have hHne : H ≠ ⊥ := fun hbot => hz1 (Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_map_of_mem Ψ hzI))
  obtain ⟨y₀, hy₀I, hy₀⟩ :=
    hbelow P hPp hPbot ⟨z, hzI, hsplit z (Ideal.inertia_le_stabilizer P hzI), hz1⟩ x₀ hx₀
  obtain ⟨a, ha⟩ := hord x₀ (hsplit x₀ hx₀)
  have hy : (Ψ x₀ * (Ψ y₀)⁻¹) ^ ℓ = 1 := by
    refine hker _ ?_
    rw [_root_.map_mul, _root_.map_inv, hover, hover, hy₀, mul_inv_cancel]
  have hx₀H : Ψ x₀ ∈ H :=
    mem_of_pow_prime_pow hℓ ha hHle hHne (Subgroup.mem_map_of_mem Ψ hy₀I) hy
  obtain ⟨y, hyI, hyx⟩ := Subgroup.mem_map.1 (Subgroup.zpowers_le.2 hx₀H (hgen x hx))
  exact ⟨y, hyI, hyx.symm⟩

end InverseGalois.Shafarevich
