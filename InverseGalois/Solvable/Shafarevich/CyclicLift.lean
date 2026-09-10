/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.CharacterRoot
import InverseGalois.CFT.Units.DecompositionClosed
import InverseGalois.Solvable.Shafarevich.LocalLift

/-!
# The local step from the roots of unity of the base field

The ramified case of the local step was reduced to the lifting of a cyclic character of prime power
order along a surjection raising that order once.  Such a character takes its values in the powers
of a single element, and the powers of an element are, as a group, carried onto the powers of any
other element whose order divides them: the transport sends one generator to the other, and it is
well defined because two integers with the same power of the first element differ by a multiple of
its order, hence by a multiple of the order of the second.

That transport carries the character into the units of the extension, where the roots of unity of
every order are found because the field is algebraically closed.  Extracting a root of a character
with values in the units is what Hilbert's theorem ninety for a closed subgroup does, and the
transport in the other direction carries the root character into the group the lift was wanted in.
The two transports agree at the generators, which is why the lifted character composed with the
surjection is the character one started with.

So the whole of the ramified case rests on one condition: that the roots of unity of the order in
play are fixed by the decomposition subgroup, that is, that the local field at the prime contains
them.  Nothing else about the prime — its ramification, its residue field — enters, and the only
property of its decomposition subgroup that is used is that it is closed, which every decomposition
subgroup is.

That condition is exactly the last clause of the restriction the solutions of the ladder already
carry, so nothing has to be assumed for it.  The two halves then assemble: at a prime where the
solution kills inertia the unramified case applies, and at one where it does not the cyclic
character lifts, so **the step has a local solution at every prime**.

## Main definitions

* `InverseGalois.Shafarevich.zpowersExp` — an exponent witnessing that an element of the powers of
  an element is such a power.
* `InverseGalois.Shafarevich.zpowersLift` — the powers of one element, carried onto the powers of
  another whose order divides them.

## Main results

* `InverseGalois.Shafarevich.hasCyclicLift_of_fixed_rootsOfUnity` — **a cyclic character of a
  closed subgroup lifts as soon as the roots of unity of its order are fixed.**
* `InverseGalois.Shafarevich.hasLocalLift_isSplitTotallyRamified` — **the step of the tower has a
  local solution at every prime**, the restriction the solutions carry supplying the roots of unity
  the lifting calls for.

## Tags

inverse Galois problem, solvable group, embedding problem, Kummer theory, root of unity,
decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT MulAction NumberField

open scoped Pointwise

/-! ### Carrying the powers of one element onto the powers of another -/

section ZPowers

variable {G H : Type*} [Group G] [Group H] {x : G} {y : H}

/-- **Two powers of an element that agree have powers of any element of dividing order that
agree.** -/
theorem zpow_eq_zpow_of_orderOf_dvd (h : orderOf y ∣ orderOf x) {i j : ℤ}
    (hij : x ^ i = x ^ j) : y ^ i = y ^ j := by
  rw [zpow_eq_zpow_iff_modEq] at hij ⊢
  exact hij.of_dvd (Int.natCast_dvd_natCast.mpr h)

/-- A power of an element killed by a number is killed by that number. -/
theorem zpow_pow_eq_one {n : ℕ} (hy : y ^ n = 1) (i : ℤ) : (y ^ i) ^ n = 1 := by
  rw [← zpow_natCast (y ^ i) n, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

/-- An exponent witnessing that an element of the powers of an element is such a power. -/
noncomputable def zpowersExp (u : Subgroup.zpowers x) : ℤ :=
  (Subgroup.mem_zpowers_iff.1 u.2).choose

/-- The exponent witnessing membership of the powers of an element does witness it. -/
theorem zpow_zpowersExp (u : Subgroup.zpowers x) : x ^ zpowersExp u = (u : G) :=
  (Subgroup.mem_zpowers_iff.1 u.2).choose_spec

/-- **The powers of one element, carried onto the powers of another whose order divides them.**

An element of the powers of the first is a power of it by some exponent, and the value is the power
of the second element by that exponent; this does not depend on the exponent chosen, because two
exponents with the same power of the first element differ by a multiple of its order, hence by a
multiple of the order of the second. -/
noncomputable def zpowersLift (h : orderOf y ∣ orderOf x) : Subgroup.zpowers x →* H :=
  MonoidHom.mk' (fun u => y ^ zpowersExp u) (by
    intro u v
    have hx : x ^ zpowersExp (u * v) = x ^ (zpowersExp u + zpowersExp v) := by
      rw [zpow_add, zpow_zpowersExp, zpow_zpowersExp, zpow_zpowersExp]
      rfl
    show y ^ zpowersExp (u * v) = y ^ zpowersExp u * y ^ zpowersExp v
    rw [zpow_eq_zpow_of_orderOf_dvd h hx, zpow_add])

/-- The transport of the powers of one element onto the powers of another matches the exponents. -/
theorem zpowersLift_apply (h : orderOf y ∣ orderOf x) {u : Subgroup.zpowers x} {i : ℤ}
    (hi : (u : G) = x ^ i) : zpowersLift h u = y ^ i :=
  zpow_eq_zpow_of_orderOf_dvd h ((zpow_zpowersExp u).trans hi)

end ZPowers

/-! ### The cyclic lift from the roots of unity -/

section CyclicLift

variable (ℓ : ℕ) [Fact ℓ.Prime] {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω]

omit [Fact ℓ.Prime] in
/-- **A cyclic character of a closed subgroup lifts along a surjection raising its order once, as
soon as the roots of unity of that order are fixed by the whole group.**

The character has its values in the powers of one element of the target, which are carried onto the
roots of unity of the order of that element inside the units of the extension, the field being
algebraically closed and so carrying a primitive root of unity of every order.  The character read
in the units has a root of the complementary order, by Hilbert's theorem ninety for a closed
subgroup, and that root has its values in the roots of unity of the full order, which are carried
back onto the powers of the element the lift was wanted at.  The two transports agree at the
generators, so the lift composed with the surjection is the character one started with. -/
theorem hasCyclicLift_of_fixed_rootsOfUnity {A : Subgroup Gal(Ω/k)}
    (hA : IsClosed (A : Set Gal(Ω/k))) (N : ℕ)
    (hμ : ∀ ζ : Ωˣ, ζ ^ N = 1 → ∀ σ : ↥A, σ • ζ = ζ) :
    HasCyclicLift ℓ N A := by
  intro Z Z' _ _ _ f z' _ _ hNdvd ν hνs hνmem
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  set m := orderOf z' with hmdef
  have hm0 : 0 < m := orderOf_pos z'
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hm0.ne'⟩
  set q := orderOf (f z') with hqdef
  obtain ⟨d, hd⟩ : q ∣ m := orderOf_map_dvd f z'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hd
      exact absurd hd hm0.ne'
    · exact h
  -- a primitive root of unity of the order of the element to be lifted
  obtain ⟨ξ₀, hξ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  set ξ : Ωˣ := (hξ₀.isUnit hm0.ne').unit with hξdef
  have hξcoe : ((ξ : Ωˣ) : Ω) = ξ₀ := IsUnit.unit_spec _
  have hξ : IsPrimitiveRoot ξ m := hξ₀.isUnit_unit hm0.ne'
  set ζ : Ωˣ := ξ ^ d with hζdef
  have hζord : orderOf ζ = q := by
    rw [hζdef, orderOf_pow' _ hd0.ne', ← hξ.eq_orderOf, hd]
    rw [Nat.gcd_eq_right ⟨q, mul_comm q d⟩, Nat.mul_div_cancel _ hd0]
  have hζq : ζ ^ q = 1 := by
    rw [← hζord]
    exact pow_orderOf_eq_one ζ
  -- the character read in the units of the extension
  have hqζ : orderOf ζ ∣ orderOf (f z') := by rw [hζord, hqdef]
  set χ₀ : Subgroup.zpowers (f z') →* Ωˣ := zpowersLift hqζ with hχ₀def
  set ν₁ : ↥A →* Subgroup.zpowers (f z') := ν.codRestrict _ hνmem with hν₁def
  set χ : ↥A →* Ωˣ := χ₀.comp ν₁ with hχdef
  have hχval : ∀ (σ : ↥A) (i : ℤ), (f z') ^ i = ν σ → χ σ = ζ ^ i := fun σ i hi =>
    zpowersLift_apply hqζ (u := ν₁ σ) hi.symm
  have hχs : IsSmooth₁ (χ : ↥A → Ωˣ) := by
    obtain ⟨M, hM, hu⟩ := hνs
    refine ⟨M, hM, fun a n hn => ?_⟩
    show χ₀ (ν₁ (a * n)) = χ₀ (ν₁ a)
    exact congrArg χ₀ (Subtype.ext (hu a n hn))
  have hχn : ∀ σ : ↥A, χ σ ^ q = 1 := by
    intro σ
    obtain ⟨i, hi⟩ := hνmem σ
    rw [hχval σ i hi]
    exact zpow_pow_eq_one hζq i
  have hμ' : ∀ w : Ωˣ, w ^ (q * d) = 1 → ∀ σ : ↥A, σ • w = w := by
    intro w hw σ
    obtain ⟨t, ht⟩ := hNdvd
    refine hμ w ?_ σ
    rw [ht, pow_mul, hd, hw, one_pow]
  obtain ⟨χ', hχ's, hχ'd, hχ'm⟩ := exists_smoothHom_pow_eq hA hd0 χ hχs hχn hμ'
  -- the values of the root character are powers of the primitive root of unity
  have hmem' : ∀ σ : ↥A, χ' σ ∈ Subgroup.zpowers ξ := by
    intro σ
    have h1 : ((χ' σ : Ωˣ) : Ω) ^ m = 1 := by
      have h2 : (χ' σ) ^ m = 1 := by
        rw [hd]
        exact hχ'm σ
      have h3 := congrArg (fun w : Ωˣ => (w : Ω)) h2
      simpa using h3
    obtain ⟨i, -, hival⟩ := hξ₀.eq_pow_of_pow_eq_one h1
    refine ⟨(i : ℤ), ?_⟩
    show ξ ^ (i : ℤ) = χ' σ
    rw [zpow_natCast]
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hξcoe, hival]
  have hz'ξ : orderOf z' ∣ orderOf ξ := by rw [← hξ.eq_orderOf, hmdef]
  set ν'₀ : Subgroup.zpowers ξ →* Z' := zpowersLift hz'ξ with hν'₀def
  set ν' : ↥A →* Z' := ν'₀.comp (χ'.codRestrict _ hmem') with hν'def
  refine ⟨ν', ?_, ?_, ?_⟩
  · obtain ⟨M, hM, hu⟩ := hχ's
    refine ⟨M, hM, fun a n hn => ?_⟩
    show ν'₀ _ = ν'₀ _
    exact congrArg ν'₀ (Subtype.ext (hu a n hn))
  · intro σ
    obtain ⟨i, hi⟩ := hmem' σ
    obtain ⟨j, hj⟩ := hνmem σ
    have hν'i : ν' σ = z' ^ i := zpowersLift_apply hz'ξ (u := χ'.codRestrict _ hmem' σ) hi.symm
    have hζi : χ σ = ζ ^ i := by
      rw [← hχ'd σ, ← hi, hζdef, ← zpow_natCast ξ d, ← zpow_natCast (ξ ^ i) d, ← zpow_mul,
        ← zpow_mul, mul_comm]
    have hζj : χ σ = ζ ^ j := hχval σ j hj
    have hfin : (f z') ^ i = (f z') ^ j :=
      zpow_eq_zpow_of_orderOf_dvd (by rw [hζord, hqdef]) (hζi.symm.trans hζj)
    rw [hν'i, map_zpow, hfin]
    exact hj
  · intro σ
    obtain ⟨i, hi⟩ := hmem' σ
    exact ⟨i, (zpowersLift_apply hz'ξ (u := χ'.codRestrict _ hmem' σ) hi.symm).symm⟩

end CyclicLift

/-! ### The local step -/

section LocalStep

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S]
  [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω]

/-- **The step of the tower has a local solution at every prime.**

At a prime where the solution kills inertia the local solution comes from the Frobenius alone.  At
a prime where it does not, the solution splits completely and is totally ramified there, so its
restriction to the decomposition subgroup is cyclic and the local field carries the roots of unity
that restriction calls for; the decomposition subgroup being closed, the cyclic character lifts.
Nothing beyond the restriction the solutions already carry is asked, so the condition is met
outright. -/
theorem hasLocalLift_isSplitTotallyRamified (hS : IsPGroup ℓ S) (φ : Gal(Ω/k) →* U) {t : ℕ}
    (D : Fin t → Subgroup Gal(Ω/k)) (T : Set (Subgroup Gal(Ω/k)))
    (hT : ∀ A ∈ T, ∃ P : Ideal (𝓞 Ω), P.IsPrime ∧ P ≠ ⊥ ∧ A = stabilizer Gal(Ω/k) P)
    (hD : ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      stabilizer Gal(Ω/k) P ∉ conjFamily D → ∀ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1) :
    HasLocalLift ℓ U n S j φ D T (IsSplitTotallyRamified ℓ U S φ) :=
  hasLocalLift_of_hasSplitRamifiedLift ℓ U n S j φ D T hT hD
    (hasSplitRamifiedLift_of_hasCyclicLift ℓ U n S j hS φ fun P N _ _ _ hμ =>
      hasCyclicLift_of_fixed_rootsOfUnity ℓ (isClosed_stabilizer_ideal P) N
        fun ζ hζ σ => hμ ζ hζ (σ : Gal(Ω/k)) σ.2)

end LocalStep

end InverseGalois.Shafarevich
