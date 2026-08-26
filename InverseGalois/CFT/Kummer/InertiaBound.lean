/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CongruentRadical
import InverseGalois.CFT.Kummer.RadicalCharacter
import InverseGalois.CFT.Units.PlaceComap

/-!
# The inertia group of an abelian extension of exponent `ℓ` at a place over `ℓ`

Let `k` be a number field with a place over a prime `ℓ` of ramification index and residue degree
one, let `K` be obtained from `k` by adjoining the `ℓ`-th roots of unity, and let `M / K` be an
abelian extension of exponent `ℓ` which is abelian even over `k`.  The inertia group of `M / K` at
a place over `ℓ` then has order at most `ℓ`.

The proof is Kummer theory.  Every character of the Galois group with values in `ZMod ℓ` has a
radical, whose radicand is an eigenvector for the action of the roots of unity because the whole
extension is abelian over `k`.  Two eigen radicands are dependent modulo the radicands congruent to
one modulo the `ℓ`-th power of the different, and a radicand congruent to one has an unramified
radical: so the two characters attached to two elements of the inertia group cannot separate them,
and the inertia group is cyclic of order at most `ℓ`.

## Main results

* `InverseGalois.CFT.eq_of_isCongrPow`: **an element of the inertia group fixes the radical of a
  radicand congruent to one.**
* `InverseGalois.CFT.exists_hom_pair`: two elements of an abelian group killed by a prime, the
  second not a power of the first, are separated by a pair of characters.
* `InverseGalois.CFT.card_inertia_le`: **the inertia group at a place over the exponent of an
  abelian extension of exponent `ℓ` has order at most `ℓ`.**

## Tags

number field, Kummer theory, inertia, ramification, root of unity, character
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Radicands congruent to one do not ramify -/

section Congr

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
variable {ℓ : ℕ}

set_option synthInstance.maxHeartbeats 400000

/-- **An element of the inertia group at a place over the exponent fixes the radical of a radicand
congruent to one.**  Dividing out the `ℓ`-th power hidden in the radicand leaves a unit congruent
to one modulo the `ℓ`-th power of `ζ - 1`, and the valuation of the base is the valuation of the
extension raised to the ramification index, so the congruence survives the extension. -/
theorem eq_of_isCongrPow (hℓ : ℓ.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    (W : HeightOneSpectrum (𝓞 M)) {w : K}
    (hw : IsCongrPow ℓ ((primeUnder (𝓞 K) W).valuation K) (ζ - 1) w)
    {α : M} (hα : α ^ ℓ = algebraMap K M w)
    {σ : Gal(M/K)} (hσ : σ ∈ Ideal.inertia Gal(M/K) W.asIdeal) :
    σ α = α := by
  obtain ⟨c, γ, hγ0, hcv, hc1, hwe⟩ := hw
  have htrans : ∀ x : K,
      W.valuation M (algebraMap K M x) = ((primeUnder (𝓞 K) W).valuation K x) ^ ramIdx (𝓞 K) W :=
    fun x => valuation_algebraMap (A := 𝓞 K) W x
  have hγM : algebraMap K M γ ≠ 0 := (map_ne_zero (algebraMap K M)).mpr hγ0
  have hβ : (α / algebraMap K M γ) ^ ℓ = algebraMap K M c := by
    rw [div_pow, hα, hwe, map_mul, map_pow, mul_div_assoc,
      div_self (pow_ne_zero _ hγM), mul_one]
  have hunit : W.valuation M (algebraMap K M c) = 1 := by rw [htrans, hcv, one_pow]
  have hcongr : W.valuation M (algebraMap K M c - 1)
      ≤ W.valuation M (algebraMap K M (ζ - 1)) ^ ℓ := by
    rw [show (algebraMap K M c - 1 : M) = algebraMap K M (c - 1) by rw [map_sub, map_one],
      htrans, htrans, ← pow_mul, mul_comm (ramIdx (𝓞 K) W) ℓ, pow_mul]
    exact pow_le_pow_left₀ zero_le' hc1 _
  have hfix := eq_of_mem_inertia_of_radical_congr hℓ hζ hσ hβ hunit hcongr
  have hsplit : α = α / algebraMap K M γ * algebraMap K M γ := by field_simp
  rw [hsplit, map_mul, hfix, AlgEquiv.commutes]

end Congr

/-! ### Separating characters -/

section Characters

variable {Γ : Type*} [Group Γ] {ℓ : ℕ}

/-- In an abelian group killed by a prime, a subgroup all of whose elements are powers of a single
one of them has order at most that prime. -/
theorem card_le_of_forall_mem_zpowers (hℓ : ℓ.Prime) (hexp : ∀ x : Γ, x ^ ℓ = 1)
    {S : Subgroup Γ} (h : ∀ s ∈ S, s ≠ 1 → ∀ t ∈ S, t ∈ Subgroup.zpowers s) :
    Nat.card ↥S ≤ ℓ := by
  by_cases hS : ∀ s ∈ S, s = 1
  · have hbot : S = ⊥ := by
      refine le_antisymm (fun x hx => ?_) bot_le
      simpa using hS x hx
    rw [hbot]
    simpa using hℓ.one_lt.le
  push_neg at hS
  obtain ⟨s, hsS, hs1⟩ := hS
  have hle : S ≤ Subgroup.zpowers s := fun t ht => h s hsS hs1 t ht
  have horder : orderOf s = ℓ := by
    have hdvd : orderOf s ∣ ℓ := orderOf_dvd_of_pow_eq_one (hexp s)
    rcases (Nat.Prime.eq_one_or_self_of_dvd hℓ _ hdvd) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hs1
    · exact h1
  have hcard : Nat.card ↥(Subgroup.zpowers s) = ℓ := by rw [Nat.card_zpowers, horder]
  have hdvd : Nat.card ↥S ∣ Nat.card ↥(Subgroup.zpowers s) :=
    Subgroup.card_dvd_of_le hle
  rw [hcard] at hdvd
  exact Nat.le_of_dvd hℓ.pos hdvd

end Characters

section Vector

variable {V : Type*} {ℓ : ℕ} [AddCommGroup V] [Fact ℓ.Prime] [Module (ZMod ℓ) V]

/-- Two vectors, the second outside the line spanned by the first, are separated by a pair of
linear functionals: the first does not vanish on the first vector, and the second vanishes on the
first vector but not on the second. -/
theorem exists_linearMap_pair {s t : V} (hs : s ≠ 0)
    (hst : t ∉ Submodule.span (ZMod ℓ) {s}) :
    ∃ f₁ f₂ : V → ZMod ℓ, (∀ x y : V, f₁ (x + y) = f₁ x + f₁ y) ∧
      (∀ x y : V, f₂ (x + y) = f₂ x + f₂ y) ∧ f₁ s ≠ 0 ∧ f₂ s = 0 ∧ f₂ t ≠ 0 := by
  have hbot : s ∉ (⊥ : Submodule (ZMod ℓ) V) := by
    simpa using hs
  obtain ⟨f₁, hf₁, -⟩ := Submodule.exists_le_ker_of_notMem hbot
  obtain ⟨f₂, hf₂, hker⟩ := Submodule.exists_le_ker_of_notMem hst
  exact ⟨f₁, f₂, map_add f₁, map_add f₂, hf₁,
    hker (Submodule.mem_span_singleton_self _), hf₂⟩

end Vector

section Separate

variable {Γ : Type*} [Group Γ] {ℓ : ℕ}

/-- **Two elements of an abelian group killed by a prime, the second not a power of the first, are
separated by a pair of characters** with values in the field with `ℓ` elements: the first character
does not vanish on the first element, and the second vanishes on the first element but not on the
second. -/
theorem exists_hom_pair (hℓ : ℓ.Prime) (hcomm : ∀ x y : Γ, x * y = y * x)
    (hexp : ∀ x : Γ, x ^ ℓ = 1) {s t : Γ} (hs : s ≠ 1)
    (hst : t ∉ Subgroup.zpowers s) :
    ∃ χ₁ χ₂ : Γ → ZMod ℓ, (∀ x y : Γ, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
      (∀ x y : Γ, χ₂ (x * y) = χ₂ x + χ₂ y) ∧ χ₁ s ≠ 0 ∧ χ₂ s = 0 ∧ χ₂ t ≠ 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  letI : CommGroup Γ := { ‹Group Γ› with mul_comm := hcomm }
  letI : Module (ZMod ℓ) (Additive Γ) := AddCommGroup.zmodModule (n := ℓ) (by
    intro x
    have hx : (Additive.toMul x) ^ ℓ = 1 := hexp _
    simpa using congrArg Additive.ofMul hx)
  obtain ⟨f₁, f₂, hadd₁, hadd₂, hf₁, hf₂s, hf₂t⟩ :=
    exists_linearMap_pair (V := Additive Γ) (ℓ := ℓ) (s := Additive.ofMul s)
      (t := Additive.ofMul t)
      (by
        intro h
        exact hs (by simpa using congrArg Additive.toMul h))
      (by
        -- the second element is outside the line spanned by the first
        intro hmem
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
        refine hst ⟨(a.val : ℤ), ?_⟩
        rw [show a • Additive.ofMul s = a.val • Additive.ofMul s by
          conv_lhs => rw [← ZMod.natCast_rightInverse a]
          exact Nat.cast_smul_eq_nsmul _ _ _] at ha
        simpa [zpow_natCast, -ZMod.natCast_val] using congrArg Additive.toMul ha)
  exact ⟨fun x => f₁ (Additive.ofMul x), fun x => f₂ (Additive.ofMul x),
    fun x y => hadd₁ (Additive.ofMul x) (Additive.ofMul y),
    fun x y => hadd₂ (Additive.ofMul x) (Additive.ofMul y), hf₁, hf₂s, hf₂t⟩

end Separate

/-! ### The bound on the inertia group -/

section Main

variable {k K M : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Field M]
  [NumberField M] [Algebra k K] [Algebra K M] [Algebra k M] [IsScalarTower k K M]
  [IsGalois k M] [Normal k K]
variable {ℓ g : ℕ} {ζ : K}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

/-- **The inertia group at a place over the exponent of an abelian extension of exponent `ℓ` has
order at most `ℓ`.**  Two elements of the inertia group which are independent would be separated by
two characters, whose radicands are eigenvectors for the action on the roots of unity; but two
eigen radicands are dependent modulo the radicands congruent to one, and a radicand congruent to
one has an unramified radical. -/
theorem card_inertia_le (habel : ∀ x y : Gal(M/k), x * y = y * x)
    (hexp : ∀ σ : Gal(M/K), σ ^ ℓ = 1) (hζ : IsPrimitiveRoot ζ ℓ) (δ : K ≃ₐ[k] K)
    (hδζ : δ ζ = ζ ^ g) (W : HeightOneSpectrum (𝓞 M))
    (hcyc : IsCyclotomicPlace ℓ g ((primeUnder (𝓞 K) W).valuation K) (ζ - 1)
      (δ.toRingEquiv : K →+* K) (RingHom.id K)) :
    Nat.card ↥(Ideal.inertia Gal(M/K) W.asIdeal) ≤ ℓ := by
  have hℓ : ℓ.Prime := hcyc.prime
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : FiniteDimensional K M := FiniteDimensional.right k K M
  haveI : IsGalois K M := IsGalois.tower_top_of_isGalois k K M
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hℓ.ne_zero
  set ξ : M := algebraMap K M ζ with hξdef
  have hξ : IsPrimitiveRoot ξ ℓ := hζ.map_of_injective (algebraMap K M).injective
  have hξ0 : ξ ≠ 0 := (map_ne_zero (algebraMap K M)).mpr hζ0
  have hfin : IsOfFinOrder ξ := isOfFinOrder_iff_pow_eq_one.mpr ⟨ℓ, hℓ.pos, hξ.pow_eq_one⟩
  set ξu : Mˣ := Units.mk0 ξ hξ0 with hξudef
  have hξu : ξu ^ ℓ = 1 := Units.ext (by simpa [hξudef] using hξ.pow_eq_one)
  -- every character has a radical whose radicand is an eigenvector
  have key : ∀ χ : Gal(M/K) → ZMod ℓ, (∀ x y : Gal(M/K), χ (x * y) = χ x + χ y) →
      ∃ (α : M) (w : K), α ≠ 0 ∧ w ≠ 0 ∧ algebraMap K M w = α ^ ℓ ∧
        (∀ σ : Gal(M/K), σ α = ξ ^ (χ σ).val * α) ∧
        IsEigenRadicand ℓ g (δ.toRingEquiv : K →+* K) (RingHom.id K) w := by
    intro χ hχ
    set f : Gal(M/K) →* Mˣ := rootHom ξu hξu χ hχ with hfdef
    have hfval : ∀ σ : Gal(M/K), (f σ : M) = ξ ^ (χ σ).val := fun σ => by
      simp [hfdef, rootHom_apply, hξudef]
    have hfix : ∀ σ τ : Gal(M/K), σ (f τ : M) = (f τ : M) := by
      intro σ τ
      rw [hfval, hξdef, ← map_pow, AlgEquiv.commutes]
    have hpow : ∀ σ : Gal(M/K), (f σ : M) ^ ℓ = 1 := by
      intro σ
      rw [hfval, ← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
    obtain ⟨α, hα0, hα, w, hw⟩ := exists_radical f hfix hpow
    have hroot : ∀ σ : Gal(M/K), σ α = ξ ^ (χ σ).val * α := by
      intro σ
      rw [hα, hfval]
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, map_zero] at hw
      exact (pow_ne_zero ℓ hα0) hw.symm
    obtain ⟨y, hy0, hy⟩ :=
      exists_pow_mul_pow_eq (k := k) habel δ hζ0 hδζ hα0 (fun σ => ⟨(χ σ).val, hroot σ⟩) hw
    exact ⟨α, w, hα0, hw0, hw, hroot, ⟨y, hy0, hy⟩, ⟨1, one_ne_zero, by simp⟩⟩
  -- an element of the inertia group acting trivially on a radical kills the character
  refine card_le_of_forall_mem_zpowers hℓ hexp ?_
  intro σ₁ hσ₁ hσ₁1 σ₂ hσ₂
  by_contra hnot
  have hcommK : ∀ x y : Gal(M/K), x * y = y * x := by
    intro x y
    have h := habel (x.restrictScalars k) (y.restrictScalars k)
    ext a
    exact congrArg (fun e : Gal(M/k) => e a) h
  obtain ⟨χ₁, χ₂, hχ₁, hχ₂, h₁s, h₂s, h₂t⟩ := exists_hom_pair hℓ hcommK hexp hσ₁1 hnot
  obtain ⟨α₁, w₁, hα₁0, hw₁0, hw₁, hroot₁, he₁⟩ := key χ₁ hχ₁
  obtain ⟨α₂, w₂, hα₂0, hw₂0, hw₂, hroot₂, he₂⟩ := key χ₂ hχ₂
  -- a fixed radical forces the character to vanish
  have hkill : ∀ (χ : Gal(M/K) → ZMod ℓ) (α : M), α ≠ 0 → (∀ σ : Gal(M/K),
      σ α = ξ ^ (χ σ).val * α) → ∀ σ : Gal(M/K), σ α = α → χ σ = 0 := by
    intro χ α hα0 hroot σ hfix
    have h1 : ξ ^ (χ σ).val = 1 := by
      have := hroot σ
      rw [hfix] at this
      field_simp at this
      exact this.symm
    have hdvd : ℓ ∣ (χ σ).val := (hξ.pow_eq_one_iff_dvd _).mp h1
    have hv0 : (χ σ).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    have h0 : (((χ σ).val : ℕ) : ZMod ℓ) = 0 := by rw [hv0, Nat.cast_zero]
    rwa [ZMod.natCast_rightInverse (χ σ)] at h0
  rcases hcyc.isCongrPow_or_exists_div hw₁0 hw₂0 he₁ he₂ with hc | ⟨j, hc⟩
  · exact h₁s (hkill χ₁ α₁ hα₁0 hroot₁ σ₁
      (eq_of_isCongrPow hℓ hζ W hc hw₁.symm hσ₁))
  · -- the quotient of the two radicals is a radical of the quotient of the radicands
    have hβ : (α₂ / α₁ ^ j) ^ ℓ = algebraMap K M (w₂ / w₁ ^ j) := by
      rw [map_div₀, map_pow, hw₁, hw₂, div_pow, ← pow_mul, ← pow_mul, mul_comm ℓ j]
    have hrel : ∀ σ : Gal(M/K), σ ∈ Ideal.inertia Gal(M/K) W.asIdeal →
        χ₂ σ = (j : ZMod ℓ) * χ₁ σ := by
      intro σ hσ
      have hfix := eq_of_isCongrPow hℓ hζ W hc hβ hσ
      have hσ2 : σ (α₂ / α₁ ^ j) = ξ ^ (χ₂ σ).val * α₂ / (ξ ^ ((χ₁ σ).val * j) * α₁ ^ j) := by
        rw [map_div₀, map_pow, hroot₁, hroot₂, mul_pow, ← pow_mul]
      rw [hσ2] at hfix
      have hα₁j : α₁ ^ j ≠ 0 := pow_ne_zero _ hα₁0
      have hB0 : ξ ^ ((χ₁ σ).val * j) ≠ 0 := pow_ne_zero _ hξ0
      have heq : ξ ^ (χ₂ σ).val = ξ ^ ((χ₁ σ).val * j) := by
        have h := (div_eq_div_iff (mul_ne_zero hB0 hα₁j) hα₁j).mp hfix
        refine mul_right_cancel₀ (b := α₂ * α₁ ^ j) (mul_ne_zero hα₂0 hα₁j) ?_
        linear_combination h
      have hmod : (χ₂ σ).val ≡ (χ₁ σ).val * j [MOD ℓ] := by
        have h := hfin.pow_eq_pow_iff_modEq.mp heq
        rwa [← hξ.eq_orderOf] at h
      have hcast : ∀ a : ZMod ℓ, ((a.val : ℕ) : ZMod ℓ) = a := fun a =>
        ZMod.natCast_rightInverse a
      have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      rw [Nat.cast_mul, hcast, hcast] at h3
      rw [h3]
      ring
    have hj : (j : ZMod ℓ) = 0 := by
      have h := hrel σ₁ hσ₁
      rw [h₂s] at h
      exact (mul_eq_zero.mp h.symm).resolve_right h₁s
    have h := hrel σ₂ hσ₂
    rw [hj, zero_mul] at h
    exact h₂t h

end Main

end InverseGalois.CFT
