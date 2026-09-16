/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelFlatRadicand

/-!
# One named prime, one radicand

A prescription at a named prime away from the exponent is a homomorphism of the part of inertia
there which the base realization kills, into an elementary abelian layer.  That part of inertia is
carried by a single element modulo an open subgroup, so every coordinate of such a homomorphism is a
multiple of one and the same character of it, and the homomorphism is the power of a single value of
the layer by that character.

This file reads that off a single radicand.  A unit of the level whose order at the place below the
named prime is prime to the exponent has a Kummer character taking a unit value there, so every
coordinate of the prescribed homomorphism is a multiple of that character; the powers of that one
unit by those multipliers are a family of radicands, and the homomorphism assembled out of them is
the power of a single value of the layer by the Kummer character of the one unit.

Conjugating the argument is then transparent.  An automorphism of the extension over the base raises
the chosen root of unity to some exponent, and it multiplies the Kummer character of a radicand it
fixes by that exponent; so the assembled homomorphism is moved by a map of the layer exactly when
that map raises the single value to that exponent.  That is the equivariance a prescription made at
one prime can carry, and it costs the radicand only being fixed by the decomposition subgroup there.

## Main definitions

* `InverseGalois.Shafarevich.subKummerChar` — the Kummer character of a unit of the level, read on a
  subgroup of the base group contained in the kernel of the base realization.

## Main results

* `InverseGalois.Shafarevich.kummerKernelHom_eq_pow` — **the homomorphism assembled out of the
  powers of a single radicand is the power of a single value of the target by the Kummer character
  of that radicand.**
* `InverseGalois.Shafarevich.kummerKernelHom_conj_of_pow` — **conjugating the argument by an
  automorphism fixing the radicand moves that homomorphism by any map of the target which raises the
  single value to the exponent by which the automorphism raises the roots of unity.**
* `InverseGalois.Shafarevich.exists_forall_eq_pow_subKummerChar` — **a smooth homomorphism of the
  part of inertia the base realization kills is the power of a single value of the target by the
  Kummer character of any radicand whose character there takes a unit value.**
* `InverseGalois.Shafarevich.exists_subKummerChar_eq_one` — a Kummer character taking a unit value
  on a subgroup takes the value one there.

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, radicand, inertia subgroup, character
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### A product of powers killed by the exponent -/

section Prod

variable {ℓ : ℕ} {M : Type*} [CommMonoid M] {T : Type*} [Fintype T]

/-- A product of powers of elements killed by the exponent is killed by the exponent. -/
theorem prod_pow_pow_eq_one {b : T → M} (hb : ∀ t, b t ^ ℓ = 1) (c : T → ℕ) :
    (∏ t, b t ^ c t) ^ ℓ = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun t _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, hb t, one_pow]

end Prod

/-! ### The Kummer character on a subgroup of the kernel -/

section SubChar

variable {ℓ : ℕ} [NeZero ℓ] {k Ω U : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [Group U] {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω} {ζ : ↥K}
  {hζ : IsPrimitiveRoot ζ ℓ}

attribute [local instance] zmodTrivialAction

variable (hKker : K.fixingSubgroup = φ.ker)
  (h : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
  {A : Subgroup Gal(Ω/k)} (hAker : A ≤ φ.ker)

/-- **The Kummer character of a unit of the level, read on a subgroup of the base group contained in
the kernel of the base realization.** -/
noncomputable def subKummerChar (Z : (↥K)ˣ) (x : ↥A) : ZMod ℓ :=
  kummerChar h Z (kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hAker x.2⟩)

/-- The Kummer character read on a subgroup of the kernel is a character of that subgroup. -/
theorem subKummerChar_mul (Z : (↥K)ˣ) (x y : ↥A) :
    subKummerChar hKker h hAker Z (x * y)
      = subKummerChar hKker h hAker Z x + subKummerChar hKker h hAker Z y := by
  simp only [subKummerChar]
  rw [show (⟨((x * y : ↥A) : Gal(Ω/k)), hAker (x * y).2⟩ : ↥φ.ker)
      = ⟨(x : Gal(Ω/k)), hAker x.2⟩ * ⟨(y : Gal(Ω/k)), hAker y.2⟩ from Subtype.ext rfl,
    _root_.map_mul, kummerChar_mul]

/-- The Kummer character read on a subgroup of the kernel multiplies by the exponent at a power. -/
theorem subKummerChar_pow (Z : (↥K)ˣ) (x : ↥A) (m : ℕ) :
    subKummerChar hKker h hAker Z (x ^ m) = m • subKummerChar hKker h hAker Z x :=
  zmodChar_pow (subKummerChar_mul hKker h hAker Z) x m

/-- **A Kummer character taking a unit value on a subgroup of the kernel takes the value one
there**, at the matching power of an element where it is a unit. -/
theorem exists_subKummerChar_eq_one (Z : (↥K)ˣ) {x₁ : ↥A}
    (hx₁ : IsUnit (subKummerChar hKker h hAker Z x₁)) :
    ∃ x₀ : ↥A, subKummerChar hKker h hAker Z x₀ = 1 := by
  obtain ⟨u, hu⟩ := hx₁
  refine ⟨x₁ ^ ((u⁻¹ : (ZMod ℓ)ˣ) : ZMod ℓ).val, ?_⟩
  rw [subKummerChar_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, ← hu, ← Units.val_mul,
    inv_mul_cancel, Units.val_one]

end SubChar

/-! ### The homomorphism carried by the powers of a single radicand -/

section Pow

variable {ℓ : ℕ} [NeZero ℓ] {k Ω U : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [Group U] {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω} {ζ : ↥K}
  {hζ : IsPrimitiveRoot ζ ℓ}

attribute [local instance] zmodTrivialAction

variable (hKker : K.fixingSubgroup = φ.ker)
  (h : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
  {M : Type*} [CommGroup M] {T : Type*} [Fintype T] (b : T → M) (hb : ∀ t, b t ^ ℓ = 1)

/-- **The homomorphism assembled out of the powers of a single radicand is the power of a single
value of the target by the Kummer character of that radicand**, the value being the matching product
of the powers of the coefficients. -/
theorem kummerKernelHom_eq_pow (Z : (↥K)ˣ) (c : T → ZMod ℓ) (y : ↥φ.ker) :
    kummerKernelHom hKker h b hb (fun t => Z ^ (c t).val) y
      = (∏ t, b t ^ (c t).val) ^ (kummerChar h Z (kerGalEquiv hKker y)).val := by
  rw [kummerKernelHom_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [kummerChar_units_pow, ← pow_mul]
  refine pow_eq_pow_of_pow_eq_one (hb t) ?_
  push_cast [ZMod.natCast_zmod_val, nsmul_eq_mul]
  ring

variable [Normal k ↥K]

/-- **Conjugating the argument by an automorphism fixing the radicand up to an exponent-th power
moves the homomorphism assembled out of its powers by any map of the target which raises the single
value to the exponent by which the automorphism raises the roots of unity.**

The Kummer character of a radicand an automorphism over the base fixes up to an exponent-th power is
multiplied by that exponent when the argument is conjugated by it, and the homomorphism is the power
of the single value by that character. -/
theorem kummerKernelHom_conj_of_pow (Z : (↥K)ˣ) (c : T → ZMod ℓ) {g : Gal(Ω/k)} {e : ℕ}
    (hgζ : g • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ e) {s : (↥K)ˣ}
    (hZ : AlgEquiv.restrictNormalHom (↥K) g • Z = Z * s ^ ℓ) (f : M →* M)
    (hV : (∏ t, b t ^ (c t).val) ^ e = f (∏ t, b t ^ (c t).val)) (y : ↥φ.ker)
    (hy : g * (y : Gal(Ω/k)) * g⁻¹ ∈ φ.ker) :
    kummerKernelHom hKker h b hb (fun t => Z ^ (c t).val) ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩
      = f (kummerKernelHom hKker h b hb (fun t => Z ^ (c t).val) y) := by
  have hτ : galSubHom K (kerGalEquiv hKker ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩)
      = g * galSubHom K (kerGalEquiv hKker y) * g⁻¹ := by
    rw [galSubHom_kerGalEquiv, galSubHom_kerGalEquiv]
  rw [kummerKernelHom_eq_pow hKker h b hb Z c, kummerKernelHom_eq_pow hKker h b hb Z c,
    kummerChar_conj_of_smul_eq_mul_pow h hgζ hZ hτ, _root_.map_pow, ← hV, ← pow_mul]
  refine pow_eq_pow_of_pow_eq_one (prod_pow_pow_eq_one hb _) ?_
  push_cast [ZMod.natCast_zmod_val]
  ring

end Pow

/-! ### The coordinates of a prescription at a named prime -/

section Coord

variable {ℓ : ℕ} [NeZero ℓ] {k Ω U : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω] [Group U] {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω} [NumberField ↥K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ ℓ}

attribute [local instance] zmodTrivialAction

variable (hKker : K.fixingSubgroup = φ.ker)
  (h : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)

/-- **A smooth homomorphism of the part of inertia the base realization kills is the power of a
single value of the target by the Kummer character of any radicand whose character there takes a
unit value.**

Every coordinate of the homomorphism is a smooth character of that subgroup, hence a multiple of the
character of the radicand; the multipliers are the coordinates of the single value. -/
theorem exists_forall_eq_pow_subKummerChar {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥)
    (hℓP : (ℓ : 𝓞 Ω) ∉ P) {A : Subgroup Gal(Ω/k)}
    (hA : A = Ideal.inertia Gal(Ω/k) P ⊓ φ.ker) (hAker : A ≤ φ.ker) {M : Type*} [CommGroup M]
    {T : Type*} [Fintype T] {b : T → M} (hb : ∀ t, b t ^ ℓ = 1) {χ : T → M → ZMod ℓ}
    (hχ : ∀ m : M, ∏ t, b t ^ (χ t m).val = m)
    (hχadd : ∀ (t : T) (m m' : M), χ t (m * m') = χ t m + χ t m') (a : ↥A →* M)
    (hasm : IsSmooth₁ ((a : ↥A →* M) : ↥A → M)) (Z : (↥K)ˣ) {x₁ : ↥A}
    (hx₁ : IsUnit (subKummerChar hKker h hAker Z x₁)) :
    ∃ c : T → ZMod ℓ, ∀ x : ↥A,
      a x = (∏ t, b t ^ (c t).val) ^ (subKummerChar hKker h hAker Z x).val := by
  classical
  have key : ∀ t : T, ∃ ct : ZMod ℓ, ∀ x : ↥A,
      χ t (a x) = ct * subKummerChar hKker h hAker Z x := by
    intro t
    have hadd : ∀ x y : ↥A, χ t (a (x * y)) = χ t (a x) + χ t (a y) := fun x y => by
      rw [_root_.map_mul, hχadd]
    exact exists_forall_eq_mul_kummerChar hKker h hP hℓP hA hAker hadd
      (isSmooth₁_of_map_eq_one hasm hadd fun x hx => by rw [hx, zmodChar_one_eq_zero (hχadd t)])
      Z hx₁
  choose c hc using key
  refine ⟨c, fun x => ?_⟩
  conv_lhs => rw [← hχ (a x)]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [hc t x, ← pow_mul]
  refine pow_eq_pow_of_pow_eq_one (hb t) ?_
  push_cast [ZMod.natCast_zmod_val]
  ring

end Coord

end InverseGalois.Shafarevich
