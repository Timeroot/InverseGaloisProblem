/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.RadicandLevel

/-!
# Radicals attached to characters of an abelian extension

Let `M / K` be a Galois extension whose group is killed by a prime `ℓ`, and suppose the base `K`
contains a primitive `ℓ`-th root of unity `ζ`.  Every character of the Galois group with values in
`ZMod ℓ` becomes, after composing with `n ↦ ζ ^ n`, a one-cocycle with values in the units of `M`,
so Hilbert's theorem 90 produces a radical: an element `α` of `M` which every automorphism
multiplies by the corresponding root of unity.  Its `ℓ`-th power is fixed by the whole group and so
comes from the base.

If moreover `M` is abelian over a smaller field `k` over which `K` is normal, the radicand
transforms under an automorphism `δ` of `K / k` by the exponent through which `δ` acts on the roots
of unity, up to an `ℓ`-th power: it is an eigenvector of `δ` in the group of radicands modulo
`ℓ`-th powers.  This is the input to the local analysis of the level of a radicand.

## Main results

* `InverseGalois.CFT.rootHom`: the homomorphism `x ↦ u ^ χ x` attached to a `ZMod ℓ`-valued
  character and a root of unity of order dividing `ℓ`.
* `InverseGalois.CFT.exists_radical`: **Hilbert's theorem 90 produces a radical for a character
  with values in the roots of unity of the base**, together with a radicand in the base.
* `InverseGalois.CFT.exists_pow_mul_pow_eq`: **the radicand of a character of an abelian extension
  is an eigenvector** for the automorphisms of the base.

## Tags

Kummer theory, Hilbert 90, character, radical, root of unity, eigenvector
-/

namespace InverseGalois.CFT

/-! ### Powers indexed by `ZMod ℓ` -/

section RootHom

variable {G H : Type*} [Group G] [CommGroup H] {ℓ : ℕ}

/-- The homomorphism `x ↦ u ^ χ x` attached to a character with values in `ZMod ℓ` and an element
of order dividing `ℓ`.  The exponent is the natural-number representative of the value of the
character, which is well defined because `u` is killed by `ℓ`. -/
noncomputable def rootHom [NeZero ℓ] (u : H) (hu : u ^ ℓ = 1) (χ : G → ZMod ℓ)
    (hχ : ∀ x y : G, χ (x * y) = χ x + χ y) : G →* H where
  toFun x := u ^ (χ x).val
  map_one' := by
    have h := hχ 1 1
    rw [one_mul] at h
    have h0 : χ 1 = 0 := by linear_combination -h
    rw [h0, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    rw [hχ, ← pow_add]
    refine pow_eq_pow_iff_modEq.mpr (Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hu) ?_)
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _

@[simp]
theorem rootHom_apply [NeZero ℓ] (u : H) (hu : u ^ ℓ = 1) (χ : G → ZMod ℓ)
    (hχ : ∀ x y : G, χ (x * y) = χ x + χ y) (x : G) :
    rootHom u hu χ hχ x = u ^ (χ x).val := rfl

end RootHom

/-! ### Radicals from Hilbert's theorem 90 -/

section Radical

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
variable {ℓ : ℕ}

omit [IsGalois K M] in
/-- **Hilbert's theorem 90 produces a radical for a character with values in the roots of unity of
the base.**  A homomorphism into the units of `M` whose values are fixed by the Galois group is a
one-cocycle, hence a coboundary. -/
theorem exists_eq_mul_of_forall_fixed (f : Gal(M/K) →* Mˣ)
    (hfix : ∀ σ τ : Gal(M/K), σ (f τ : M) = (f τ : M)) :
    ∃ α : M, α ≠ 0 ∧ ∀ σ : Gal(M/K), σ α = (f σ : M) * α := by
  have hcoc : groupCohomology.IsMulCocycle₁ (fun σ : Gal(M/K) => f σ) := by
    intro σ τ
    have hστ : σ • f τ = f τ := by
      ext
      exact hfix σ τ
    show f (σ * τ) = σ • f τ * f σ
    rw [hστ, map_mul, mul_comm]
  obtain ⟨x, hx⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units (fun σ : Gal(M/K) => f σ)
      hcoc
  refine ⟨(x : M), x.ne_zero, fun σ => ?_⟩
  have h := congrArg (fun u : Mˣ => (u : M)) (hx σ)
  simp only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_coe] at h
  field_simp at h
  linear_combination h

/-- **A character of the Galois group with values in the roots of unity of the base has a
radical**: an element multiplied by the value of the character, whose `ℓ`-th power lies in the
base. -/
theorem exists_radical (f : Gal(M/K) →* Mˣ) (hfix : ∀ σ τ : Gal(M/K), σ (f τ : M) = (f τ : M))
    (hpow : ∀ σ : Gal(M/K), (f σ : M) ^ ℓ = 1) :
    ∃ α : M, α ≠ 0 ∧ (∀ σ : Gal(M/K), σ α = (f σ : M) * α) ∧
      ∃ w : K, algebraMap K M w = α ^ ℓ := by
  obtain ⟨α, hα0, hα⟩ := exists_eq_mul_of_forall_fixed f hfix
  refine ⟨α, hα0, hα, ?_⟩
  have hfixed : ∀ σ : Gal(M/K), σ (α ^ ℓ) = α ^ ℓ := by
    intro σ
    rw [map_pow, hα, mul_pow, hpow, one_mul]
  exact (IsGalois.mem_range_algebraMap_iff_fixed (α ^ ℓ)).mpr hfixed

end Radical

/-! ### The radicand is an eigenvector -/

section Eigen

variable {k K M : Type*} [Field k] [Field K] [Field M]
  [Algebra k K] [Algebra K M] [Algebra k M] [IsScalarTower k K M]
  [FiniteDimensional k M] [IsGalois k M] [Normal k K]
variable {ℓ g : ℕ} {ζ : K}

/-- **The radicand of a character of an abelian extension is an eigenvector.**  An automorphism of
the base lifts to the whole extension, where it commutes with the Galois group of the extension
over the base; so it moves the radical by an element of the base times the power of the radical
through which it acts on the roots of unity. -/
theorem exists_pow_mul_pow_eq (habel : ∀ x y : Gal(M/k), x * y = y * x)
    (δ : K ≃ₐ[k] K) (hζ0 : ζ ≠ 0) (hδζ : δ ζ = ζ ^ g) {α : M} (hα0 : α ≠ 0)
    (hroot : ∀ σ : Gal(M/K), ∃ n : ℕ, σ α = (algebraMap K M ζ) ^ n * α)
    {w : K} (hw : algebraMap K M w = α ^ ℓ) :
    ∃ y : K, y ≠ 0 ∧ δ w = w ^ g * y ^ ℓ := by
  haveI : FiniteDimensional K M := FiniteDimensional.right k K M
  haveI : IsGalois K M := IsGalois.tower_top_of_isGalois k K M
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := M) δ
  have hτcom : ∀ x : K, τ (algebraMap K M x) = algebraMap K M (δ x) := by
    intro x
    rw [← hτ]
    exact (AlgEquiv.restrictNormal_commutes τ K x).symm
  have hβ0 : τ α ≠ 0 := fun h => hα0 (by simpa using congrArg τ.symm h)
  have hαg0 : α ^ g ≠ 0 := pow_ne_zero _ hα0
  have hξ0 : (algebraMap K M ζ) ≠ 0 := (map_ne_zero (algebraMap K M)).mpr hζ0
  -- the quotient of the conjugate radical by the `g`-th power of the radical is fixed
  have hfix : ∀ σ : Gal(M/K), σ (τ α / α ^ g) = τ α / α ^ g := by
    intro σ
    obtain ⟨n, hn⟩ := hroot σ
    have hcomm : σ (τ α) = τ (σ α) := by
      have h := habel (σ.restrictScalars k) τ
      exact congrArg (fun e : Gal(M/k) => e α) h
    have h1 : σ (τ α) = (algebraMap K M ζ) ^ (g * n) * τ α := by
      rw [hcomm, hn, map_mul, map_pow, hτcom, hδζ, map_pow, ← pow_mul]
    have h2 : σ (α ^ g) = (algebraMap K M ζ) ^ (g * n) * α ^ g := by
      rw [map_pow, hn, mul_pow, ← pow_mul, mul_comm n g]
    rw [map_div₀, h1, h2, mul_div_mul_left _ _ (pow_ne_zero _ hξ0)]
  obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (τ α / α ^ g)).mpr hfix
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact hβ0 ((div_eq_zero_iff.mp hy.symm).resolve_right hαg0)
  refine ⟨y, hy0, (algebraMap K M).injective ?_⟩
  have hlhs : algebraMap K M (δ w) = (τ α) ^ ℓ := by rw [← hτcom, hw, map_pow]
  rw [hlhs, map_mul, map_pow, map_pow, hw, hy, div_pow, ← pow_mul, ← pow_mul, mul_comm ℓ g]
  field_simp

end Eigen

end InverseGalois.CFT
