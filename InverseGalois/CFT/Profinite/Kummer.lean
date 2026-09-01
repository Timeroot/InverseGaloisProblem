/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Hilbert90
import InverseGalois.CFT.Profinite.Trivial

/-!
# Kummer theory for an infinite Galois group

Let `Ω` be a Galois extension of a field `k` containing a primitive `n`-th root of unity, and let
`M` be a group of `n`-th roots of unity of `k` on which the Galois group acts trivially.  A unit
`a` of `k` with an `n`-th root `β` in the extension produces the cochain `σ ↦ σ β / β`.  Its values
are `n`-th roots of unity, hence come from `M`, and it is a smooth one cocycle because an element
of a Galois extension is fixed by an open normal subgroup, namely by the subgroup fixing the normal
closure of the field it generates.

Conversely every smooth one cocycle arises this way.  Pushed into the units of the extension, a
cocycle with values in `M` is still a smooth one cocycle, so Hilbert's theorem ninety for an
infinite Galois group produces a single unit `β` whose coboundary is the given cocycle; the `n`-th
power of `β` is fixed by the whole Galois group and therefore is a unit of the base.

The class of a unit of the base is trivial exactly when that unit is an `n`-th power there: for a
trivial action every coboundary is trivial, so a trivial class means the radical is fixed by the
Galois group and hence already lies in the base, while conversely two `n`-th roots of the same
element differ by a root of unity of the base.

## Main results

* `InverseGalois.CFT.exists_isOpenNormal_forall_apply_eq`: an element of a Galois extension is
  fixed by an open normal subgroup of the Galois group.
* `InverseGalois.CFT.exists_ι_eq_of_pow_eq_one`: an `n`-th root of unity of the extension comes
  from the coefficients.
* `InverseGalois.CFT.exists_isMulCocycle₁_kummer`: **the Kummer cocycle of a unit of the base with
  an `n`-th root in the extension.**
* `InverseGalois.CFT.exists_pow_eq_of_isMulCocycle₁`: **every smooth one cocycle with coefficients
  in the `n`-th roots of unity is the Kummer cocycle of a unit of the base.**
* `InverseGalois.CFT.smoothH1Mk_eq_one_iff_exists_pow`: **the class of a unit of the base is
  trivial exactly when that unit is an `n`-th power in the base.**

## Tags

Kummer theory, infinite Galois theory, Hilbert's theorem 90, root of unity, Galois cohomology
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open groupCohomology

/-! ### The coboundary of an element -/

section Coboundary

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- The coboundary of an element is a one cocycle. -/
theorem isMulCocycle₁_smul_div (x : M) : IsMulCocycle₁ (fun g : G => g • x / x) := by
  intro g h
  simp only [mul_smul, smul_div']
  rw [div_mul_div_cancel]

end Coboundary

/-! ### An element is fixed by an open normal subgroup -/

section Fixed

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- **An element of a Galois extension is fixed by an open normal subgroup of the Galois group**,
namely by the subgroup fixing the normal closure of the field it generates. -/
theorem exists_isOpenNormal_forall_apply_eq (x : Ω) :
    ∃ N : Subgroup Gal(Ω/k), IsOpenNormal N ∧ ∀ σ ∈ N, σ x = x := by
  haveI : FiniteDimensional k ↥(IntermediateField.adjoin k {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  refine ⟨(IntermediateField.normalClosure k ↥(IntermediateField.adjoin k {x}) Ω).fixingSubgroup,
    isOpenNormal_fixingSubgroup _, fun σ hσ =>
      (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ x ?_⟩
  exact IntermediateField.le_normalClosure (IntermediateField.adjoin k {x})
    (IntermediateField.mem_adjoin_simple_self k x)

/-- A unit of a Galois extension is fixed by an open normal subgroup of the Galois group. -/
theorem exists_isOpenNormal_forall_smul_eq (x : Ωˣ) :
    ∃ N : Subgroup Gal(Ω/k), IsOpenNormal N ∧ ∀ σ ∈ N, σ • x = x := by
  obtain ⟨N, hN, hfix⟩ := exists_isOpenNormal_forall_apply_eq (k := k) (x : Ω)
  exact ⟨N, hN, fun σ hσ => Units.ext (hfix σ hσ)⟩

end Fixed

/-! ### Roots of unity of the extension come from the coefficients -/

section Descent

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
variable {M : Type*} [CommGroup M] {n : ℕ} [NeZero n]

/-- The units of the base inject into the units of the extension. -/
theorem injective_units_algebraMap :
    Function.Injective (Units.map (algebraMap k Ω : k →* Ω)) := fun _ _ h =>
  Units.ext ((algebraMap k Ω).injective (congrArg Units.val h))

/-- The coefficients inject into the units of the extension. -/
theorem injective_units_algebraMap_comp {ι : M →* kˣ} (hιinj : Function.Injective ι) :
    Function.Injective fun m : M => Units.map (algebraMap k Ω : k →* Ω) (ι m) :=
  fun _ _ h => hιinj (injective_units_algebraMap h)

/-- **An `n`-th root of unity of an extension whose base contains a primitive `n`-th root of unity
comes from the coefficients.** -/
theorem exists_ι_eq_of_pow_eq_one {ζ : k} (hζ : IsPrimitiveRoot ζ n) {ι : M →* kˣ}
    (hιsurj : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y) {x : Ωˣ} (hx : x ^ n = 1) :
    ∃ m : M, Units.map (algebraMap k Ω : k →* Ω) (ι m) = x := by
  have hζΩ : IsPrimitiveRoot (algebraMap k Ω ζ) n :=
    hζ.map_of_injective (algebraMap k Ω).injective
  obtain ⟨i, -, hi⟩ := hζΩ.eq_pow_of_pow_eq_one (ξ := (x : Ω))
    (by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one])
  have hu : IsUnit ζ := hζ.isUnit (NeZero.ne n)
  have hyval : ((hu.unit ^ i : kˣ) : k) = ζ ^ i := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  have hyn : (hu.unit ^ i : kˣ) ^ n = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hyval, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow,
      Units.val_one]
  obtain ⟨m, hm⟩ := hιsurj _ hyn
  refine ⟨m, Units.ext ?_⟩
  have hval : ((Units.map (algebraMap k Ω : k →* Ω) (ι m) : Ωˣ) : Ω)
      = algebraMap k Ω ((ι m : kˣ) : k) := rfl
  rw [hval, hm, hyval, map_pow, hi]

end Descent

/-! ### The Kummer cocycle of a unit of the base -/

section Kummer

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M] {n : ℕ} [NeZero n]

omit [IsGalois k Ω] in
/-- An automorphism of the extension fixes the image of a unit of the base. -/
theorem smul_units_algebraMap (σ : Gal(Ω/k)) (y : kˣ) :
    σ • Units.map (algebraMap k Ω : k →* Ω) y = Units.map (algebraMap k Ω : k →* Ω) y :=
  Units.ext (σ.commutes (y : k))

/-- **The Kummer cocycle of a unit of the base**: an `n`-th root in the extension of a unit of the
base gives a smooth one cocycle whose values are `n`-th roots of unity of the base. -/
theorem exists_isMulCocycle₁_kummer {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m) {ι : M →* kˣ}
    (hιinj : Function.Injective ι) (hιsurj : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    {a : kˣ} {β : Ωˣ} (hβ : β ^ n = Units.map (algebraMap k Ω : k →* Ω) a) :
    ∃ (c : Gal(Ω/k) → M) (_ : IsMulCocycle₁ c) (_ : IsSmooth₁ c),
      ∀ σ : Gal(Ω/k), Units.map (algebraMap k Ω : k →* Ω) (ι (c σ)) = σ • β / β := by
  have hpow : ∀ σ : Gal(Ω/k), (σ • β / β) ^ n = 1 := by
    intro σ
    rw [div_pow, ← smul_pow', hβ, smul_units_algebraMap, div_self']
  choose c hc using fun σ : Gal(Ω/k) => exists_ι_eq_of_pow_eq_one hζ hιsurj (hpow σ)
  have hinj := injective_units_algebraMap_comp (Ω := Ω) hιinj
  have hstep : ∀ σ τ : Gal(Ω/k), (σ * τ) • β / β = (τ • β / β) * (σ • β / β) := by
    intro σ τ
    have h2 : (σ * τ) • β / β = σ • (τ • β / β) * (σ • β / β) := isMulCocycle₁_smul_div β σ τ
    rw [h2, ← hc τ, smul_units_algebraMap]
  have hcoc : IsMulCocycle₁ c := by
    intro σ τ
    refine hinj ?_
    show Units.map (algebraMap k Ω : k →* Ω) (ι (c (σ * τ)))
      = Units.map (algebraMap k Ω : k →* Ω) (ι (σ • c τ * c σ))
    rw [hc, htriv, map_mul, map_mul, hc, hc]
    exact hstep σ τ
  obtain ⟨N, hN, hfix⟩ := exists_isOpenNormal_forall_smul_eq (k := k) β
  refine ⟨c, hcoc, ⟨N, hN, fun σ ν hν => hinj ?_⟩, hc⟩
  show Units.map (algebraMap k Ω : k →* Ω) (ι (c (σ * ν)))
    = Units.map (algebraMap k Ω : k →* Ω) (ι (c σ))
  rw [hc, hc, mul_smul, hfix ν hν]

omit [NeZero n] in
/-- **Every smooth one cocycle with coefficients in the `n`-th roots of unity of the base is the
Kummer cocycle of a unit of the base.**  The cocycle pushed into the units of the extension is
still a smooth one cocycle, so Hilbert's theorem ninety produces a radical, and the `n`-th power of
that radical is fixed by the whole Galois group. -/
theorem exists_pow_eq_of_isMulCocycle₁ (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m)
    {ι : M →* kˣ} (hιpow : ∀ m : M, ι m ^ n = 1) {c : Gal(Ω/k) → M} (hc : IsMulCocycle₁ c)
    (hs : IsSmooth₁ c) :
    ∃ (a : kˣ) (β : Ωˣ), β ^ n = Units.map (algebraMap k Ω : k →* Ω) a ∧
      ∀ σ : Gal(Ω/k), Units.map (algebraMap k Ω : k →* Ω) (ι (c σ)) = σ • β / β := by
  have hucoc : IsMulCocycle₁ (fun σ : Gal(Ω/k) =>
      Units.map (algebraMap k Ω : k →* Ω) (ι (c σ))) := by
    intro σ τ
    show Units.map (algebraMap k Ω : k →* Ω) (ι (c (σ * τ)))
      = σ • Units.map (algebraMap k Ω : k →* Ω) (ι (c τ))
        * Units.map (algebraMap k Ω : k →* Ω) (ι (c σ))
    rw [smul_units_algebraMap, hc σ τ, htriv, map_mul, map_mul]
  have husm : IsSmooth₁ (fun σ : Gal(Ω/k) =>
      Units.map (algebraMap k Ω : k →* Ω) (ι (c σ))) := by
    obtain ⟨N, hN, hcon⟩ := hs
    refine ⟨N, hN, fun x ν hν => ?_⟩
    show Units.map (algebraMap k Ω : k →* Ω) (ι (c (x * ν)))
      = Units.map (algebraMap k Ω : k →* Ω) (ι (c x))
    rw [hcon x ν hν]
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_smooth hucoc husm
  have hβ' : ∀ σ : Gal(Ω/k),
      σ • β / β = Units.map (algebraMap k Ω : k →* Ω) (ι (c σ)) := fun σ => hβ σ
  have hfixpow : ∀ σ : Gal(Ω/k), σ • β ^ n = β ^ n := by
    intro σ
    have h2 : (σ • β / β) ^ n = 1 := by
      rw [hβ' σ, ← map_pow, hιpow, map_one]
    rw [div_pow] at h2
    rw [smul_pow']
    exact div_eq_one.1 h2
  obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed ((β ^ n : Ωˣ) : Ω)).2
    fun σ => congrArg Units.val (hfixpow σ)
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact (β ^ n).ne_zero hy.symm
  exact ⟨Units.mk0 y hy0, β, Units.ext hy.symm, fun σ => (hβ' σ).symm⟩

/-- **The class of a unit of the base is trivial exactly when that unit is an `n`-th power in the
base.** -/
theorem smoothH1Mk_eq_one_iff_exists_pow {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m) {ι : M →* kˣ}
    (hιinj : Function.Injective ι) (hιsurj : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    {a : kˣ} {β : Ωˣ} (hβ : β ^ n = Units.map (algebraMap k Ω : k →* Ω) a)
    {c : Gal(Ω/k) → M} (hc : IsMulCocycle₁ c) (hs : IsSmooth₁ c)
    (hcβ : ∀ σ : Gal(Ω/k), Units.map (algebraMap k Ω : k →* Ω) (ι (c σ)) = σ • β / β) :
    smoothH1Mk c hc hs = 1 ↔ ∃ b : kˣ, b ^ n = a := by
  rw [smoothH1Mk_eq_one_iff_of_trivial htriv]
  constructor
  · intro h
    have hfix : ∀ σ : Gal(Ω/k), σ • β = β := by
      intro σ
      have h1 := hcβ σ
      rw [h, Pi.one_apply, map_one, map_one, eq_comm, div_eq_one] at h1
      exact h1
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed ((β : Ωˣ) : Ω)).2
      fun σ => congrArg Units.val (hfix σ)
    have hy0 : y ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hy
      exact β.ne_zero hy.symm
    have hmap : Units.map (algebraMap k Ω : k →* Ω) (Units.mk0 y hy0) = β := Units.ext hy
    refine ⟨Units.mk0 y hy0, injective_units_algebraMap (Ω := Ω) ?_⟩
    rw [map_pow, hmap, hβ]
  · rintro ⟨b, hb⟩
    have hγ : (β / Units.map (algebraMap k Ω : k →* Ω) b) ^ n = 1 := by
      rw [div_pow, hβ, ← hb, map_pow, div_self']
    obtain ⟨m₀, hm₀⟩ := exists_ι_eq_of_pow_eq_one hζ hιsurj hγ
    have hβeq : β = Units.map (algebraMap k Ω : k →* Ω) (ι m₀ * b) := by
      rw [map_mul, hm₀, div_mul_cancel]
    funext σ
    refine injective_units_algebraMap_comp (Ω := Ω) hιinj ?_
    show Units.map (algebraMap k Ω : k →* Ω) (ι (c σ))
      = Units.map (algebraMap k Ω : k →* Ω) (ι 1)
    rw [hcβ, map_one, map_one, hβeq, smul_units_algebraMap, div_self']

end Kummer

end InverseGalois.CFT
