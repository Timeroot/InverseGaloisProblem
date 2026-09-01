/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Kummer

/-!
# The Kummer isomorphism for an infinite Galois group

The cocycles of the previous file are assembled into a homomorphism.  The data are a Galois
extension `Ω` of a field `k`, a group `M` mapping injectively into the units of `k` with image the
`n`-th roots of unity there, a primitive `n`-th root of unity in `k`, and an `n`-th root in the
extension of every unit of the base.

Two `n`-th roots of the same unit differ by an `n`-th root of unity of the base, which every
automorphism fixes, so the coboundary of a root does not depend on which root is taken.  A cocycle
is determined by its coboundary because the coefficients inject into the units of the extension, so
choosing a root of each unit of the base gives a well defined cochain, multiplicative in the unit
because the product of two roots is a root of the product.  Its class is trivial exactly when the
unit is an `n`-th power in the base, and Hilbert's theorem ninety makes it surjective, so the
quotient of the units of the base by the `n`-th powers is the first cohomology.

## Main results

* `InverseGalois.CFT.IsKummerData`: the data of a base whose `n`-th roots of unity are `M` and
  whose units all have an `n`-th root in the extension.
* `InverseGalois.CFT.IsKummerData.kummerHom`: **the Kummer homomorphism** from the units of the
  base to the first cohomology of the Galois group with coefficients in the roots of unity.
* `InverseGalois.CFT.IsKummerData.ker_kummerHom`: **its kernel is the `n`-th powers.**
* `InverseGalois.CFT.IsKummerData.kummerHom_surjective`: **it is surjective.**
* `InverseGalois.CFT.IsKummerData.kummerEquiv`: **the Kummer isomorphism** between the units of the
  base modulo `n`-th powers and the first cohomology.

## Tags

Kummer theory, infinite Galois theory, Hilbert's theorem 90, root of unity, Galois cohomology
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open groupCohomology

/-! ### The coboundary does not depend on the chosen root -/

section Root

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M] {n : ℕ} [NeZero n]

omit [IsGalois k Ω] [MulDistribMulAction Gal(Ω/k) M] in
/-- **Two `n`-th roots of the same unit have the same coboundary**, because they differ by an
`n`-th root of unity of the base, which every automorphism fixes. -/
theorem smul_div_eq_of_pow_eq {ζ : k} (hζ : IsPrimitiveRoot ζ n) {ι : M →* kˣ}
    (hιsurj : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y) {β β' : Ωˣ} (hββ' : β ^ n = β' ^ n)
    (σ : Gal(Ω/k)) : σ • β / β = σ • β' / β' := by
  have hq : (β / β') ^ n = 1 := by rw [div_pow, hββ', div_self']
  obtain ⟨m, hm⟩ := exists_ι_eq_of_pow_eq_one hζ hιsurj hq
  have hβ : β = Units.map (algebraMap k Ω : k →* Ω) (ι m) * β' := by rw [hm, div_mul_cancel]
  rw [hβ, smul_mul', smul_units_algebraMap, mul_div_mul_left_eq_div]

end Root

/-! ### The data of a Kummer situation -/

/-- **The data of a Kummer situation**: a group `M` whose image in the units of `k` is the group of
`n`-th roots of unity, with the Galois group acting trivially on it, together with a primitive
`n`-th root of unity in `k` and an `n`-th root in `Ω` of every unit of `k`. -/
structure IsKummerData (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] (M : Type*) [CommGroup M]
    [MulDistribMulAction Gal(Ω/k) M] (ι : M →* kˣ) (n : ℕ) : Prop where
  /-- The base contains a primitive `n`-th root of unity. -/
  exists_isPrimitiveRoot : ∃ ζ : k, IsPrimitiveRoot ζ n
  /-- The Galois group acts trivially on the coefficients. -/
  smul_eq : ∀ (g : Gal(Ω/k)) (m : M), g • m = m
  /-- The coefficients embed into the units of the base. -/
  injective : Function.Injective ι
  /-- The image of the coefficients consists of `n`-th roots of unity. -/
  pow_eq_one : ∀ m : M, ι m ^ n = 1
  /-- Every `n`-th root of unity of the base comes from the coefficients. -/
  exists_ι_eq : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y
  /-- Every unit of the base has an `n`-th root in the extension. -/
  exists_root : ∀ a : kˣ, ∃ β : Ωˣ, β ^ n = Units.map (algebraMap k Ω : k →* Ω) a

namespace IsKummerData

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M] {ι : M →* kˣ} {n : ℕ}
variable [NeZero n]

/-- A primitive `n`-th root of unity of the base. -/
noncomputable def primitiveRoot (h : IsKummerData k Ω M ι n) : k :=
  h.exists_isPrimitiveRoot.choose

omit [IsGalois k Ω] [NeZero n] in
/-- The chosen root of unity of the base is primitive. -/
theorem isPrimitiveRoot_primitiveRoot (h : IsKummerData k Ω M ι n) :
    IsPrimitiveRoot h.primitiveRoot n := h.exists_isPrimitiveRoot.choose_spec

/-- A chosen `n`-th root in the extension of a unit of the base. -/
noncomputable def root (h : IsKummerData k Ω M ι n) (a : kˣ) : Ωˣ := (h.exists_root a).choose

omit [IsGalois k Ω] [NeZero n] in
/-- The chosen root of a unit of the base is an `n`-th root of it. -/
theorem root_pow (h : IsKummerData k Ω M ι n) (a : kˣ) :
    h.root a ^ n = Units.map (algebraMap k Ω : k →* Ω) a := (h.exists_root a).choose_spec

/-- The Kummer cochain of a unit of the base exists. -/
private theorem exists_cochain (h : IsKummerData k Ω M ι n) (a : kˣ) :
    ∃ (c : Gal(Ω/k) → M) (_ : IsMulCocycle₁ c) (_ : IsSmooth₁ c),
      ∀ σ : Gal(Ω/k), Units.map (algebraMap k Ω : k →* Ω) (ι (c σ)) = σ • h.root a / h.root a :=
  exists_isMulCocycle₁_kummer h.isPrimitiveRoot_primitiveRoot h.smul_eq h.injective h.exists_ι_eq
    (h.root_pow a)

/-- **The Kummer cochain of a unit of the base**, the coboundary of a chosen `n`-th root read in
the coefficients. -/
noncomputable def cochain (h : IsKummerData k Ω M ι n) (a : kˣ) : Gal(Ω/k) → M :=
  (h.exists_cochain a).choose

/-- The Kummer cochain is a one cocycle. -/
theorem cochain_isMulCocycle₁ (h : IsKummerData k Ω M ι n) (a : kˣ) :
    IsMulCocycle₁ (h.cochain a) := (h.exists_cochain a).choose_spec.choose

/-- The Kummer cochain is smooth. -/
theorem cochain_isSmooth₁ (h : IsKummerData k Ω M ι n) (a : kˣ) :
    IsSmooth₁ (h.cochain a) := (h.exists_cochain a).choose_spec.choose_spec.choose

/-- The image of the Kummer cochain is the coboundary of the chosen root. -/
theorem cochain_spec (h : IsKummerData k Ω M ι n) (a : kˣ) (σ : Gal(Ω/k)) :
    Units.map (algebraMap k Ω : k →* Ω) (ι (h.cochain a σ)) = σ • h.root a / h.root a :=
  (h.exists_cochain a).choose_spec.choose_spec.choose_spec σ

/-- The Kummer cochain is the only cochain whose image is the coboundary of an `n`-th root. -/
theorem cochain_unique (h : IsKummerData k Ω M ι n) (a : kˣ) {c : Gal(Ω/k) → M} {β : Ωˣ}
    (hβ : β ^ n = Units.map (algebraMap k Ω : k →* Ω) a)
    (hc : ∀ σ : Gal(Ω/k), Units.map (algebraMap k Ω : k →* Ω) (ι (c σ)) = σ • β / β) :
    c = h.cochain a := by
  funext σ
  refine injective_units_algebraMap_comp (Ω := Ω) h.injective ?_
  show Units.map (algebraMap k Ω : k →* Ω) (ι (c σ))
    = Units.map (algebraMap k Ω : k →* Ω) (ι (h.cochain a σ))
  rw [hc, h.cochain_spec]
  exact smul_div_eq_of_pow_eq h.isPrimitiveRoot_primitiveRoot h.exists_ι_eq
    (hβ.trans (h.root_pow a).symm) σ

/-- The Kummer cochain of a product is the product of the Kummer cochains. -/
theorem cochain_mul (h : IsKummerData k Ω M ι n) (a b : kˣ) :
    h.cochain (a * b) = h.cochain a * h.cochain b := by
  refine (h.cochain_unique (a * b) (β := h.root a * h.root b) ?_ ?_).symm
  · rw [mul_pow, h.root_pow, h.root_pow, map_mul]
  · intro σ
    show Units.map (algebraMap k Ω : k →* Ω) (ι (h.cochain a σ * h.cochain b σ)) = _
    rw [map_mul, map_mul, h.cochain_spec, h.cochain_spec, div_mul_div_comm, ← smul_mul']

/-! ### The Kummer homomorphism -/

/-- The class of the Kummer cochain of a unit of the base. -/
noncomputable def kummerClass (h : IsKummerData k Ω M ι n) (a : kˣ) : SmoothH1 Gal(Ω/k) M :=
  smoothH1Mk (h.cochain a) (h.cochain_isMulCocycle₁ a) (h.cochain_isSmooth₁ a)

/-- **The class of a unit of the base is trivial exactly when it is an `n`-th power there.** -/
theorem kummerClass_eq_one_iff (h : IsKummerData k Ω M ι n) (a : kˣ) :
    h.kummerClass a = 1 ↔ ∃ b : kˣ, b ^ n = a :=
  smoothH1Mk_eq_one_iff_exists_pow h.isPrimitiveRoot_primitiveRoot h.smul_eq h.injective
    h.exists_ι_eq (h.root_pow a) (h.cochain_isMulCocycle₁ a) (h.cochain_isSmooth₁ a)
    (h.cochain_spec a)

/-- **The Kummer homomorphism** from the units of the base to the first cohomology of the Galois
group with coefficients in the `n`-th roots of unity. -/
noncomputable def kummerHom (h : IsKummerData k Ω M ι n) : kˣ →* SmoothH1 Gal(Ω/k) M where
  toFun := h.kummerClass
  map_one' := (h.kummerClass_eq_one_iff 1).2 ⟨1, one_pow n⟩
  map_mul' a b := by
    show smoothH1Mk (h.cochain (a * b)) _ _
      = smoothH1Mk (h.cochain a) _ _ * smoothH1Mk (h.cochain b) _ _
    rw [← smoothH1Mk_mul (h.cochain_isMulCocycle₁ a) (h.cochain_isSmooth₁ a)
      (h.cochain_isMulCocycle₁ b) (h.cochain_isSmooth₁ b)]
    congr 1
    exact h.cochain_mul a b

/-- The Kummer homomorphism sends a unit of the base to the class of its Kummer cochain. -/
theorem kummerHom_apply (h : IsKummerData k Ω M ι n) (a : kˣ) :
    h.kummerHom a = h.kummerClass a := rfl

/-- **The kernel of the Kummer homomorphism is the group of `n`-th powers.** -/
theorem ker_kummerHom (h : IsKummerData k Ω M ι n) :
    h.kummerHom.ker = (powMonoidHom n : kˣ →* kˣ).range := by
  ext a
  rw [MonoidHom.mem_ker, kummerHom_apply, h.kummerClass_eq_one_iff, MonoidHom.mem_range]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb⟩⟩

/-- **The Kummer homomorphism is surjective**, by Hilbert's theorem ninety for an infinite Galois
group. -/
theorem kummerHom_surjective (h : IsKummerData k Ω M ι n) :
    Function.Surjective h.kummerHom := by
  intro x
  obtain ⟨c, hc, hs, rfl⟩ := smoothH1Mk_surjective x
  obtain ⟨a, β, hβ, hcβ⟩ := exists_pow_eq_of_isMulCocycle₁ h.smul_eq h.pow_eq_one hc hs
  obtain rfl : c = h.cochain a := h.cochain_unique a hβ hcβ
  exact ⟨a, rfl⟩

/-- **The Kummer isomorphism**: the units of the base modulo the `n`-th powers are the first
cohomology of the Galois group with coefficients in the `n`-th roots of unity. -/
noncomputable def kummerEquiv (h : IsKummerData k Ω M ι n) :
    kˣ ⧸ (powMonoidHom n : kˣ →* kˣ).range ≃* SmoothH1 Gal(Ω/k) M :=
  (QuotientGroup.quotientMulEquivOfEq h.ker_kummerHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective h.kummerHom h.kummerHom_surjective)

end IsKummerData

/-! ### Kummer data exist -/

section Witness

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {n : ℕ} [NeZero n]

/-- Over an algebraically closed extension every unit of the base has an `n`-th root. -/
theorem exists_units_pow_eq [IsAlgClosed Ω] (a : kˣ) :
    ∃ β : Ωˣ, β ^ n = Units.map (algebraMap k Ω : k →* Ω) a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k Ω (a : k)) (NeZero.pos n)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne n)] at hz
    exact (Units.map (algebraMap k Ω : k →* Ω) a).ne_zero hz.symm
  exact ⟨Units.mk0 z hz0,
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz]; rfl)⟩

/-- The Galois group of an extension acts trivially on the roots of unity of the base. -/
def rootsOfUnityTrivialAction : MulDistribMulAction Gal(Ω/k) ↥(rootsOfUnity n k) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

omit [NeZero n] in
/-- **Kummer data exist**: if the base contains a primitive `n`-th root of unity and every unit of
the base has an `n`-th root in the extension, then the `n`-th roots of unity of the base, with the
trivial action, are Kummer data. -/
theorem isKummerData_rootsOfUnity {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (hroot : ∀ a : kˣ, ∃ β : Ωˣ, β ^ n = Units.map (algebraMap k Ω : k →* Ω) a) :
    letI := rootsOfUnityTrivialAction (k := k) (Ω := Ω) (n := n)
    IsKummerData k Ω ↥(rootsOfUnity n k) (rootsOfUnity n k).subtype n := by
  letI := rootsOfUnityTrivialAction (k := k) (Ω := Ω) (n := n)
  exact
    { exists_isPrimitiveRoot := ⟨ζ, hζ⟩
      smul_eq := fun _ _ => rfl
      injective := fun _ _ h => Subtype.ext h
      pow_eq_one := fun m => (mem_rootsOfUnity n (m : kˣ)).1 m.2
      exists_ι_eq := fun y hy => ⟨⟨y, (mem_rootsOfUnity n y).2 hy⟩, rfl⟩
      exists_root := hroot }

end Witness

end InverseGalois.CFT
