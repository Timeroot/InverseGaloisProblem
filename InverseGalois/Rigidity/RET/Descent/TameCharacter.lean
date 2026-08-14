/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The tame inertia character

Let `L` be a field with a valuation subring `A` that is a discrete valuation ring, and let `K` be a
subfield of `L` (`Algebra K L`).  Mathlib provides the decomposition subgroup
`A.decompositionSubgroup K ≤ (L ≃ₐ[K] L)` acting on `A`, and the inertia subgroup
`A.inertiaSubgroup K` — the kernel of the action on the residue field `IsLocalRing.ResidueField A`.

For an inertia element `g` and a uniformizer `π` of `A`, `g • π` is again a uniformizer, so `g • π`
and `π` are associate: there is a unique unit `u_g ∈ Aˣ` with `g • π = u_g · π`.  The **tame
character** sends `g` to the residue of `u_g`:

  `θ : A.inertiaSubgroup K → (ResidueField A)ˣ`,  `θ(g) = (g • π / π) mod 𝔪`.

## Main results

* `tameUnit` / `tameUnit_spec` / `tameUnit_unique` — the unit `u_g` with `g • π = u_g · π`, and its
  uniqueness.
* `θ` / `θ_apply` — the tame character valued in `(ResidueField A)ˣ`.
* `θ_independent_of_uniformizer` — `θ` does not depend on the chosen uniformizer.
* `θHom` — `θ` is a monoid homomorphism `A.inertiaSubgroup K →* (ResidueField A)ˣ`.
-/


open scoped Pointwise
open IsLocalRing

namespace TameCharacter

variable {L : Type*} [Field L] (K : Type*) [Field K] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]

/-- Shorthand for the decomposition subgroup. -/
local notation "D" => A.decompositionSubgroup K
/-- Shorthand for the inertia subgroup (a subgroup of `D`). -/
local notation "I" => A.inertiaSubgroup K

/-! ### The action sends uniformizers to uniformizers -/

omit [IsDiscreteValuationRing A] in
/-- An element of the decomposition group acts as a ring automorphism, hence preserves
irreducibility: `g • π` is irreducible whenever `π` is. -/
theorem irreducible_smul (g : D) {π : A} (hπ : Irreducible π) :
    Irreducible ((g • π : A)) := by
  have h := MulEquiv.irreducible_iff
    (f := MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A g) (x := π)
  simpa using h.mpr hπ

/-! ### The tame unit `g • π / π ∈ Aˣ` -/

/-- Since `g • π` and `π` are both uniformizers of the discrete valuation ring `A`, they are
associate, so there is a (necessarily unique) unit `w` with `g • π = w * π`. -/
theorem exists_tameUnit (g : D) {π : A} (hπ : Irreducible π) :
    ∃ w : Aˣ, (g • π : A) = (w : A) * π := by
  obtain ⟨c, hc⟩ :=
    IsDiscreteValuationRing.associated_of_irreducible (R := A) (irreducible_smul K A g hπ) hπ
  refine ⟨c⁻¹, ?_⟩
  have h1 : (c : A) * ((c⁻¹ : Aˣ) : A) = 1 := by simp
  calc (g • π : A)
      = ((g • π : A) * (c : A)) * ((c⁻¹ : Aˣ) : A) := by rw [mul_assoc, h1, mul_one]
    _ = (π : A) * ((c⁻¹ : Aˣ) : A) := by rw [hc]
    _ = ((c⁻¹ : Aˣ) : A) * π := by rw [mul_comm]

/-- The unit `w` with `g • π = w * π`. -/
noncomputable def tameUnit (g : D) {π : A} (hπ : Irreducible π) : Aˣ :=
  (exists_tameUnit K A g hπ).choose

theorem tameUnit_spec (g : D) {π : A} (hπ : Irreducible π) :
    (g • π : A) = (tameUnit K A g hπ : A) * π :=
  (exists_tameUnit K A g hπ).choose_spec

/-- Uniqueness: any unit exhibiting `g • π` as an associate of `π` equals `tameUnit`. -/
theorem tameUnit_unique (g : D) {π : A} (hπ : Irreducible π) (w : Aˣ)
    (hw : (g • π : A) = (w : A) * π) : w = tameUnit K A g hπ := by
  have h := tameUnit_spec K A g hπ
  have hπ0 : (π : A) ≠ 0 := hπ.ne_zero
  have : (w : A) = (tameUnit K A g hπ : A) := by
    apply mul_right_cancel₀ hπ0
    rw [← hw, h]
  exact Units.ext this

/-- The image `g • u` of a unit, as a unit (via the ring hom `x ↦ g • x`). -/
noncomputable def smulUnit (g : D) (u : Aˣ) : Aˣ :=
  Units.map (MulSemiringAction.toRingHom (A.decompositionSubgroup K) A g).toMonoidHom u

omit [IsDiscreteValuationRing A] in
@[simp]
theorem smulUnit_coe (g : D) (u : Aˣ) : (smulUnit K A g u : A) = g • (u : A) := by
  simp [smulUnit, MulSemiringAction.toRingHom_apply]

/-! ### The tame character -/

/-- The **tame character** `θ : I → (ResidueField A)ˣ`, `θ(g) = (g • π / π) mod 𝔪`, defined via a
uniformizer `π`. -/
noncomputable def θ {π : A} (hπ : Irreducible π) : I → (ResidueField A)ˣ :=
  fun g => Units.map (IsLocalRing.residue A).toMonoidHom
    (tameUnit K A (g : D) hπ)

theorem θ_apply {π : A} (hπ : Irreducible π) (g : I) :
    (θ K A hπ g : ResidueField A) = IsLocalRing.residue A (tameUnit K A (g : D) hπ : A) := rfl

/-! ### Inertia acts trivially on the residue field -/

omit [IsDiscreteValuationRing A] in
/-- Elements of the inertia subgroup act trivially on the residue field: this is the defining
property of `inertiaSubgroup` (it is the kernel of the action on the residue field). -/
theorem inertia_smul_residue (g : I) (r : ResidueField A) :
    (g : D) • r = r := by
  have hg : (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A)) (g : D) = 1 :=
    MonoidHom.mem_ker.mp g.2
  have := congrArg (fun e : RingAut (ResidueField A) => e r) hg
  simpa using this

/-! ### `θ` is a group homomorphism -/

/-- The cocycle identity for `tameUnit`: `tameUnit (g*h) = (g • tameUnit h) * tameUnit g`. -/
theorem tameUnit_mul (g h : D) {π : A} (hπ : Irreducible π) :
    tameUnit K A (g * h) hπ = smulUnit K A g (tameUnit K A h hπ) * tameUnit K A g hπ := by
  symm
  apply tameUnit_unique
  have hh := tameUnit_spec K A h hπ
  have hg := tameUnit_spec K A g hπ
  calc ((g * h) • π : A)
      = g • (h • π : A) := by rw [mul_smul]
    _ = g • ((tameUnit K A h hπ : A) * π) := by rw [hh]
    _ = (g • (tameUnit K A h hπ : A)) * (g • π : A) := by rw [smul_mul']
    _ = (g • (tameUnit K A h hπ : A)) * ((tameUnit K A g hπ : A) * π) := by rw [hg]
    _ = ((smulUnit K A g (tameUnit K A h hπ) * tameUnit K A g hπ : Aˣ) : A) * π := by
          push_cast [smulUnit_coe]; ring

/-- `θ` is a monoid homomorphism `I → (ResidueField A)ˣ`. -/
noncomputable def θHom {π : A} (hπ : Irreducible π) : I →* (ResidueField A)ˣ where
  toFun := θ K A hπ
  map_one' := by
    apply Units.ext
    rw [θ_apply]
    have h1 : tameUnit K A ((1 : I) : D) hπ = 1 := by
      symm; apply tameUnit_unique; simp
    rw [h1]; simp
  map_mul' g h := by
    apply Units.ext
    have hcoc := tameUnit_mul K A (g : D) (h : D) hπ
    rw [Units.val_mul, θ_apply, θ_apply, θ_apply]
    have hcast : ((g * h : I) : D) = (g : D) * (h : D) := rfl
    rw [hcast, hcoc, Units.val_mul, map_mul, smulUnit_coe, IsLocalRing.ResidueField.residue_smul,
      inertia_smul_residue K A g]
    ring

/-! ### Independence of the uniformizer -/

/-- `θ` does not depend on the choice of uniformizer. -/
theorem θ_independent_of_uniformizer {π π' : A} (hπ : Irreducible π) (hπ' : Irreducible π')
    (g : I) : θ K A hπ g = θ K A hπ' g := by
  apply Units.ext
  rw [θ_apply, θ_apply]
  obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_of_irreducible (R := A) hπ' hπ
  have hv' : (π : A) = (v : A) * π' := by rw [← hv]; ring
  have hgπ := tameUnit_spec K A (g : D) hπ
  have hgπ' := tameUnit_spec K A (g : D) hπ'
  have e1 : (g : D) • (π : A) = ((g : D) • (v : A)) * ((tameUnit K A (g : D) hπ' : A) * π') := by
    conv_lhs => rw [hv']
    rw [smul_mul', hgπ']
  have e2 : (g : D) • (π : A) = (tameUnit K A (g : D) hπ : A) * ((v : A) * π') := by
    rw [hgπ, ← hv']
  have hπ'0 : (π' : A) ≠ 0 := hπ'.ne_zero
  have ecancel : ((g : D) • (v : A)) * (tameUnit K A (g : D) hπ' : A)
      = (tameUnit K A (g : D) hπ : A) * (v : A) := by
    have hEq : (((g : D) • (v : A)) * (tameUnit K A (g : D) hπ' : A)) * π'
        = ((tameUnit K A (g : D) hπ : A) * (v : A)) * π' := by
      have h12 := e1.symm.trans e2
      ring_nf
      ring_nf at h12
      linear_combination h12
    exact mul_right_cancel₀ hπ'0 hEq
  have hres := congrArg (IsLocalRing.residue A) ecancel
  rw [map_mul, map_mul, IsLocalRing.ResidueField.residue_smul, inertia_smul_residue K A g] at hres
  have hv0 : IsLocalRing.residue A (v : A) ≠ 0 := (v.isUnit.map (IsLocalRing.residue A)).ne_zero
  apply mul_left_cancel₀ hv0
  rw [mul_comm (IsLocalRing.residue A (v : A)) (IsLocalRing.residue A (tameUnit K A (g : D) hπ : A))]
  rw [← hres]

/-! ### Cyclotomic equivariance (the branch-cycle formula, algebraic core) -/

omit [IsDiscreteValuationRing A] in
/-- The conjugate `σ g σ⁻¹` of an inertia element `g` by a decomposition element `σ` lies again in
the inertia subgroup: the inertia subgroup is normal in the decomposition subgroup (it is the kernel
of the action on the residue field). -/
theorem conj_mem_inertia (σ : D) (g : I) : σ * (g : D) * σ⁻¹ ∈ I := by
  haveI hN : (A.inertiaSubgroup K).Normal := MonoidHom.normal_ker _
  exact hN.conj_mem (g : D) g.2 σ

/-- **Equivariance of the tame character under the decomposition group.**  For `σ` in the
decomposition group and `g` in the inertia subgroup, the tame character of the conjugate `σ g σ⁻¹`
is the `σ`-twist of the tame character of `g`:

  `θ (σ g σ⁻¹) = σ • θ (g)`   in the residue field.

Composed with the cyclotomic action of `σ` on the roots of unity in the residue field, this is
Fried's branch-cycle formula: the arithmetic Galois action raises the tame inertia to the cyclotomic
power. -/
theorem θ_conj (σ : D) (g : I) {π : A} (hπ : Irreducible π) :
    (θ K A hπ ⟨σ * (g : D) * σ⁻¹, conj_mem_inertia K A σ g⟩ : ResidueField A)
      = σ • (θ K A hπ g : ResidueField A) := by
  have hπ' : Irreducible ((σ • π : A)) := irreducible_smul K A σ hπ
  set gc : I := ⟨σ * (g : D) * σ⁻¹, conj_mem_inertia K A σ g⟩ with hgc
  have hgcD : (gc : D) = σ * (g : D) * σ⁻¹ := rfl
  -- the tame unit of the conjugate, computed at the uniformizer `σ • π`, is `σ • u_g`.
  have hunit : tameUnit K A (σ * (g : D) * σ⁻¹) hπ'
      = smulUnit K A σ (tameUnit K A (g : D) hπ) := by
    symm
    apply tameUnit_unique
    have hg := tameUnit_spec K A (g : D) hπ
    calc ((σ * (g : D) * σ⁻¹) • (σ • π) : A)
        = σ • ((g : D) • π) := by rw [mul_smul, mul_smul, inv_smul_smul]
      _ = σ • ((tameUnit K A (g : D) hπ : A) * π) := by rw [hg]
      _ = (σ • (tameUnit K A (g : D) hπ : A)) * (σ • π) := by rw [smul_mul']
      _ = ((smulUnit K A σ (tameUnit K A (g : D) hπ) : A)) * (σ • π) := by rw [smulUnit_coe]
  -- compute `θ` at the conjugate using the uniformizer `σ • π`, then read off the twist.
  rw [θ_independent_of_uniformizer K A hπ hπ' gc, θ_apply, hgcD, hunit, smulUnit_coe,
    IsLocalRing.ResidueField.residue_smul, θ_apply]

/-! ### The tame character is valued in roots of unity -/

/-- The tame character is valued in roots of unity: the order of `θ (g)` divides the order of the
inertia element `g` (the ramification index at the place). -/
theorem orderOf_θHom_dvd {π : A} (hπ : Irreducible π) (g : I) :
    orderOf (θHom K A hπ g) ∣ orderOf g := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow, pow_orderOf_eq_one, map_one]

/-! ### The branch-cycle formula at the level of the inertia group -/

/-- **Fried's branch-cycle formula, at the level of the inertia group.**  When the tame character
`θHom` is injective, the equivariance `θ (σ g σ⁻¹) = σ • θ (g)` (`θ_conj`) upgrades from the residue
field to the inertia group itself: for `σ` in the decomposition group and `g` in the inertia
subgroup, the conjugate `σ g σ⁻¹` is the `k`-th power of `g`, where `k` is the exponent by which `σ`
acts on the root of unity `θ (g)`:

  `σ • θ (g) = θ (g) ^ k  ⟹  σ g σ⁻¹ = g ^ k`. -/
theorem conj_eq_pow_of_θInjective {π : A} (hπ : Irreducible π)
    (hinj : Function.Injective (θHom K A hπ)) (σ : D) (g : I) (k : ℕ)
    (hcyc : σ • (θHom K A hπ g : ResidueField A) = (θHom K A hπ g : ResidueField A) ^ k) :
    (⟨σ * (g : D) * σ⁻¹, conj_mem_inertia K A σ g⟩ : I) = g ^ k := by
  apply hinj
  rw [map_pow]
  apply Units.ext
  calc (θHom K A hπ ⟨σ * (g : D) * σ⁻¹, conj_mem_inertia K A σ g⟩ : ResidueField A)
      = σ • (θHom K A hπ g : ResidueField A) := θ_conj K A σ g hπ
    _ = (θHom K A hπ g : ResidueField A) ^ k := hcyc
    _ = ((θHom K A hπ g) ^ k : (ResidueField A)ˣ) := (Units.val_pow_eq_pow_val _ _).symm

/-- When the tame character is injective and the inertia group is finite, the inertia group is
cyclic: `θHom` embeds it into the units of the residue field, and a finite subgroup of the units of a
field (an integral domain) is cyclic. -/
theorem isCyclic_inertia_of_θInjective {π : A} (hπ : Irreducible π) [Finite I]
    (hinj : Function.Injective (θHom K A hπ)) : IsCyclic I :=
  isCyclic_of_subgroup_isDomain ((Units.coeHom (ResidueField A)).comp (θHom K A hπ))
    (fun a b h => hinj (Units.ext (by simpa using h)))

/-! ### The cyclotomic action on residue roots of unity -/

omit [IsDiscreteValuationRing A] in
/-- A decomposition element acts on the `M`-th roots of unity of the residue field through a fixed
exponent.  Given a primitive `M`-th root of unity `ζ` in the residue field, there is an exponent `c`
(the cyclotomic exponent of `σ` at the place) with `σ • x = x ^ c` for every `M`-th root of unity
`x`; indeed `σ` maps `ζ` to some power `ζ ^ c`, and every `M`-th root of unity is a power of `ζ`. -/
theorem exists_cyclotomic_exponent {M : ℕ} [NeZero M] {ζ : ResidueField A}
    (hζ : IsPrimitiveRoot ζ M) (σ : D) :
    ∃ c : ℕ, ∀ x : ResidueField A, x ^ M = 1 → σ • x = x ^ c := by
  have hpow : (σ • ζ) ^ M = 1 := by rw [← smul_pow', hζ.pow_eq_one, smul_one]
  obtain ⟨c, _, hc⟩ := hζ.eq_pow_of_pow_eq_one hpow
  refine ⟨c, fun x hx => ?_⟩
  obtain ⟨j, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [smul_pow', ← hc, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **Fried's branch-cycle formula, with the cyclotomic exponent.**  When the tame character is
injective and the residue field contains a primitive `M`-th root of unity `ζ`, conjugation of an
inertia element `g` (with `θ (g)` an `M`-th root of unity) by a decomposition element `σ` raises `g`
to the cyclotomic power `c` by which `σ` acts on the `M`-th roots of unity:

  `σ g σ⁻¹ = g ^ c`,  where `σ • ζ = ζ ^ c`.

This packages `exists_cyclotomic_exponent` with `conj_eq_pow_of_θInjective`: the arithmetic action on
the tame inertia is read off the arithmetic action on the roots of unity. -/
theorem conj_eq_pow_cyclotomic_of_θInjective {π : A} (hπ : Irreducible π)
    (hinj : Function.Injective (θHom K A hπ)) {M : ℕ} [NeZero M] {ζ : ResidueField A}
    (hζ : IsPrimitiveRoot ζ M) (σ : D) (g : I) (hgM : (θHom K A hπ g) ^ M = 1) :
    ∃ c : ℕ, (⟨σ * (g : D) * σ⁻¹, conj_mem_inertia K A σ g⟩ : I) = g ^ c := by
  obtain ⟨c, hc⟩ := exists_cyclotomic_exponent K A hζ σ
  refine ⟨c, conj_eq_pow_of_θInjective K A hπ hinj σ g c (hc _ ?_)⟩
  rw [← Units.val_pow_eq_pow_val, hgM, Units.val_one]

/-! ### The cyclotomic exponent as a unit of `ZMod M` -/

omit [IsDiscreteValuationRing A] in
/-- The cyclotomic exponent of a decomposition element, as a **unit** of `ZMod M`.

This refines `exists_cyclotomic_exponent`.  A decomposition element `σ` acts as a ring automorphism
of the residue field, so it permutes the primitive `M`-th roots of unity; hence the exponent `c` with
`σ • ζ = ζ ^ c` is coprime to `M`, i.e. an element of `(ZMod M)ˣ`.  The action on every `M`-th root
of unity `x` is then `σ • x = x ^ c.val`.  This is the unit-valued cyclotomic character at the place,
the local shadow of the cyclotomic action `E →* (ZMod M)ˣ` carried by the branch data. -/
theorem exists_cyclotomic_unit {M : ℕ} [NeZero M] {ζ : ResidueField A}
    (hζ : IsPrimitiveRoot ζ M) (σ : D) :
    ∃ c : (ZMod M)ˣ, ∀ x : ResidueField A, x ^ M = 1 → σ • x = x ^ ((c : ZMod M).val) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  -- `σ •` is injective (it is a group element acting), so it preserves primitivity.
  have hsmul_inj : Function.Injective (fun x : ResidueField A => σ • x) := MulAction.injective σ
  have hpow : (σ • ζ) ^ M = 1 := by rw [← smul_pow', hζ.pow_eq_one, smul_one]
  obtain ⟨c, _, hc⟩ := hζ.eq_pow_of_pow_eq_one hpow
  -- `σ • ζ = ζ ^ c` is again a primitive `M`-th root of unity, so `c` is coprime to `M`.
  have hprim : IsPrimitiveRoot (σ • ζ) M := by
    refine ⟨hpow, fun l hl => ?_⟩
    refine hζ.dvd_of_pow_eq_one l (hsmul_inj ?_)
    show σ • ζ ^ l = σ • (1 : ResidueField A)
    rw [smul_pow', smul_one]; exact hl
  rw [← hc] at hprim
  have hcop : Nat.Coprime c M := (hζ.pow_iff_coprime hM c).mp hprim
  -- reduction mod `M` is harmless on `M`-th roots of unity
  have hred : ∀ (y : ResidueField A) (n : ℕ), y ^ M = 1 → y ^ ((n : ZMod M).val) = y ^ n := by
    intro y n hy
    rw [ZMod.val_natCast]
    conv_rhs => rw [← Nat.div_add_mod n M, pow_add, pow_mul, hy, one_pow, one_mul]
  refine ⟨ZMod.unitOfCoprime c hcop, fun x hx => ?_⟩
  rw [ZMod.coe_unitOfCoprime, hred x c hx]
  -- back to `exists_cyclotomic_exponent`'s computation: `σ • x = x ^ c`
  obtain ⟨j, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [smul_pow', ← hc, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **Fried's branch-cycle formula, with the cyclotomic exponent as a unit of `ZMod M`.**

The unit-valued refinement of `conj_eq_pow_cyclotomic_of_θInjective`: when the tame character is
injective and the residue field contains a primitive `M`-th root of unity `ζ`, conjugation of an
inertia element `g` (with `θ (g)` an `M`-th root of unity) by a decomposition element `σ` raises `g`
to `g ^ c.val`, where `c : (ZMod M)ˣ` is the cyclotomic unit by which `σ` acts on the `M`-th roots of
unity.  This is the shape the branch data consumes: the exponent is a unit, so automatically coprime
to `M`. -/
theorem conj_eq_pow_cyclotomicUnit_of_θInjective {π : A} (hπ : Irreducible π)
    (hinj : Function.Injective (θHom K A hπ)) {M : ℕ} [NeZero M] {ζ : ResidueField A}
    (hζ : IsPrimitiveRoot ζ M) (σ : D) (g : I) (hgM : (θHom K A hπ g) ^ M = 1) :
    ∃ c : (ZMod M)ˣ,
      (⟨σ * (g : D) * σ⁻¹, conj_mem_inertia K A σ g⟩ : I) = g ^ ((c : ZMod M).val) := by
  obtain ⟨c, hc⟩ := exists_cyclotomic_unit K A hζ σ
  refine ⟨c, conj_eq_pow_of_θInjective K A hπ hinj σ g ((c : ZMod M).val) (hc _ ?_)⟩
  rw [← Units.val_pow_eq_pow_val, hgM, Units.val_one]

end TameCharacter
