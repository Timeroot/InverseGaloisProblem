/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Cup
import InverseGalois.CFT.Profinite.KummerHom
import InverseGalois.CFT.Profinite.KummerRes
import InverseGalois.CFT.Profinite.KummerTwo

/-!
# The `n`-th power symbol

Two units of a base field containing a primitive `n`-th root of unity have Kummer classes in the
first cohomology of the Galois group with coefficients in the `n`-th roots of unity, and a pairing
of the roots of unity with themselves multiplies those classes into the second cohomology.  The
result is bimultiplicative in the two units, trivial on `n`-th powers, killed by `n`, and
compatible with restriction to a subgroup, which is the localization of the symbol at a place.
Read in the units of the extension it becomes a class of the Brauer group of the base, and nothing
is lost, because the second cohomology of the roots of unity injects there.

The pairing is not canonical: it amounts to the choice of a primitive root.  The residues modulo
`n`, with their ring multiplication read multiplicatively, are the concrete model, and they are
Kummer data for any base containing a primitive `n`-th root of unity.

## Main definitions

* `InverseGalois.CFT.mulZMod`: the multiplication of the residues modulo `n`, read
  multiplicatively.
* `InverseGalois.CFT.zmodRootHom`: the residues modulo `n`, as the `n`-th roots of unity of a
  field containing a primitive one.
* `InverseGalois.CFT.kummerSymbol`: **the `n`-th power symbol of two units of the base.**
* `InverseGalois.CFT.kummerSymbolUnits`: the symbol read in the units of the extension.

## Main results

* `InverseGalois.CFT.isKummerData_zmod`: **the residues modulo `n` are Kummer data.**
* `InverseGalois.CFT.pow_kummerSymbol_eq_one`: the symbol is killed by `n`.
* `InverseGalois.CFT.kummerSymbol_eq_one_of_isPow_left`: the symbol is trivial on `n`-th powers.
* `InverseGalois.CFT.resH2_kummerSymbol`: **the symbol commutes with restriction to a subgroup.**
* `InverseGalois.CFT.kummerSymbolUnits_eq_one_iff`: **reading the symbol in the units of the
  extension loses nothing.**

## Tags

Hilbert symbol, norm residue symbol, Kummer theory, cup product, Galois cohomology, Brauer group
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### Powers of an element killed by an exponent -/

section Pow

/-- A power of an element killed by `n` depends only on the exponent modulo `n`. -/
theorem pow_mod_of_pow_eq_one {A : Type*} [Monoid A] {u : A} {n : ℕ} (hu : u ^ n = 1) (i : ℕ) :
    u ^ (i % n) = u ^ i := by
  conv_rhs => rw [← Nat.div_add_mod i n]
  rw [pow_add, pow_mul, hu, one_pow, one_mul]

end Pow

/-! ### The residues modulo `n`, multiplied -/

section ZMod

variable (n : ℕ)

/-- **The multiplication of the residues modulo `n`, read multiplicatively.**  This is the pairing
of the `n`-th roots of unity with themselves that a choice of primitive root produces. -/
def mulZMod : Multiplicative (ZMod n) →* Multiplicative (ZMod n) →* Multiplicative (ZMod n) where
  toFun a :=
    { toFun := fun b => Multiplicative.ofAdd (a.toAdd * b.toAdd)
      map_one' := by
        show Multiplicative.ofAdd (a.toAdd * (0 : ZMod n)) = 1
        rw [mul_zero]
        rfl
      map_mul' := fun b c => by
        show Multiplicative.ofAdd (a.toAdd * (b.toAdd + c.toAdd)) = _
        rw [mul_add]
        rfl }
  map_one' := by
    refine MonoidHom.ext fun b => ?_
    show Multiplicative.ofAdd ((0 : ZMod n) * b.toAdd) = 1
    rw [zero_mul]
    rfl
  map_mul' a a' := by
    refine MonoidHom.ext fun b => ?_
    show Multiplicative.ofAdd ((a.toAdd + a'.toAdd) * b.toAdd) = _
    rw [add_mul]
    rfl

@[simp]
theorem mulZMod_apply (a b : Multiplicative (ZMod n)) :
    mulZMod n a b = Multiplicative.ofAdd (a.toAdd * b.toAdd) := rfl

end ZMod

/-! ### The residues modulo `n` as the roots of unity of the base -/

section ZModRoots

variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {ζ : k}

/-- A primitive `n`-th root of unity of a field, as a unit. -/
noncomputable def primitiveRootUnit (hζ : IsPrimitiveRoot ζ n) : kˣ :=
  (hζ.isUnit (NeZero.ne n)).unit

/-- The unit attached to a primitive root of unity is a primitive root of unity. -/
theorem isPrimitiveRoot_primitiveRootUnit (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (primitiveRootUnit hζ) n := hζ.isUnit_unit (NeZero.ne n)

/-- **The residues modulo `n`, read as the `n`-th roots of unity of a field containing a primitive
one.** -/
noncomputable def zmodRootHom (hζ : IsPrimitiveRoot ζ n) : Multiplicative (ZMod n) →* kˣ where
  toFun a := primitiveRootUnit hζ ^ a.toAdd.val
  map_one' := by
    show primitiveRootUnit hζ ^ (0 : ZMod n).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' a b := by
    show primitiveRootUnit hζ ^ (a.toAdd + b.toAdd).val = _
    rw [ZMod.val_add, pow_mod_of_pow_eq_one (isPrimitiveRoot_primitiveRootUnit hζ).pow_eq_one,
      pow_add]

theorem zmodRootHom_apply (hζ : IsPrimitiveRoot ζ n) (a : Multiplicative (ZMod n)) :
    zmodRootHom hζ a = primitiveRootUnit hζ ^ a.toAdd.val := rfl

/-- The residues modulo `n` inject into the units of the field. -/
theorem injective_zmodRootHom (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (zmodRootHom hζ) := by
  intro a b hab
  have hval : a.toAdd.val = b.toAdd.val :=
    (isPrimitiveRoot_primitiveRootUnit hζ).pow_inj (ZMod.val_lt a.toAdd) (ZMod.val_lt b.toAdd) hab
  exact Multiplicative.ext (ZMod.val_injective n hval)

/-- The image of the residues modulo `n` consists of `n`-th roots of unity. -/
theorem zmodRootHom_pow_eq_one (hζ : IsPrimitiveRoot ζ n) (a : Multiplicative (ZMod n)) :
    zmodRootHom hζ a ^ n = 1 := by
  rw [zmodRootHom_apply, ← pow_mul, mul_comm, pow_mul,
    (isPrimitiveRoot_primitiveRootUnit hζ).pow_eq_one, one_pow]

/-- **Every `n`-th root of unity of the field is a residue modulo `n`.** -/
theorem exists_zmodRootHom_eq (hζ : IsPrimitiveRoot ζ n) (y : kˣ) (hy : y ^ n = 1) :
    ∃ a : Multiplicative (ZMod n), zmodRootHom hζ a = y := by
  have hyval : ((y : k)) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]
  have hcoe : ((primitiveRootUnit hζ : kˣ) : k) = ζ := IsUnit.unit_spec _
  obtain ⟨i, hi, hival⟩ := hζ.eq_pow_of_pow_eq_one hyval
  refine ⟨Multiplicative.ofAdd (i : ZMod n), ?_⟩
  have hv : ((i : ZMod n)).val = i := ZMod.val_cast_of_lt hi
  rw [zmodRootHom_apply]
  refine Units.ext ?_
  show ((primitiveRootUnit hζ ^ (Multiplicative.ofAdd (i : ZMod n)).toAdd.val : kˣ) : k) = (y : k)
  rw [Units.val_pow_eq_pow_val, hcoe]
  show ζ ^ ((i : ZMod n)).val = (y : k)
  rw [hv, hival]

end ZModRoots

/-! ### The residues modulo `n` are Kummer data -/

section ZModData

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {n : ℕ} [NeZero n]

variable (k Ω n) in
/-- The trivial action of the Galois group on the residues modulo `n`. -/
def zmodTrivialAction : MulDistribMulAction Gal(Ω/k) (Multiplicative (ZMod n)) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

/-- **The residues modulo `n` are Kummer data** for a base containing a primitive `n`-th root of
unity whose units all have an `n`-th root in the extension. -/
theorem isKummerData_zmod {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (hroot : ∀ a : kˣ, ∃ β : Ωˣ, β ^ n = Units.map (algebraMap k Ω : k →* Ω) a) :
    letI := zmodTrivialAction k Ω n
    IsKummerData k Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n := by
  letI := zmodTrivialAction k Ω n
  exact
    { exists_isPrimitiveRoot := ⟨ζ, hζ⟩
      smul_eq := fun _ _ => rfl
      injective := injective_zmodRootHom hζ
      pow_eq_one := zmodRootHom_pow_eq_one hζ
      exists_ι_eq := exists_zmodRootHom_eq hζ
      exists_root := hroot }

end ZModData

/-! ### The symbol -/

section Symbol

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M] {ι : M →* kˣ} {n : ℕ}
variable [NeZero n] [IsSmoothAction Gal(Ω/k) M]

omit [IsGalois k Ω] [NeZero n] [IsSmoothAction Gal(Ω/k) M] in
/-- For a trivial action every pairing of the coefficients is equivariant. -/
theorem IsKummerData.equivariant (h : IsKummerData k Ω M ι n) (Φ : M →* M →* M)
    (g : Gal(Ω/k)) (m m' : M) : Φ (g • m) (g • m') = g • Φ m m' := by
  rw [h.smul_eq, h.smul_eq, h.smul_eq]

variable (h : IsKummerData k Ω M ι n) (Φ : M →* M →* M)

/-- **The `n`-th power symbol of two units of the base**: the cup product of their Kummer classes
along a pairing of the `n`-th roots of unity with themselves. -/
noncomputable def kummerSymbol : kˣ →* kˣ →* SmoothH2 Gal(Ω/k) M where
  toFun a := (cupSmoothH1 Φ (h.equivariant Φ) (h.kummerHom a)).comp h.kummerHom
  map_one' := by rw [map_one, map_one, MonoidHom.one_comp]
  map_mul' a b := by rw [map_mul, map_mul, MonoidHom.mul_comp]

theorem kummerSymbol_apply (a b : kˣ) :
    kummerSymbol h Φ a b = cupSmoothH1 Φ (h.equivariant Φ) (h.kummerHom a) (h.kummerHom b) := rfl

/-- The symbol of an `n`-th power is trivial in the first argument. -/
theorem kummerSymbol_eq_one_of_isPow_left {a : kˣ} (ha : ∃ c : kˣ, c ^ n = a) (b : kˣ) :
    kummerSymbol h Φ a b = 1 := by
  have hka : h.kummerHom a = 1 := (h.kummerClass_eq_one_iff a).2 ha
  rw [kummerSymbol_apply, hka, map_one, MonoidHom.one_apply]

/-- The symbol of an `n`-th power is trivial in the second argument. -/
theorem kummerSymbol_eq_one_of_isPow_right (a : kˣ) {b : kˣ} (hb : ∃ c : kˣ, c ^ n = b) :
    kummerSymbol h Φ a b = 1 := by
  have hkb : h.kummerHom b = 1 := (h.kummerClass_eq_one_iff b).2 hb
  rw [kummerSymbol_apply, hkb, map_one]

/-- **The symbol commutes with restriction to a subgroup**, which is its localization at a
place. -/
theorem resH2_kummerSymbol (H : Subgroup Gal(Ω/k)) (a b : kˣ) :
    resH2 H (kummerSymbol h Φ a b)
      = cupSmoothH1 (G := ↥H) Φ (fun g m m' => h.equivariant Φ (g : Gal(Ω/k)) m m')
          (resH1 H (h.kummerHom a)) (resH1 H (h.kummerHom b)) := by
  rw [kummerSymbol_apply, resH2_cupSmoothH1]

/-- **A symbol one of whose arguments is a local `n`-th power everywhere is everywhere locally
trivial.** -/
theorem kummerSymbol_mem_sha2_left {S : Set (Subgroup Gal(Ω/k))} {a : kˣ}
    (ha : a ∈ h.localPowers S) (b : kˣ) : kummerSymbol h Φ a b ∈ sha2 M S := by
  refine mem_sha2.2 fun D hD => ?_
  have hka : resH1 D (h.kummerHom a) = 1 :=
    (h.resH1_kummerClass_eq_one_iff a D).2 ((h.mem_localPowers_iff S a).1 ha D hD)
  rw [resH2_kummerSymbol, hka, map_one, MonoidHom.one_apply]

/-- **A symbol one of whose arguments is a local `n`-th power everywhere is everywhere locally
trivial.** -/
theorem kummerSymbol_mem_sha2_right {S : Set (Subgroup Gal(Ω/k))} (a : kˣ) {b : kˣ}
    (hb : b ∈ h.localPowers S) : kummerSymbol h Φ a b ∈ sha2 M S := by
  refine mem_sha2.2 fun D hD => ?_
  have hkb : resH1 D (h.kummerHom b) = 1 :=
    (h.resH1_kummerClass_eq_one_iff b D).2 ((h.mem_localPowers_iff S b).1 hb D hD)
  rw [resH2_kummerSymbol, hkb, map_one]

end Symbol

/-! ### The symbol is killed by the exponent -/

section Torsion

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*} [CommGroup M]
  [MulDistribMulAction G M] {n : ℕ}

/-- The second cohomology of coefficients killed by `n` is killed by `n`. -/
theorem smoothH2_pow_eq_one (hpow : ∀ m : M, m ^ n = 1) (z : SmoothH2 G M) : z ^ n = 1 := by
  obtain ⟨a, ha, has, rfl⟩ := smoothH2Mk_surjective z
  rw [← smoothH2Mk_pow ha has n, smoothH2Mk_eq_one_iff]
  exact ⟨1, isSmooth₁_one, by rw [coboundary₂_one]; exact (funext fun p => hpow (a p)).symm⟩

end Torsion

/-! ### The coefficients, read in the units of the extension -/

section UnitsHom

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M] {ι : M →* kˣ} {n : ℕ}
variable [NeZero n]

/-- The coefficients of a Kummer situation, read in the units of the extension. -/
def IsKummerData.unitsHom (_h : IsKummerData k Ω M ι n) : M →* Ωˣ :=
  (Units.map (algebraMap k Ω : k →* Ω)).comp ι

variable (h : IsKummerData k Ω M ι n)

omit [NeZero n] in
theorem IsKummerData.unitsHom_apply (m : M) :
    h.unitsHom m = Units.map (algebraMap k Ω : k →* Ω) (ι m) := rfl

omit [NeZero n] in
/-- The coefficients land in the units of the base, which the Galois group fixes. -/
theorem IsKummerData.unitsHom_equivariant (g : Gal(Ω/k)) (m : M) :
    h.unitsHom (g • m) = g • h.unitsHom m := by
  rw [h.unitsHom_apply, h.unitsHom_apply, h.smul_eq, smul_units_algebraMap]

omit [NeZero n] in
/-- The coefficients inject into the units of the extension. -/
theorem IsKummerData.injective_unitsHom : Function.Injective h.unitsHom :=
  injective_units_algebraMap_comp (Ω := Ω) h.injective

omit [NeZero n] in
/-- The coefficients are `n`-th roots of unity in the extension. -/
theorem IsKummerData.unitsHom_pow_eq_one (m : M) : h.unitsHom m ^ n = 1 := by
  rw [h.unitsHom_apply, ← map_pow, h.pow_eq_one, map_one]

/-- **Every `n`-th root of unity of the extension comes from the coefficients**, the base
containing a primitive `n`-th root of unity. -/
theorem IsKummerData.exists_unitsHom_eq (y : Ωˣ) (hy : y ^ n = 1) : ∃ m : M, h.unitsHom m = y :=
  exists_ι_eq_of_pow_eq_one h.isPrimitiveRoot_primitiveRoot h.exists_ι_eq hy

end UnitsHom

/-! ### The symbol in the units of the extension -/

section Units

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M] {ι : M →* kˣ} {n : ℕ}
variable [NeZero n] [IsSmoothAction Gal(Ω/k) M]
variable (h : IsKummerData k Ω M ι n) (Φ : M →* M →* M)

/-- The symbol is killed by `n`. -/
theorem pow_kummerSymbol_eq_one (a b : kˣ) : kummerSymbol h Φ a b ^ n = 1 :=
  smoothH2_pow_eq_one (fun m => h.injective (by rw [map_pow, h.pow_eq_one, map_one])) _

/-- **The `n`-th power symbol read in the units of the extension**, that is, as a class of the
Brauer group of the base. -/
noncomputable def kummerSymbolUnits : kˣ →* kˣ →* SmoothH2 Gal(Ω/k) Ωˣ where
  toFun a := (coeffH2 h.unitsHom h.unitsHom_equivariant).comp (kummerSymbol h Φ a)
  map_one' := by rw [map_one, MonoidHom.comp_one]
  map_mul' a b := MonoidHom.ext fun c => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, map_mul, MonoidHom.mul_apply]

theorem kummerSymbolUnits_apply (a b : kˣ) :
    kummerSymbolUnits h Φ a b
      = coeffH2 h.unitsHom h.unitsHom_equivariant (kummerSymbol h Φ a b) := rfl

/-- **Reading the symbol in the units of the extension loses nothing**, the second cohomology of
the `n`-th roots of unity injecting into that of the units. -/
theorem kummerSymbolUnits_eq_one_iff (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ n = y) (a b : kˣ) :
    kummerSymbolUnits h Φ a b = 1 ↔ kummerSymbol h Φ a b = 1 := by
  rw [kummerSymbolUnits_apply]
  constructor
  · intro hz
    refine coeffH2_injective h.unitsHom_equivariant h.injective_unitsHom h.unitsHom_pow_eq_one
      h.exists_unitsHom_eq hroot ?_
    rw [hz, map_one]
  · intro hz
    rw [hz, map_one]

end Units

end InverseGalois.CFT
