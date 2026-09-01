/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerHom
import InverseGalois.CFT.Profinite.Res

/-!
# Restriction of a Kummer class to a subgroup

The class attached to a unit of the base dies on a subgroup exactly when the unit acquires an
`n`-th root in the field that subgroup fixes.

The cochain of a unit takes the value that measures how far a chosen `n`-th root of the unit is
from being fixed, so on a subgroup it is a coboundary exactly when it vanishes there, the
coefficients carrying only the trivial action.  That happens exactly when the chosen root is fixed
by the subgroup, and since two roots differ by a root of unity of the base one root is fixed
precisely when every root is.  For the subgroup fixing an intermediate field the fixed field is the
field itself, so the condition is that the unit is an `n`-th power there.

Applying this to a family of subgroups describes the everywhere locally trivial classes as the
units that are locally `n`-th powers, modulo the `n`-th powers of the base.

## Main results

* `InverseGalois.CFT.IsKummerData.resH1_kummerClass_eq_one_iff`: **a Kummer class dies on a
  subgroup exactly when the unit has an `n`-th root fixed by that subgroup.**
* `InverseGalois.CFT.IsKummerData.resH1_fixingSubgroup_kummerClass_eq_one_iff`: **a Kummer class
  dies on the subgroup fixing an intermediate field exactly when the unit is an `n`-th power in
  that field.**
* `InverseGalois.CFT.IsKummerData.localPowers`: the units of the base that are `n`-th powers in the
  field fixed by every subgroup of a family.
* `InverseGalois.CFT.IsKummerData.map_localPowers`: **the Kummer homomorphism carries them onto the
  classes that are trivial on every subgroup of the family.**

## Tags

Kummer theory, infinite Galois theory, Galois cohomology, restriction, Tate–Shafarevich group
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open groupCohomology

namespace IsKummerData

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M] {ι : M →* kˣ} {n : ℕ}
variable [NeZero n]

/-! ### The restriction of a Kummer class -/

/-- **A Kummer class dies on a subgroup exactly when the chosen `n`-th root of the unit is fixed by
that subgroup.** -/
theorem resH1_kummerClass_eq_one_iff_smul_root (h : IsKummerData k Ω M ι n) (a : kˣ)
    (D : Subgroup Gal(Ω/k)) :
    resH1 D (h.kummerClass a) = 1 ↔ ∀ d ∈ D, d • h.root a = h.root a := by
  rw [kummerClass, resH1_eq_one_iff]
  constructor
  · rintro ⟨t, ht⟩ d hd
    have h1 : h.cochain a d = 1 := by rw [← ht d hd, h.smul_eq, div_self']
    have hspec := h.cochain_spec a d
    rw [h1, map_one, map_one, eq_comm, div_eq_one] at hspec
    exact hspec
  · intro hfix
    refine ⟨1, fun d hd => ?_⟩
    rw [h.smul_eq, div_self']
    refine injective_units_algebraMap_comp (Ω := Ω) h.injective ?_
    show Units.map (algebraMap k Ω : k →* Ω) (ι 1)
      = Units.map (algebraMap k Ω : k →* Ω) (ι (h.cochain a d))
    rw [map_one, map_one, h.cochain_spec, hfix d hd, div_self']

/-- **A Kummer class dies on a subgroup exactly when the unit has an `n`-th root fixed by that
subgroup.** -/
theorem resH1_kummerClass_eq_one_iff (h : IsKummerData k Ω M ι n) (a : kˣ)
    (D : Subgroup Gal(Ω/k)) :
    resH1 D (h.kummerClass a) = 1 ↔
      ∃ β : Ωˣ, β ^ n = Units.map (algebraMap k Ω : k →* Ω) a ∧ ∀ d ∈ D, d • β = β := by
  rw [h.resH1_kummerClass_eq_one_iff_smul_root a D]
  refine ⟨fun hfix => ⟨h.root a, h.root_pow a, hfix⟩, ?_⟩
  rintro ⟨β, hβ, hβfix⟩ d hd
  have hdiv := smul_div_eq_of_pow_eq h.isPrimitiveRoot_primitiveRoot h.exists_ι_eq
    (β := h.root a) (β' := β) ((h.root_pow a).trans hβ.symm) d
  rw [hβfix d hd, div_self'] at hdiv
  rwa [div_eq_one] at hdiv

/-- **A Kummer class dies on a subgroup exactly when the unit is an `n`-th power in the field that
subgroup fixes.** -/
theorem resH1_kummerClass_eq_one_iff_mem_fixedField (h : IsKummerData k Ω M ι n) (a : kˣ)
    (D : Subgroup Gal(Ω/k)) :
    resH1 D (h.kummerClass a) = 1 ↔
      ∃ b ∈ IntermediateField.fixedField D, b ^ n = algebraMap k Ω (a : k) := by
  rw [h.resH1_kummerClass_eq_one_iff a D]
  constructor
  · rintro ⟨β, hβ, hβfix⟩
    refine ⟨(β : Ω), (IntermediateField.mem_fixedField_iff _ _).2 fun d hd =>
      congrArg (Units.val (α := Ω)) (hβfix d hd), ?_⟩
    have := congrArg (Units.val (α := Ω)) hβ
    rwa [Units.val_pow_eq_pow_val] at this
  · rintro ⟨b, hbmem, hbn⟩
    have hane : ((Units.map (algebraMap k Ω : k →* Ω) a : Ωˣ) : Ω) ≠ 0 := Units.ne_zero _
    have hb0 : b ≠ 0 := by
      intro hb
      rw [hb, zero_pow (NeZero.ne n)] at hbn
      exact hane hbn.symm
    refine ⟨Units.mk0 b hb0, Units.ext ?_, fun d hd => Units.ext ?_⟩
    · rw [Units.val_pow_eq_pow_val, Units.val_mk0, hbn]
      rfl
    · show d b = b
      exact (IntermediateField.mem_fixedField_iff _ _).1 hbmem d hd

/-- **A Kummer class dies on the subgroup fixing an intermediate field exactly when the unit is an
`n`-th power in that field.** -/
theorem resH1_fixingSubgroup_kummerClass_eq_one_iff (h : IsKummerData k Ω M ι n) (a : kˣ)
    (E : IntermediateField k Ω) :
    resH1 E.fixingSubgroup (h.kummerClass a) = 1 ↔
      ∃ b : ↥E, (b : Ω) ^ n = algebraMap k Ω (a : k) := by
  rw [h.resH1_kummerClass_eq_one_iff_mem_fixedField a, InfiniteGalois.fixedField_fixingSubgroup E]
  exact ⟨fun ⟨b, hbmem, hbn⟩ => ⟨⟨b, hbmem⟩, hbn⟩, fun ⟨b, hbn⟩ => ⟨(b : Ω), b.2, hbn⟩⟩

/-! ### The classes that die on a family of subgroups -/

/-- **The units of the base that are `n`-th powers in the field fixed by every subgroup of a
family.**  For the family of decomposition subgroups of the Galois group of a number field these
are the units that are everywhere locally `n`-th powers. -/
noncomputable def localPowers (h : IsKummerData k Ω M ι n) (S : Set (Subgroup Gal(Ω/k))) :
    Subgroup kˣ :=
  (sha1 M S).comap h.kummerHom

/-- Membership in the local powers is an `n`-th root fixed by each subgroup of the family. -/
theorem mem_localPowers_iff (h : IsKummerData k Ω M ι n) (S : Set (Subgroup Gal(Ω/k))) (a : kˣ) :
    a ∈ h.localPowers S ↔ ∀ D ∈ S, ∃ β : Ωˣ,
      β ^ n = Units.map (algebraMap k Ω : k →* Ω) a ∧ ∀ d ∈ D, d • β = β := by
  show h.kummerHom a ∈ sha1 M S ↔ _
  rw [mem_sha1]
  exact forall₂_congr fun D _ => by rw [kummerHom_apply, h.resH1_kummerClass_eq_one_iff]

/-- Membership in the local powers is being an `n`-th power in the field fixed by each subgroup of
the family. -/
theorem mem_localPowers_iff_mem_fixedField (h : IsKummerData k Ω M ι n)
    (S : Set (Subgroup Gal(Ω/k))) (a : kˣ) :
    a ∈ h.localPowers S ↔ ∀ D ∈ S, ∃ b ∈ IntermediateField.fixedField D,
      b ^ n = algebraMap k Ω (a : k) := by
  show h.kummerHom a ∈ sha1 M S ↔ _
  rw [mem_sha1]
  exact forall₂_congr fun D _ => by
    rw [kummerHom_apply, h.resH1_kummerClass_eq_one_iff_mem_fixedField]

/-- The `n`-th powers of the base are local powers. -/
theorem range_pow_le_localPowers (h : IsKummerData k Ω M ι n) (S : Set (Subgroup Gal(Ω/k))) :
    (powMonoidHom n : kˣ →* kˣ).range ≤ h.localPowers S := by
  intro a ha
  rw [← h.ker_kummerHom, MonoidHom.mem_ker] at ha
  show h.kummerHom a ∈ sha1 M S
  rw [ha]
  exact one_mem _

/-- **The Kummer homomorphism carries the local powers onto the classes that are trivial on every
subgroup of the family.** -/
theorem map_localPowers (h : IsKummerData k Ω M ι n) (S : Set (Subgroup Gal(Ω/k))) :
    (h.localPowers S).map h.kummerHom = sha1 M S :=
  Subgroup.map_comap_eq_self_of_surjective h.kummerHom_surjective _

end IsKummerData

end InverseGalois.CFT
