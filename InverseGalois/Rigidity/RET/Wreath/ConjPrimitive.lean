/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A transcendental primitive element and its conjugates

Fix a tower `k ⊆ B ⊆ F` of fields with `F / B` finite Galois.  One thinks of `k` as a field of
constants, of `B` as a field of functions on a base — a rational function field, say — and of `F`
as the function field of a cover of that base; the group `F ≃ₐ[B] F` is then the deck group of the
cover.  A finite Galois extension is separable, so `F` is generated over `B` by a single element,
but a bare primitive element is not quite enough for constructions that read the cover through the
values of a function: one also wants the generator to be a genuine function rather than a constant,
that is, transcendental over `k`.  This is free as soon as the base itself contains one
transcendental element `x`.  Indeed, if a primitive element happens to be algebraic over `k`, then
adding `x` to it produces another generator — `x` already lies in the base, so adjoining the sum
adjoins the original element — and the sum of an element algebraic over `k` with one transcendental
over `k` is transcendental over `k`.

Once a generator `θ` is fixed, the group `F ≃ₐ[B] F` is faithfully visible in it.  An automorphism
fixing `θ` fixes the field `θ` generates, which is all of `F`, so it is the identity; consequently
distinct automorphisms carry `θ` to distinct elements, and the orbit of `θ` consists of as many
distinct elements as there are automorphisms, each of them transcendental over `k` because an
automorphism over `B` is in particular an isomorphism of fields over `k`.

The point of all this is the final non-vanishing statement.  In characteristic zero, any two
distinct conjugates of `θ` differ by an element that is not a constant.  The mechanism is a
counting argument on a single automorphism: if `g θ = θ + a` with `a` a constant, then iterating
gives `gᵐ θ = θ + m·a`, and taking `m` to be the order of `g` returns `θ` to itself and forces
`m·a = 0`, hence `a = 0`.  The two-automorphism version follows by writing `g θ - h θ` as the image
under `h` of `u θ - θ` with `u = h⁻¹g`, an automorphism that genuinely moves `θ`; the transported
statement is the one wanted, because `h` fixes the constants.  Read on a curve, where a nonzero
element of the function field has only finitely many zeros and poles, this is exactly what bounds
the places at which the conjugates of `θ` can collide with each other or with a prescribed finite
set of constants.

## Main results

* `Rigidity.RET.Wreath.exists_transcendental_primitive` — a finite Galois extension of a base
  containing a transcendental element has a primitive element transcendental over the constants.
* `Rigidity.RET.Wreath.eq_one_of_apply_eq` — an automorphism fixing a primitive element is the
  identity.
* `Rigidity.RET.Wreath.apply_ne_apply` — distinct automorphisms move a primitive element to
  distinct elements.
* `Rigidity.RET.Wreath.transcendental_apply` — the conjugates of a transcendental element are
  transcendental.
* `Rigidity.RET.Wreath.sub_const_conj_ne_zero` — an automorphism never moves an element by a
  nonzero constant amount.
* `Rigidity.RET.Wreath.sub_conj_sub_const_ne_zero` — the difference of two distinct conjugates of a
  primitive element misses every constant.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Wreath

variable {k B F : Type*} [Field k] [Field B] [Field F]
  [Algebra k B] [Algebra B F] [Algebra k F] [IsScalarTower k B F]

/-! ## Constants and the automorphism group -/

/-- **An automorphism over the base fixes the constants**, because the constants reach the top
field through the base. -/
theorem map_const (g : F ≃ₐ[B] F) (a : k) : g (algebraMap k F a) = algebraMap k F a := by
  rw [IsScalarTower.algebraMap_apply k B F]
  exact g.commutes _

/-- **A transcendental element of the base stays transcendental in the extension**: the extension
is a faithful field extension of the base, and it inherits the constants through it. -/
theorem transcendental_algebraMap {x : B} (hx : Transcendental k x) :
    Transcendental k (algebraMap B F x) := by
  intro halg
  exact hx ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom k B F)
    (algebraMap B F).injective).mp halg)

/-- **An element fixed by an automorphism lies in the field fixed by the subgroup it
generates.** -/
theorem mem_fixedField_of_apply_eq {g : F ≃ₐ[B] F} {θ : F} (hg : g θ = θ) :
    θ ∈ IntermediateField.fixedField (Subgroup.closure ({g} : Set (F ≃ₐ[B] F))) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro y hy
  have hle : Subgroup.closure ({g} : Set (F ≃ₐ[B] F)) ≤
      MulAction.stabilizer (F ≃ₐ[B] F) θ := by
    rw [Subgroup.closure_le]
    rintro z rfl
    exact hg
  exact hle hy

/-! ## A transcendental primitive element -/

/-- **A finite Galois extension of a base with a transcendental element has a transcendental
primitive element.**  A finite Galois extension is separable, hence simple; and if the generator
produced happens to be algebraic over the constants, translating it by a transcendental element of
the base yields another generator, one that is transcendental because otherwise the translating
element itself would be algebraic over the constants. -/
theorem exists_transcendental_primitive [FiniteDimensional B F] [IsGalois B F]
    (x : B) (hx : Transcendental k x) :
    ∃ θ : F, IntermediateField.adjoin B {θ} = ⊤ ∧ Transcendental k θ := by
  obtain ⟨θ₀, hθ₀⟩ := Field.exists_primitive_element B F
  have hX : Transcendental k (algebraMap B F x) := transcendental_algebraMap hx
  by_cases hcase : Transcendental k θ₀
  · exact ⟨θ₀, hθ₀, hcase⟩
  · have hmem : θ₀ ∈ IntermediateField.adjoin B ({θ₀ + algebraMap B F x} : Set F) := by
      have h1 : θ₀ + algebraMap B F x ∈
          IntermediateField.adjoin B ({θ₀ + algebraMap B F x} : Set F) :=
        IntermediateField.mem_adjoin_simple_self _ _
      have h2 : algebraMap B F x ∈
          IntermediateField.adjoin B ({θ₀ + algebraMap B F x} : Set F) :=
        IntermediateField.algebraMap_mem _ _
      simpa using sub_mem h1 h2
    refine ⟨θ₀ + algebraMap B F x, ?_, fun halg => ?_⟩
    · rw [eq_top_iff, ← hθ₀, IntermediateField.adjoin_le_iff]
      rintro y rfl
      exact hmem
    · refine hX ?_
      have h1 : θ₀ ∈ algebraicClosure k F := mem_algebraicClosure_iff.mpr (not_not.mp hcase)
      have h2 : θ₀ + algebraMap B F x ∈ algebraicClosure k F :=
        mem_algebraicClosure_iff.mpr halg
      have h3 : algebraMap B F x ∈ algebraicClosure k F := by simpa using sub_mem h2 h1
      exact mem_algebraicClosure_iff.mp h3

/-! ## The automorphism group seen through a primitive element -/

/-- **An automorphism fixing a primitive element is the identity.**  The elements it fixes form an
intermediate field containing the generator, hence all of the extension. -/
theorem eq_one_of_apply_eq {θ : F} (hprim : IntermediateField.adjoin B {θ} = ⊤)
    {g : F ≃ₐ[B] F} (hg : g θ = θ) : g = 1 := by
  have hfix : (⊤ : IntermediateField B F) ≤
      IntermediateField.fixedField (Subgroup.closure ({g} : Set (F ≃ₐ[B] F))) := by
    rw [← hprim, IntermediateField.adjoin_le_iff]
    rintro y rfl
    exact mem_fixedField_of_apply_eq hg
  refine AlgEquiv.ext fun y => ?_
  rw [AlgEquiv.one_apply]
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hfix IntermediateField.mem_top) g
    (Subgroup.subset_closure rfl)

/-- **Distinct automorphisms move a primitive element to distinct elements**: if two of them agreed
on the generator, their quotient would fix it. -/
theorem apply_ne_apply {θ : F} (hprim : IntermediateField.adjoin B {θ} = ⊤)
    {g h : F ≃ₐ[B] F} (hgh : g ≠ h) : g θ ≠ h θ := by
  intro heq
  refine hgh ?_
  have hfix : (h⁻¹ * g) θ = θ := by
    rw [AlgEquiv.mul_apply, heq]
    exact h.symm_apply_apply θ
  exact (inv_mul_eq_one.mp (eq_one_of_apply_eq hprim hfix)).symm

/-- **The conjugates of a transcendental element are transcendental.**  An automorphism over the
base is in particular an automorphism over the constants, and an isomorphism of fields over the
constants preserves algebraicity in both directions. -/
theorem transcendental_apply {θ : F} (hθ : Transcendental k θ) (g : F ≃ₐ[B] F) :
    Transcendental k (g θ) := by
  intro halg
  refine hθ ?_
  have hinj : Function.Injective ⇑(AlgEquiv.restrictScalars k g : F →ₐ[k] F) :=
    (AlgEquiv.restrictScalars k g).injective
  exact (isAlgebraic_algHom_iff (AlgEquiv.restrictScalars k g : F →ₐ[k] F) hinj).mp halg

/-! ## An automorphism never shifts by a constant -/

/-- **Iterating an automorphism that shifts an element by a constant shifts it by a multiple** of
that constant, since the automorphism fixes the constant it shifts by. -/
theorem pow_apply_of_sub_eq_const {θ : F} {g : F ≃ₐ[B] F} {a : k}
    (hgθ : g θ = θ + algebraMap k F a) (m : ℕ) :
    (g ^ m) θ = θ + algebraMap k F (m • a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, AlgEquiv.mul_apply, hgθ, map_add, ih, map_const, succ_nsmul, map_add, add_assoc]

/-- **An automorphism moves an element by a non-constant amount.**  A shift by a constant is
multiplied by the order of the automorphism when it is iterated back to the identity, so in
characteristic zero the shift is zero. -/
theorem sub_conj_ne_const [FiniteDimensional B F] [CharZero F] {θ : F} {g : F ≃ₐ[B] F}
    (hg : g θ ≠ θ) (a : k) : g θ - θ ≠ algebraMap k F a := by
  intro hc
  have hgθ : g θ = θ + algebraMap k F a := by rw [← hc]; ring
  have hord : 0 < orderOf g := orderOf_pos g
  have hfix : (g ^ orderOf g) θ = θ := by rw [pow_orderOf_eq_one]; simp
  rw [pow_apply_of_sub_eq_const hgθ] at hfix
  have hzero : algebraMap k F (orderOf g • a) = 0 := by linear_combination hfix
  rw [map_nsmul, nsmul_eq_mul] at hzero
  have hne : ((orderOf g : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr hord.ne'
  have ha : algebraMap k F a = 0 := (mul_eq_zero.mp hzero).resolve_left hne
  exact hg (by rw [hgθ, ha, add_zero])

/-- **An automorphism moves an element by an amount avoiding every constant.**  This is the
non-vanishing that bounds, by the finiteness of the zeros and poles of a nonzero function, the
places at which a conjugate can collide with a prescribed constant. -/
theorem sub_const_conj_ne_zero [FiniteDimensional B F] [CharZero F] {θ : F} {g : F ≃ₐ[B] F}
    (hg : g θ ≠ θ) (a : k) : g θ - θ - algebraMap k F a ≠ 0 :=
  fun h => sub_conj_ne_const hg a (by linear_combination h)

/-! ## Distinct conjugates never differ by a constant -/

/-- **The difference of two distinct conjugates of a primitive element misses every constant.**
Transporting by the inverse of one of the two automorphisms, which fixes the constants, reduces the
statement to the fact that a single automorphism never moves an element by a constant amount. -/
theorem sub_conj_sub_const_ne_zero [FiniteDimensional B F] [CharZero F] {θ : F}
    (hprim : IntermediateField.adjoin B {θ} = ⊤) {g h : F ≃ₐ[B] F} (hgh : g ≠ h) (a : k) :
    g θ - h θ - algebraMap k F a ≠ 0 := by
  have huθ : (h⁻¹ * g) θ ≠ θ := by
    intro hfix
    exact hgh (inv_mul_eq_one.mp (eq_one_of_apply_eq hprim hfix)).symm
  have hne := sub_const_conj_ne_zero huθ a
  intro hzero
  refine hne ?_
  have hmap : (h⁻¹ : F ≃ₐ[B] F) (g θ - h θ - algebraMap k F a) = (h⁻¹ : F ≃ₐ[B] F) 0 := by
    rw [hzero]
  rw [map_sub, map_sub, map_zero, map_const] at hmap
  have h1 : (h⁻¹ : F ≃ₐ[B] F) (g θ) = (h⁻¹ * g) θ := (AlgEquiv.mul_apply h⁻¹ g θ).symm
  have h2 : (h⁻¹ : F ≃ₐ[B] F) (h θ) = θ := h.symm_apply_apply θ
  rw [h1, h2] at hmap
  exact hmap

end Rigidity.RET.Wreath
