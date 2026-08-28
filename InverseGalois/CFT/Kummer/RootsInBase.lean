/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Roots of unity already present in the base field

A field containing a primitive `n`-th root of unity already contains every `n`-th root of unity of
every extension: the polynomial `X ^ n - 1` has its full complement of `n` roots in the base, and a
field extension cannot produce more.  Consequently the Galois group of an extension acts trivially
on the `n`-th roots of unity of the top field, and a cyclic group of order `n` embeds onto them.

This is the bookkeeping that lets a cochain of `n`-th roots of unity, produced over a large
extension by Kummer theory, be read as a cochain with values in the kernel of a central extension
of order `n`.

## Main results

* `InverseGalois.CFT.exists_algebraMap_eq_of_pow_eq_one`: **an `n`-th root of unity of an extension
  of a field containing a primitive `n`-th root of unity comes from the base field.**
* `InverseGalois.CFT.exists_units_algebraMap_eq_of_pow_eq_one`: the same statement for units.
* `InverseGalois.CFT.smul_eq_self_of_pow_eq_one`: the Galois group of such an extension fixes every
  `n`-th root of unity.
* `InverseGalois.CFT.exists_monoidHom_units_of_card`: **a cyclic group of order `n` embeds onto the
  group of `n`-th roots of unity of a field containing a primitive one.**
* `InverseGalois.CFT.exists_fun_eq_of_pow_eq_one`: a family of `n`-th roots of unity of an extension
  is the image of a family of elements of such a cyclic group.

## Tags

roots of unity, primitive root, Kummer theory, cyclic group, Galois action
-/

namespace InverseGalois.CFT

section Descend

variable {k M : Type*} [Field k] [Field M] [Algebra k M]

/-- **An `n`-th root of unity of an extension of a field containing a primitive `n`-th root of
unity comes from the base field.**  The image of the primitive root is still primitive, so every
`n`-th root of unity upstairs is one of its powers. -/
theorem exists_algebraMap_eq_of_pow_eq_one {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    {x : M} (hx : x ^ n = 1) : ∃ y : k, y ^ n = 1 ∧ algebraMap k M y = x := by
  obtain ⟨i, -, hi⟩ := (hζ.map_of_injective (algebraMap k M).injective).eq_pow_of_pow_eq_one hx
  refine ⟨ζ ^ i, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [map_pow]; exact hi

/-- **An `n`-th root of unity in the units of an extension of a field containing a primitive `n`-th
root of unity comes from the units of the base field.** -/
theorem exists_units_algebraMap_eq_of_pow_eq_one {n : ℕ} [NeZero n] {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) {x : Mˣ} (hx : x ^ n = 1) :
    ∃ y : kˣ, y ^ n = 1 ∧ Units.map (algebraMap k M : k →* M) y = x := by
  obtain ⟨y, hy, hyx⟩ := exists_algebraMap_eq_of_pow_eq_one hζ
    (x := (x : M)) (by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one])
  refine ⟨(IsUnit.of_pow_eq_one hy (NeZero.ne n)).unit, ?_, ?_⟩
  · exact Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hy, Units.val_one])
  · exact Units.ext (by rw [Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec, hyx])

/-- **The Galois group of an extension of a field containing a primitive `n`-th root of unity fixes
every `n`-th root of unity.**  Such a root already lies in the base field, which the Galois group
fixes pointwise. -/
theorem smul_eq_self_of_pow_eq_one {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (g : Gal(M/k)) {x : Mˣ} (hx : x ^ n = 1) : g • x = x := by
  obtain ⟨y, -, rfl⟩ := exists_units_algebraMap_eq_of_pow_eq_one hζ hx
  refine Units.ext ?_
  show g (algebraMap k M (y : k)) = algebraMap k M (y : k)
  exact g.commutes _

end Descend

section Cyclic

variable {k : Type*} [Field k]

/-- **A cyclic group of order `n` embeds onto the group of `n`-th roots of unity of a field
containing a primitive `n`-th root of unity.**  Both groups are cyclic of order `n`, so they are
isomorphic, and the roots of unity sit inside the units. -/
theorem exists_monoidHom_units_of_card {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z]
    {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n) (hcard : Nat.card Z = n) :
    ∃ χ : Z →* kˣ, Function.Injective χ ∧ (∀ z : Z, χ z ^ n = 1) ∧
      ∀ y : kˣ, y ^ n = 1 → ∃ z : Z, χ z = y := by
  haveI : IsCyclic ↥(rootsOfUnity n k) := rootsOfUnity.isCyclic k n
  haveI : HasEnoughRootsOfUnity k n := ⟨⟨ζ, hζ⟩, inferInstance⟩
  have hc : Nat.card Z = Nat.card ↥(rootsOfUnity n k) := by
    rw [hcard, HasEnoughRootsOfUnity.natCard_rootsOfUnity]
  set e : Z ≃* ↥(rootsOfUnity n k) := mulEquivOfCyclicCardEq hc with he
  refine ⟨(rootsOfUnity n k).subtype.comp e.toMonoidHom, ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp e.injective
  · intro z
    simpa using (mem_rootsOfUnity n ((e z : kˣ))).mp (e z).2
  · intro y hy
    exact ⟨e.symm ⟨y, (mem_rootsOfUnity n y).mpr hy⟩, by simp⟩

end Cyclic

section Transport

variable {k M : Type*} [Field k] [Field M] [Algebra k M]

/-- **A family of `n`-th roots of unity of an extension is the image of a family of elements of a
group mapping onto the `n`-th roots of unity of the base.** -/
theorem exists_fun_eq_of_pow_eq_one {Z ι : Type*} [Group Z]
    {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    {χ : Z →* kˣ} (hχ : ∀ y : kˣ, y ^ n = 1 → ∃ z : Z, χ z = y)
    (b : ι → Mˣ) (hb : ∀ i, b i ^ n = 1) :
    ∃ c : ι → Z, ∀ i, Units.map (algebraMap k M : k →* M) (χ (c i)) = b i := by
  choose y hy hyb using fun i => exists_units_algebraMap_eq_of_pow_eq_one (M := M) hζ (hb i)
  choose z hz using fun i => hχ (y i) (hy i)
  exact ⟨z, fun i => by rw [hz i, hyb i]⟩

end Transport

end InverseGalois.CFT
