/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.Basic
import InverseGalois.Rigidity.RET.RegularQuotient

/-!
# Functoriality of the regular wreath product

The regular wreath product `D ≀ᵣ Q` is functorial in both arguments, and in both directions it
carries surjections to surjections.  In the first argument this is immediate: a homomorphism
`D₁ →* D₂` acts on the coordinate functions `Q → D₁` pointwise.  In the second argument it is not,
because shrinking the index group `Q` forces the coordinates lying over a single index of the
smaller group to be combined, and the only canonical way to combine them is to multiply them —
which is a homomorphism precisely when `D` is abelian.  The resulting **fibre product**
`fiberProd π a y = ∏ {a x : π x = y}` intertwines the coordinate shift built into the wreath
multiplication with the shift by `π p`, which is exactly what makes `⟨a, p⟩ ↦ ⟨fiberProd π a, π p⟩`
a homomorphism `D ≀ᵣ Q₁ →* D ≀ᵣ Q₂`.

The same fibre product gives a third, less obvious map.  Wreathing by a product `D₁ × D₂` can be
replaced by wreathing twice: there is a surjection

`D₁ ≀ᵣ (D₂ ≀ᵣ Q) ↠ (D₁ × D₂) ≀ᵣ Q`,

obtained by pushing the `D₁`-coordinates, which are indexed by the larger group `D₂ ≀ᵣ Q`, forward
along its projection to `Q`, and reading the `D₂`-coordinates off the second component.  Splitting
a finite abelian group into cyclic factors and iterating, this says that a wreath product by a
finite abelian group is a quotient of an iterated wreath product by cyclic groups, so that a
realization theorem for wreath products only ever has to treat a cyclic bottom group.

Since realizability over `ℚ`, and likewise regular realizability over `ℚ(T)`, is closed under
quotients, each of the three surjections transports a realization.

## Main results

* `RegularWreathProduct.mapLeft` and `RegularWreathProduct.mapLeft_surjective` — functoriality in
  the first argument.
* `RegularWreathProduct.fiberProd` — the fibre product of a family along a homomorphism of index
  groups, with its multiplicativity `fiberProd_mul` and its shift rule `fiberProd_comp_mul_left`.
* `RegularWreathProduct.mapRight` and `RegularWreathProduct.mapRight_surjective` — functoriality in
  the second argument, for an abelian first argument.
* `RegularWreathProduct.regroup` and `RegularWreathProduct.regroup_surjective` — the surjection
  `D₁ ≀ᵣ (D₂ ≀ᵣ Q) ↠ (D₁ × D₂) ≀ᵣ Q`.
* `IsInverseGalois.wreath_of_surjective_left`, `IsInverseGalois.wreath_of_surjective_right` and
  `IsInverseGalois.wreath_prod`, together with their regular counterparts over `ℚ(T)`.
-/

namespace RegularWreathProduct

/-! ## The first argument -/

section MapLeft

variable {D₁ D₂ Q : Type*} [Group D₁] [Group D₂] [Group Q]

/-- A homomorphism `D₁ →* D₂` applied to every coordinate of a wreath product over `Q`. -/
def mapLeft (f : D₁ →* D₂) : D₁ ≀ᵣ Q →* D₂ ≀ᵣ Q where
  toFun w := ⟨fun x ↦ f (w.left x), w.right⟩
  map_one' := by
    refine RegularWreathProduct.ext (funext fun x ↦ ?_) rfl
    simp
  map_mul' a b := by
    refine RegularWreathProduct.ext (funext fun x ↦ ?_) rfl
    simp

@[simp]
theorem mapLeft_left (f : D₁ →* D₂) (w : D₁ ≀ᵣ Q) :
    (mapLeft f w).left = fun x ↦ f (w.left x) := rfl

@[simp]
theorem mapLeft_right (f : D₁ →* D₂) (w : D₁ ≀ᵣ Q) : (mapLeft f w).right = w.right := rfl

/-- Wreathing preserves surjectivity in the first argument. -/
theorem mapLeft_surjective {f : D₁ →* D₂} (hf : Function.Surjective f) :
    Function.Surjective (mapLeft (Q := Q) f) := by
  rintro ⟨c, q⟩
  obtain ⟨a, ha⟩ := hf.comp_left (α := Q) c
  exact ⟨⟨a, q⟩, RegularWreathProduct.ext ha rfl⟩

end MapLeft

/-! ## The second argument -/

section MapRight

variable {D : Type*} [CommGroup D] {Q₁ Q₂ : Type*} [Group Q₁] [Group Q₂] [Fintype Q₁]

open scoped Classical in
/-- The **fibre product** of a family `a : Q₁ → D` along a homomorphism `π : Q₁ →* Q₂`: the value
at `y` is the product of the `a x` over the fibre of `π` above `y`.  It is well defined because
`D` is commutative. -/
noncomputable def fiberProd (π : Q₁ →* Q₂) (a : Q₁ → D) (y : Q₂) : D :=
  ∏ x : Q₁, if π x = y then a x else 1

@[simp]
theorem fiberProd_one (π : Q₁ →* Q₂) : fiberProd π (1 : Q₁ → D) = 1 := by
  classical
  funext y
  simp [fiberProd]

/-- The fibre product is multiplicative in the family. -/
theorem fiberProd_mul (π : Q₁ →* Q₂) (a b : Q₁ → D) :
    fiberProd π (a * b) = fiberProd π a * fiberProd π b := by
  classical
  funext y
  simp only [fiberProd, Pi.mul_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  split
  · rfl
  · rw [one_mul]

/-- Shifting the coordinates of a family by `p` shifts its fibre product by `π p`. -/
theorem fiberProd_comp_mul_left (π : Q₁ →* Q₂) (p : Q₁) (b : Q₁ → D) (y : Q₂) :
    fiberProd π (fun x ↦ b (p⁻¹ * x)) y = fiberProd π b ((π p)⁻¹ * y) := by
  classical
  refine (Fintype.prod_equiv (Equiv.mulLeft p) _ _ fun x ↦ ?_).symm
  simp only [Equiv.coe_mulLeft, map_mul, inv_mul_cancel_left, eq_inv_mul_iff_mul_eq]

/-- A family supported on a section of `π`, with prescribed values there, has that prescribed
family as its fibre product. -/
theorem fiberProd_of_section [DecidableEq Q₁] (π : Q₁ →* Q₂) (s : Q₂ → Q₁)
    (hs : ∀ y, π (s y) = y) (c : Q₂ → D) :
    fiberProd π (fun x ↦ if x = s (π x) then c (π x) else 1) = c := by
  classical
  funext y
  refine (Finset.prod_eq_single (s y) ?_ ?_).trans ?_
  · intro x _ hx
    by_cases hxy : π x = y
    · rw [if_pos hxy]
      show (if x = s (π x) then c (π x) else 1) = 1
      rw [hxy, if_neg hx]
    · rw [if_neg hxy]
  · intro hy
    exact absurd (Finset.mem_univ _) hy
  · rw [if_pos (hs y)]
    show (if s y = s (π (s y)) then c (π (s y)) else 1) = c y
    rw [hs y, if_pos rfl]

open scoped Classical in
/-- A homomorphism `π : Q₁ →* Q₂` of index groups, pushing the coordinates of a wreath product
forward along the fibres of `π`.  The first argument must be commutative for the coordinates over a
fibre to be combinable. -/
noncomputable def mapRight (π : Q₁ →* Q₂) : D ≀ᵣ Q₁ →* D ≀ᵣ Q₂ where
  toFun w := ⟨fiberProd π w.left, π w.right⟩
  map_one' := by
    refine RegularWreathProduct.ext ?_ (map_one π)
    exact fiberProd_one (D := D) π
  map_mul' a b := by
    refine RegularWreathProduct.ext (funext fun y ↦ ?_) (map_mul π _ _)
    show fiberProd π (a.left * fun x ↦ b.left (a.right⁻¹ * x)) y = _
    rw [fiberProd_mul]
    show fiberProd π a.left y * fiberProd π (fun x ↦ b.left (a.right⁻¹ * x)) y = _
    rw [fiberProd_comp_mul_left]
    rfl

@[simp]
theorem mapRight_left (π : Q₁ →* Q₂) (w : D ≀ᵣ Q₁) :
    (mapRight π w).left = fiberProd π w.left := rfl

@[simp]
theorem mapRight_right (π : Q₁ →* Q₂) (w : D ≀ᵣ Q₁) : (mapRight π w).right = π w.right := rfl

/-- Wreathing by a commutative group preserves surjectivity in the second argument. -/
theorem mapRight_surjective {π : Q₁ →* Q₂} (hπ : Function.Surjective π) :
    Function.Surjective (mapRight (D := D) π) := by
  classical
  rintro ⟨c, q⟩
  refine ⟨⟨fun x ↦ if x = Function.surjInv hπ (π x) then c (π x) else 1,
    Function.surjInv hπ q⟩, ?_⟩
  exact RegularWreathProduct.ext
    (fiberProd_of_section π _ (Function.surjInv_eq hπ) c) (Function.surjInv_eq hπ q)

end MapRight

/-! ## Splitting the first argument into two -/

section Regroup

variable {D₁ D₂ Q : Type*} [CommGroup D₁] [Group D₂] [Group Q] [Fintype (D₂ ≀ᵣ Q)]

open scoped Classical in
/-- **Wreathing by a product, as a double wreath product.**  The `D₁`-coordinates of
`D₁ ≀ᵣ (D₂ ≀ᵣ Q)` are indexed by `D₂ ≀ᵣ Q`; pushing them forward along the projection to `Q` and
reading the `D₂`-coordinates off the second component gives a map to `(D₁ × D₂) ≀ᵣ Q`. -/
noncomputable def regroup : D₁ ≀ᵣ (D₂ ≀ᵣ Q) →* (D₁ × D₂) ≀ᵣ Q where
  toFun v := ⟨fun y ↦ (fiberProd (rightHom (D := D₂) (Q := Q)) v.left y, v.right.left y),
    v.right.right⟩
  map_one' := by
    refine RegularWreathProduct.ext (funext fun y ↦ ?_) rfl
    have : fiberProd (rightHom (D := D₂) (Q := Q)) (1 : (D₂ ≀ᵣ Q) → D₁) y = 1 := by
      rw [fiberProd_one]; rfl
    exact Prod.ext this rfl
  map_mul' u v := by
    refine RegularWreathProduct.ext (funext fun y ↦ ?_) rfl
    refine Prod.ext ?_ rfl
    show fiberProd rightHom (u.left * fun x ↦ v.left (u.right⁻¹ * x)) y = _
    rw [fiberProd_mul]
    show fiberProd rightHom u.left y * fiberProd rightHom (fun x ↦ v.left (u.right⁻¹ * x)) y = _
    rw [fiberProd_comp_mul_left]
    rfl

@[simp]
theorem regroup_right (v : D₁ ≀ᵣ (D₂ ≀ᵣ Q)) : (regroup v).right = v.right.right := rfl

/-- Every element of `(D₁ × D₂) ≀ᵣ Q` is the image of one of `D₁ ≀ᵣ (D₂ ≀ᵣ Q)`. -/
theorem regroup_surjective :
    Function.Surjective (regroup (D₁ := D₁) (D₂ := D₂) (Q := Q)) := by
  classical
  refine fun w ↦ ⟨⟨fun x ↦ if x = inl (rightHom x) then (w.left (rightHom x)).1 else 1,
    ⟨fun y ↦ (w.left y).2, w.right⟩⟩, ?_⟩
  refine RegularWreathProduct.ext (funext fun y ↦ ?_) rfl
  have hleft := congrFun
    (fiberProd_of_section (D := D₁) (rightHom (D := D₂) (Q := Q)) inl (fun y ↦ rfl)
      fun y ↦ (w.left y).1) y
  exact Prod.ext hleft rfl

end Regroup

end RegularWreathProduct

/-! ## Transport of realizations -/

/-- A surjection between the bottom groups transports a realization of a wreath product over `ℚ`.
-/
theorem IsInverseGalois.wreath_of_surjective_left {D₁ D₂ Q : Type*} [Group D₁] [Finite D₁]
    [Group D₂] [Finite D₂] [Group Q] [Finite Q] (f : D₁ →* D₂) (hf : Function.Surjective f)
    (h : IsInverseGalois (D₁ ≀ᵣ Q)) : IsInverseGalois (D₂ ≀ᵣ Q) :=
  h.of_surjective (RegularWreathProduct.mapLeft f) (RegularWreathProduct.mapLeft_surjective hf)

/-- A surjection between the index groups transports a realization of a wreath product by a finite
abelian group over `ℚ`. -/
theorem IsInverseGalois.wreath_of_surjective_right {D : Type*} [CommGroup D] [Finite D]
    {Q₁ Q₂ : Type*} [Group Q₁] [Finite Q₁] [Group Q₂] [Finite Q₂] (π : Q₁ →* Q₂)
    (hπ : Function.Surjective π) (h : IsInverseGalois (D ≀ᵣ Q₁)) : IsInverseGalois (D ≀ᵣ Q₂) := by
  letI := Fintype.ofFinite Q₁
  exact h.of_surjective (RegularWreathProduct.mapRight π)
    (RegularWreathProduct.mapRight_surjective hπ)

/-- **A wreath product by a product is realized by a double wreath product.**  Over `ℚ`. -/
theorem IsInverseGalois.wreath_prod {D₁ D₂ Q : Type*} [CommGroup D₁] [Finite D₁] [Group D₂]
    [Finite D₂] [Group Q] [Finite Q] (h : IsInverseGalois (D₁ ≀ᵣ (D₂ ≀ᵣ Q))) :
    IsInverseGalois ((D₁ × D₂) ≀ᵣ Q) := by
  letI := Fintype.ofFinite (D₂ ≀ᵣ Q)
  exact h.of_surjective RegularWreathProduct.regroup RegularWreathProduct.regroup_surjective

/-- A surjection between the bottom groups transports a regular realization of a wreath product
over `ℚ(T)`. -/
theorem IsRegularInverseGalois.wreath_of_surjective_left {D₁ D₂ Q : Type*} [Group D₁] [Finite D₁]
    [Group D₂] [Finite D₂] [Group Q] [Finite Q] (f : D₁ →* D₂) (hf : Function.Surjective f)
    (h : IsRegularInverseGalois (D₁ ≀ᵣ Q)) : IsRegularInverseGalois (D₂ ≀ᵣ Q) :=
  h.of_surjective (RegularWreathProduct.mapLeft f) (RegularWreathProduct.mapLeft_surjective hf)

/-- A surjection between the index groups transports a regular realization of a wreath product by a
finite abelian group over `ℚ(T)`. -/
theorem IsRegularInverseGalois.wreath_of_surjective_right {D : Type*} [CommGroup D] [Finite D]
    {Q₁ Q₂ : Type*} [Group Q₁] [Finite Q₁] [Group Q₂] [Finite Q₂] (π : Q₁ →* Q₂)
    (hπ : Function.Surjective π) (h : IsRegularInverseGalois (D ≀ᵣ Q₁)) :
    IsRegularInverseGalois (D ≀ᵣ Q₂) := by
  letI := Fintype.ofFinite Q₁
  exact h.of_surjective (RegularWreathProduct.mapRight π)
    (RegularWreathProduct.mapRight_surjective hπ)

/-- **A wreath product by a product is realized by a double wreath product.**  Over `ℚ(T)`. -/
theorem IsRegularInverseGalois.wreath_prod {D₁ D₂ Q : Type*} [CommGroup D₁] [Finite D₁] [Group D₂]
    [Finite D₂] [Group Q] [Finite Q] (h : IsRegularInverseGalois (D₁ ≀ᵣ (D₂ ≀ᵣ Q))) :
    IsRegularInverseGalois ((D₁ × D₂) ≀ᵣ Q) := by
  letI := Fintype.ofFinite (D₂ ≀ᵣ Q)
  exact h.of_surjective RegularWreathProduct.regroup RegularWreathProduct.regroup_surjective
