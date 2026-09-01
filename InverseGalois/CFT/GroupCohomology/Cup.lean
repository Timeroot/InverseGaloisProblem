/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The cup product of two classes of the first cohomology

A pairing of the coefficients of two representations of a group with the coefficients of a third,
compatible with the three actions, multiplies cochains.  The product of two cochains of degree one
is the cochain of degree two whose value on a pair of group elements is the pairing of the value of
the first factor at the first entry with the translate by that entry of the value of the second
factor at the second entry.

The product of two cocycles is a cocycle: the cocycle identity of the first factor splits the value
at a product into a translate and a remainder, the translate assembles with the second factor into
the translate of the product, and the remainder assembles with the cocycle identity of the second
factor into the value at the other product.  The product of a coboundary with a cocycle is a
coboundary on either side, with an explicit primitive: on the left it is the pairing of the
coefficient of the coboundary with the other cocycle, and on the right it is the negative of the
pairing of the other cocycle with the translated coefficient.

So the product descends to classes, and gives a bilinear map from the first cohomology of the two
representations to the second cohomology of the third.

## Main definitions

* `InverseGalois.CFT.cup₁₁`: the product of two cochains of degree one along a pairing of the
  coefficients.
* `InverseGalois.CFT.cupCochains₁₁`: the same, as a bilinear map of cochains.
* `InverseGalois.CFT.cupCocycles₁₁`: the product of two cocycles of degree one, as a bilinear map
  to the cocycles of degree two.
* `InverseGalois.CFT.cupH1`: **the cup product of two classes of the first cohomology**, a bilinear
  map to the second cohomology.

## Main results

* `InverseGalois.CFT.cup₁₁_mem_cocycles₂`: **the product of two cocycles of degree one is a cocycle
  of degree two.**
* `InverseGalois.CFT.cup₁₁_mem_coboundaries₂_left` and
  `InverseGalois.CFT.cup₁₁_mem_coboundaries₂_right`: **the product of a coboundary of degree one
  with a cocycle of degree one is a coboundary of degree two**, on either side.
* `InverseGalois.CFT.cupH1_apply`: the cup product of two classes is the class of the product of
  any two cocycles representing them.

## Tags

group cohomology, cup product, cocycle, coboundary, pairing
-/

universe u

namespace InverseGalois.CFT

open groupCohomology

section Cup

variable {k G : Type u} [CommRing k] [Group G] {A B C : Rep k G}

/-- The product of two cochains of degree one along a pairing of the coefficients: its value on a
pair of group elements is the pairing of the value of the first factor at the first entry with the
translate by that entry of the value of the second factor at the second entry. -/
noncomputable def cup₁₁ (Φ : A →ₗ[k] B →ₗ[k] C) (f₁ : G → A) (f₂ : G → B) : G × G → C :=
  fun p => Φ (f₁ p.1) (B.ρ p.1 (f₂ p.2))

@[simp]
theorem cup₁₁_apply (Φ : A →ₗ[k] B →ₗ[k] C) (f₁ : G → A) (f₂ : G → B) (g h : G) :
    cup₁₁ Φ f₁ f₂ (g, h) = Φ (f₁ g) (B.ρ g (f₂ h)) := rfl

theorem cup₁₁_add_left (Φ : A →ₗ[k] B →ₗ[k] C) (f₁ f₁' : G → A) (f₂ : G → B) :
    cup₁₁ Φ (f₁ + f₁') f₂ = cup₁₁ Φ f₁ f₂ + cup₁₁ Φ f₁' f₂ := by
  funext p; simp [cup₁₁]

theorem cup₁₁_smul_left (Φ : A →ₗ[k] B →ₗ[k] C) (c : k) (f₁ : G → A) (f₂ : G → B) :
    cup₁₁ Φ (c • f₁) f₂ = c • cup₁₁ Φ f₁ f₂ := by
  funext p; simp [cup₁₁]

theorem cup₁₁_add_right (Φ : A →ₗ[k] B →ₗ[k] C) (f₁ : G → A) (f₂ f₂' : G → B) :
    cup₁₁ Φ f₁ (f₂ + f₂') = cup₁₁ Φ f₁ f₂ + cup₁₁ Φ f₁ f₂' := by
  funext p; simp [cup₁₁]

theorem cup₁₁_smul_right (Φ : A →ₗ[k] B →ₗ[k] C) (c : k) (f₁ : G → A) (f₂ : G → B) :
    cup₁₁ Φ f₁ (c • f₂) = c • cup₁₁ Φ f₁ f₂ := by
  funext p; simp [cup₁₁]

variable (A B) in
/-- The product of two cochains of degree one, as a bilinear map. -/
noncomputable def cupCochains₁₁ (Φ : A →ₗ[k] B →ₗ[k] C) :
    (G → A) →ₗ[k] (G → B) →ₗ[k] (G × G → C) where
  toFun f₁ :=
    { toFun := fun f₂ => cup₁₁ Φ f₁ f₂
      map_add' := cup₁₁_add_right Φ f₁
      map_smul' := fun c f₂ => cup₁₁_smul_right Φ c f₁ f₂ }
  map_add' f₁ f₁' := LinearMap.ext (cup₁₁_add_left Φ f₁ f₁')
  map_smul' c f₁ := LinearMap.ext (cup₁₁_smul_left Φ c f₁)

@[simp]
theorem cupCochains₁₁_apply (Φ : A →ₗ[k] B →ₗ[k] C) (f₁ : G → A) (f₂ : G → B) :
    cupCochains₁₁ A B Φ f₁ f₂ = cup₁₁ Φ f₁ f₂ := rfl

/-! ### The product of two cocycles -/

/-- **The product of two cocycles of degree one is a cocycle of degree two.**  The cocycle identity
of the first factor splits its value at a product into a translate and a remainder; the translate
pairs with the second factor into the translate of the product, and the remainder pairs with the
cocycle identity of the second factor into the value at the other product. -/
theorem cup₁₁_mem_cocycles₂ (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b))
    {f₁ : G → A} (h₁ : f₁ ∈ cocycles₁ A) {f₂ : G → B} (h₂ : f₂ ∈ cocycles₁ B) :
    cup₁₁ Φ f₁ f₂ ∈ cocycles₂ C := by
  rw [mem_cocycles₁_iff] at h₁ h₂
  refine (mem_cocycles₂_iff _).2 fun g h j => ?_
  have hgh : (B.ρ (g * h)) (f₂ j) = B.ρ g (B.ρ h (f₂ j)) := by
    rw [map_mul]; rfl
  simp only [cup₁₁_apply, h₁ g h, hgh, map_add, LinearMap.add_apply, hΦ g (f₁ h) (B.ρ h (f₂ j)),
    h₂ h j]
  rw [add_assoc, ← map_add]

variable (A B) in
/-- The product of two cocycles of degree one along a pairing of the coefficients, as a bilinear map
to the cocycles of degree two. -/
noncomputable def cupCocycles₁₁ (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b)) :
    ↥(cocycles₁ A) →ₗ[k] ↥(cocycles₁ B) →ₗ[k] ↥(cocycles₂ C) where
  toFun f₁ :=
    { toFun := fun f₂ => ⟨cup₁₁ Φ f₁.1 f₂.1, cup₁₁_mem_cocycles₂ Φ hΦ f₁.2 f₂.2⟩
      map_add' := fun f₂ f₂' => Subtype.ext (cup₁₁_add_right Φ f₁.1 f₂.1 f₂'.1)
      map_smul' := fun c f₂ => Subtype.ext (cup₁₁_smul_right Φ c f₁.1 f₂.1) }
  map_add' f₁ f₁' :=
    LinearMap.ext fun f₂ => Subtype.ext (cup₁₁_add_left Φ f₁.1 f₁'.1 f₂.1)
  map_smul' c f₁ :=
    LinearMap.ext fun f₂ => Subtype.ext (cup₁₁_smul_left Φ c f₁.1 f₂.1)

@[simp]
theorem cupCocycles₁₁_coe (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b))
    (f₁ : ↥(cocycles₁ A)) (f₂ : ↥(cocycles₁ B)) :
    (cupCocycles₁₁ A B Φ hΦ f₁ f₂ : G × G → C) = cup₁₁ Φ f₁.1 f₂.1 := rfl

/-! ### The product with a coboundary -/

/-- **The product of a coboundary of degree one with a cocycle of degree one is a coboundary of
degree two**, with primitive the pairing of the coefficient of the coboundary with the cocycle. -/
theorem cup₁₁_mem_coboundaries₂_left (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b))
    {f₁ : G → A} (h₁ : f₁ ∈ coboundaries₁ A) {f₂ : G → B} (h₂ : f₂ ∈ cocycles₁ B) :
    cup₁₁ Φ f₁ f₂ ∈ coboundaries₂ C := by
  obtain ⟨a, rfl⟩ := h₁
  rw [mem_cocycles₁_iff] at h₂
  refine ⟨fun x => Φ a (f₂ x), ?_⟩
  funext p
  obtain ⟨x, y⟩ := p
  show C.ρ x (Φ a (f₂ y)) - Φ a (f₂ (x * y)) + Φ a (f₂ x) = Φ ((d₀₁ A) a x) (B.ρ x (f₂ y))
  rw [h₂ x y, map_add, d₀₁_hom_apply, map_sub, LinearMap.sub_apply, ← hΦ x a (f₂ y)]
  abel

/-- **The product of a cocycle of degree one with a coboundary of degree one is a coboundary of
degree two**, with primitive the negative of the pairing of the cocycle with the translated
coefficient of the coboundary. -/
theorem cup₁₁_mem_coboundaries₂_right (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b))
    {f₁ : G → A} (h₁ : f₁ ∈ cocycles₁ A) {f₂ : G → B} (h₂ : f₂ ∈ coboundaries₁ B) :
    cup₁₁ Φ f₁ f₂ ∈ coboundaries₂ C := by
  obtain ⟨b, rfl⟩ := h₂
  rw [mem_cocycles₁_iff] at h₁
  refine ⟨fun x => -Φ (f₁ x) (B.ρ x b), ?_⟩
  funext p
  obtain ⟨x, y⟩ := p
  have hxy : (B.ρ (x * y)) b = B.ρ x (B.ρ y b) := by rw [map_mul]; rfl
  show C.ρ x (-Φ (f₁ y) (B.ρ y b)) - -Φ (f₁ (x * y)) (B.ρ (x * y) b) + -Φ (f₁ x) (B.ρ x b)
    = Φ (f₁ x) (B.ρ x ((d₀₁ B) b y))
  rw [d₀₁_hom_apply, map_sub, map_sub, h₁ x y, map_add, LinearMap.add_apply, map_neg,
    ← hΦ x (f₁ y) (B.ρ y b), ← hxy]
  abel

end Cup

/-! ### The cup product on cohomology -/

section Descent

variable {k G : Type u} [CommRing k] [Group G] (A B C : Rep k G)

theorem H1π_surjective : Function.Surjective (H1π A).hom :=
  fun y => H1_induction_on y fun x => ⟨x, rfl⟩

/-- The first cohomology is the cocycles of degree one modulo the kernel of the projection. -/
noncomputable def h1QuotEquiv :
    (↥(cocycles₁ A) ⧸ LinearMap.ker (H1π A).hom) ≃ₗ[k] H1 A :=
  LinearMap.quotKerEquivOfSurjective _ (H1π_surjective A)

@[simp]
theorem h1QuotEquiv_mk (f : ↥(cocycles₁ A)) :
    h1QuotEquiv A (Submodule.Quotient.mk f) = H1π A f := rfl

variable {A B C}

/-- The pairing of two cocycles of degree one with the class of their product in the second
cohomology. -/
noncomputable def cupClass₁₁ (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b)) :
    ↥(cocycles₁ A) →ₗ[k] ↥(cocycles₁ B) →ₗ[k] H2 C :=
  LinearMap.compr₂ (cupCocycles₁₁ A B Φ hΦ) (H2π C).hom

@[simp]
theorem cupClass₁₁_apply (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b))
    (f₁ : ↥(cocycles₁ A)) (f₂ : ↥(cocycles₁ B)) :
    cupClass₁₁ Φ hΦ f₁ f₂ = H2π C (cupCocycles₁₁ A B Φ hΦ f₁ f₂) := rfl

/-- The class of the product of two cocycles of degree one does not change when the second factor is
changed by a coboundary. -/
noncomputable def cupClassRight₁₁ (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b)) :
    ↥(cocycles₁ A) →ₗ[k] (↥(cocycles₁ B) ⧸ LinearMap.ker (H1π B).hom) →ₗ[k] H2 C where
  toFun f₁ :=
    Submodule.liftQ _ (cupClass₁₁ Φ hΦ f₁) fun f₂ hf₂ => by
      refine (H2π_eq_zero_iff _).2 ?_
      exact cup₁₁_mem_coboundaries₂_right Φ hΦ f₁.2 ((H1π_eq_zero_iff f₂).1 hf₂)
  map_add' f₁ f₁' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨f₂, rfl⟩ := Submodule.mkQ_surjective _ x
    simp
  map_smul' c f₁ := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨f₂, rfl⟩ := Submodule.mkQ_surjective _ x
    simp

@[simp]
theorem cupClassRight₁₁_apply (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b))
    (f₁ : ↥(cocycles₁ A)) (f₂ : ↥(cocycles₁ B)) :
    cupClassRight₁₁ Φ hΦ f₁ (Submodule.Quotient.mk f₂)
      = H2π C (cupCocycles₁₁ A B Φ hΦ f₁ f₂) := rfl

/-- The cup product of two classes of the first cohomology, presented on the quotient of the
cocycles of degree one by the kernel of the projection. -/
noncomputable def cupQuot₁₁ (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b)) :
    (↥(cocycles₁ A) ⧸ LinearMap.ker (H1π A).hom) →ₗ[k]
      (↥(cocycles₁ B) ⧸ LinearMap.ker (H1π B).hom) →ₗ[k] H2 C :=
  Submodule.liftQ _ (cupClassRight₁₁ Φ hΦ) fun f₁ hf₁ => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨f₂, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Submodule.mkQ_apply, cupClassRight₁₁_apply, LinearMap.zero_apply]
    refine (H2π_eq_zero_iff _).2 ?_
    exact cup₁₁_mem_coboundaries₂_left Φ hΦ ((H1π_eq_zero_iff f₁).1 hf₁) f₂.2

/-- **The cup product of two classes of the first cohomology**, a bilinear map to the second
cohomology of the coefficients paired. -/
noncomputable def cupH1 (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b)) :
    H1 A →ₗ[k] H1 B →ₗ[k] H2 C :=
  LinearMap.compl₂ ((cupQuot₁₁ Φ hΦ).comp (h1QuotEquiv A).symm.toLinearMap)
    (h1QuotEquiv B).symm.toLinearMap

/-- **The cup product of two classes is the class of the product of any two cocycles representing
them.** -/
@[simp]
theorem cupH1_apply (Φ : A →ₗ[k] B →ₗ[k] C)
    (hΦ : ∀ (g : G) (a : A) (b : B), Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b))
    (f₁ : ↥(cocycles₁ A)) (f₂ : ↥(cocycles₁ B)) :
    cupH1 Φ hΦ (H1π A f₁) (H1π B f₂) = H2π C (cupCocycles₁₁ A B Φ hΦ f₁ f₂) := by
  have hA : (h1QuotEquiv A).symm (H1π A f₁) = Submodule.Quotient.mk f₁ :=
    (LinearEquiv.symm_apply_eq _).2 (h1QuotEquiv_mk A f₁).symm
  have hB : (h1QuotEquiv B).symm (H1π B f₂) = Submodule.Quotient.mk f₂ :=
    (LinearEquiv.symm_apply_eq _).2 (h1QuotEquiv_mk B f₂).symm
  simp only [cupH1, LinearMap.compl₂_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, hA, hB]
  rfl

end Descent

end InverseGalois.CFT
