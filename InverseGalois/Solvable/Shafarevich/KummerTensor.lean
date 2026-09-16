/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelFlatRadicand

/-!
# The Kummer homomorphism as a map out of a tensor product

The homomorphism of the kernel of the base realization assembled out of a family of units of the
level and a family of elements of the target is the product of the powers of the elements by the
Kummer characters of the units.  That expression is **bilinear** in the two families, and it kills
the level-th powers of a unit as soon as the target has exponent the level, so it does not depend
on the families themselves but only on the tensor they define.

Reading it that way removes the indexing.  A family is a sum of pure tensors, but a tensor that is
carried to itself by a group need not be presented as one, and the equivariance of the assembled
homomorphism becomes a single equation between two maps applied to that tensor — with no
permutation of an index set to exhibit and no bookkeeping between the two families.

## Main definitions

* `InverseGalois.Shafarevich.kummerCharHom`: the Kummer character of a unit, as a homomorphism of
  the additive copy of the units.
* `InverseGalois.Shafarevich.kummerTensorKernelHom`: **the homomorphism of the kernel of the base
  realization assembled out of a tensor.**
* `InverseGalois.Shafarevich.twistTensor`: the tensor carried by an automorphism of the level on
  the radicand and by the exponent by which that automorphism raises the roots of unity on the
  coefficient.

## Main results

* `InverseGalois.Shafarevich.kummerTensorHom_tmul`: on a pure tensor it is the power of the element
  by the Kummer character of the unit.
* `InverseGalois.Shafarevich.kummerTensorKernelHom_conj`: **conjugating the argument by an
  automorphism moves the assembled homomorphism by a map of the target, as soon as the twist of the
  tensor is the tensor carried by that map.**
* `InverseGalois.Shafarevich.kummerTensorKernelHom_sum`: on the tensor a family defines it is the
  homomorphism assembled out of that family.
* `InverseGalois.Shafarevich.exists_forall_sum_tmul_eq`: **a spanning family of the coefficient
  presents every tensor**, so a tensor may always be read as a family of units against a family of
  coefficients fixed in advance.

## Tags

Shafarevich's theorem, Kummer theory, tensor product, embedding problem
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT TensorProduct

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### Scalars modulo the exponent -/

section Scalar

variable {n : ℕ} [NeZero n] {N : Type*} [AddCommGroup N] [Module (ZMod n) N]

/-- A scalar modulo the exponent acts through its representative. -/
theorem zmod_smul_eq_val_nsmul (c : ZMod n) (x : N) : c • x = c.val • x := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod n) c.val x, ZMod.natCast_rightInverse c]

end Scalar

/-! ### Presenting a tensor along a spanning family of the coefficient -/

section Present

variable {ℓ : ℕ} {G M : Type*} [CommGroup G] [CommGroup M] {T : Type*} [Fintype T]

/-- **A spanning family of the coefficient presents every tensor.**

If every element of the coefficient group is a product of powers of a finite family, then every
tensor of an arbitrary group with that coefficient is the sum of the pure tensors of a single
family of the first group against that fixed family — the coefficient side of the presentation is
the one given in advance, and only the radicand side is produced. -/
theorem exists_forall_sum_tmul_eq (b : T → M)
    (hspan : ∀ m : M, ∃ d : T → ZMod ℓ, ∏ q, b q ^ (d q).val = m)
    (s : Additive G ⊗[ℤ] Additive M) :
    ∃ z : T → G, s = ∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (b q) := by
  have hL : ∀ (m : ℕ) (x : Additive G) (y : Additive M),
      Additive.ofMul (Additive.toMul x ^ m) ⊗ₜ[ℤ] y = x ⊗ₜ[ℤ] (m • y) := by
    intro m x y
    induction m with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, _root_.ofMul_mul, add_tmul, ih, _root_.ofMul_toMul, succ_nsmul, tmul_add]
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨fun _ => 1, by simp⟩
  | tmul u v =>
    obtain ⟨d, hd⟩ := hspan (Additive.toMul v)
    refine ⟨fun q => Additive.toMul u ^ (d q).val, ?_⟩
    have hv : ∑ q, (d q).val • Additive.ofMul (b q) = v := by
      have h1 : Additive.ofMul (∏ q, b q ^ (d q).val) = v := by
        rw [hd, _root_.ofMul_toMul]
      rw [_root_.ofMul_prod] at h1
      simpa only [_root_.ofMul_pow] using h1
    rw [← hv, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun q _ => (hL _ u _).symm
  | add s₁ s₂ h₁ h₂ =>
    obtain ⟨z₁, hz₁⟩ := h₁
    obtain ⟨z₂, hz₂⟩ := h₂
    refine ⟨fun q => z₁ q * z₂ q, ?_⟩
    rw [hz₁, hz₂, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [_root_.ofMul_mul, add_tmul]

end Present

/-! ### The twist of a tensor -/

section Twist

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}
variable {M : Type*} [CommGroup M]

/-- The action of an automorphism of the level on the additive copy of its units. -/
def unitsAut (σ : Gal(↥K/k)) : Additive (↥K)ˣ →+ Additive (↥K)ˣ where
  toFun u := Additive.ofMul (σ • u.toMul)
  map_zero' := congrArg Additive.ofMul (smul_one σ)
  map_add' _ _ := congrArg Additive.ofMul (smul_mul' σ _ _)

@[simp]
theorem unitsAut_apply (σ : Gal(↥K/k)) (u : (↥K)ˣ) :
    unitsAut σ (Additive.ofMul u) = Additive.ofMul (σ • u) := rfl

variable (M) in
/-- **The twist of a tensor of the units of the level with the target**: the radicand is carried by
an automorphism of the level and the coefficient is raised to the exponent by which that
automorphism raises the roots of unity. -/
noncomputable def twistTensor (σ : Gal(↥K/k)) (e : ℕ) :
    Additive (↥K)ˣ ⊗[ℤ] Additive M →ₗ[ℤ] Additive (↥K)ˣ ⊗[ℤ] Additive M :=
  TensorProduct.map (unitsAut σ).toIntLinearMap (e • LinearMap.id)

theorem twistTensor_tmul (σ : Gal(↥K/k)) (e : ℕ) (u : Additive (↥K)ˣ) (v : Additive M) :
    twistTensor M σ e (u ⊗ₜ[ℤ] v) = Additive.ofMul (σ • u.toMul) ⊗ₜ[ℤ] Additive.ofMul (v.toMul ^ e)
  := rfl

variable (M) in
/-- **The tensor carried by a map of the target on the coefficient.** -/
noncomputable def coeffTensor (f : M →* M) :
    Additive (↥K)ˣ ⊗[ℤ] Additive M →ₗ[ℤ] Additive (↥K)ˣ ⊗[ℤ] Additive M :=
  TensorProduct.map LinearMap.id (MonoidHom.toAdditive f).toIntLinearMap

theorem coeffTensor_tmul (f : M →* M) (u : Additive (↥K)ˣ) (v : Additive M) :
    coeffTensor M f (u ⊗ₜ[ℤ] v) = u ⊗ₜ[ℤ] Additive.ofMul (f v.toMul) := rfl

/-! ### The twist read off an invariance -/

/-- Twisting by the inverse of an automorphism undoes the action of that automorphism on the
radicand and raises the coefficient to the exponent. -/
theorem twistTensor_comp_map (ρ : Gal(↥K/k)) {e : ℕ} {f ast : M →* M}
    (hast : ∀ m, ast m ^ e = f m) :
    (twistTensor M ρ⁻¹ e) ∘ₗ TensorProduct.map (unitsAut ρ).toIntLinearMap
        (MonoidHom.toAdditive ast).toIntLinearMap
      = coeffTensor M f := by
  refine TensorProduct.ext' fun x y => ?_
  show Additive.ofMul (ρ⁻¹ • ρ • x.toMul) ⊗ₜ[ℤ] Additive.ofMul (ast y.toMul ^ e)
    = x ⊗ₜ[ℤ] Additive.ofMul (f y.toMul)
  rw [inv_smul_smul, hast]
  rfl

/-- **A tensor carried to itself by an automorphism on the radicand and a map on the coefficient
has its twist by the inverse of that automorphism equal to the tensor a second map carries it
to**, as soon as the exponent-th power of the first map is the second.

This is the shape the equivariance of the assembled homomorphism is asked in, and the hypothesis is
the invariance of a tensor for the diagonal action twisted on the coefficient. -/
theorem twistTensor_eq_coeffTensor_of_map_eq {ρ : Gal(↥K/k)} {e : ℕ} {f ast : M →* M}
    (hast : ∀ m, ast m ^ e = f m) {t : Additive (↥K)ˣ ⊗[ℤ] Additive M}
    (hinv : TensorProduct.map (unitsAut ρ).toIntLinearMap
      (MonoidHom.toAdditive ast).toIntLinearMap t = t) :
    twistTensor M ρ⁻¹ e t = coeffTensor M f t := by
  calc twistTensor M ρ⁻¹ e t
      = twistTensor M ρ⁻¹ e (TensorProduct.map (unitsAut ρ).toIntLinearMap
          (MonoidHom.toAdditive ast).toIntLinearMap t) := by rw [hinv]
    _ = coeffTensor M f t := LinearMap.congr_fun (twistTensor_comp_map ρ hast) t

/-- **A map of a target killed by the level has an exponent-th root among the maps of the target**,
as soon as the exponent is invertible modulo the level: that root is the power of the map by an
inverse of the exponent. -/
theorem exists_monoidHom_pow_eq {ℓ : ℕ} (hexp : ∀ m : M, m ^ ℓ = 1) (f : M →* M) {e e' : ℕ}
    (he : (e' : ZMod ℓ) * (e : ZMod ℓ) = 1) : ∃ ast : M →* M, ∀ m, ast m ^ e = f m := by
  refine ⟨(powMonoidHom e').comp f, fun m => ?_⟩
  show (f m ^ e') ^ e = f m
  rw [← pow_mul]
  conv_rhs => rw [← pow_one (f m)]
  refine pow_eq_pow_of_pow_eq_one (hexp _) ?_
  push_cast
  rw [he]

end Twist

/-! ### The homomorphism assembled out of a tensor -/

section Tensor

variable {ℓ : ℕ} [NeZero ℓ] {k Ω U : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [Group U] {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω}
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ ℓ}

attribute [local instance] zmodTrivialAction

variable (hKker : K.fixingSubgroup = φ.ker)
  (h : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)

/-- **The Kummer character of a unit at a fixed automorphism, as a homomorphism** of the additive
copy of the units of the level. -/
noncomputable def kummerCharHom (g : Gal(Ω/↥K)) : Additive (↥K)ˣ →+ ZMod ℓ where
  toFun z := kummerChar h z.toMul g
  map_zero' := kummerChar_one_units h g
  map_add' _ _ := kummerChar_mul_units h _ _ g

@[simp]
theorem kummerCharHom_apply (g : Gal(Ω/↥K)) (z : (↥K)ˣ) :
    kummerCharHom h g (Additive.ofMul z) = kummerChar h z g := rfl

variable {M : Type*} [CommGroup M] (hexp : ∀ m : M, m ^ ℓ = 1)

include hexp in
/-- The additive copy of a group whose exponent divides the level is a module over the integers
modulo the level. -/
noncomputable def zmodModuleOfExp : Module (ZMod ℓ) (Additive M) :=
  AddCommGroup.zmodModule fun x => by simpa using hexp x.toMul

/-- **The homomorphism of the kernel of the base realization assembled out of a tensor** of the
units of the level with the target: on a pure tensor it is the power of the element by the Kummer
character of the unit, and it is defined on every tensor because that expression is bilinear and
kills the level-th powers. -/
noncomputable def kummerTensorHom (y : ↥φ.ker) :
    Additive (↥K)ˣ ⊗[ℤ] Additive M →+ Additive M :=
  letI := zmodModuleOfExp (ℓ := ℓ) hexp
  (TensorProduct.lift
    { toFun := fun z =>
        (smulAddHom (ZMod ℓ) (Additive M)
          (kummerCharHom h (kerGalEquiv hKker y) z)).toIntLinearMap
      map_add' := fun z z' => by
        refine LinearMap.ext fun b => ?_
        show (kummerCharHom h (kerGalEquiv hKker y) (z + z')) • b = _
        rw [map_add, add_smul]
        rfl
      map_smul' := fun c z => by
        refine LinearMap.ext fun b => ?_
        show (kummerCharHom h (kerGalEquiv hKker y) (c • z)) • b = c • _
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod ℓ) c
          (kummerCharHom h (kerGalEquiv hKker y) z), smul_assoc,
          Int.cast_smul_eq_zsmul (ZMod ℓ) c
            ((kummerCharHom h (kerGalEquiv hKker y) z) • b)]
        rfl }).toAddMonoidHom

/-- On a pure tensor the assembled homomorphism is the power of the element by the Kummer character
of the unit. -/
theorem kummerTensorHom_tmul (y : ↥φ.ker) (z : (↥K)ˣ) (m : M) :
    kummerTensorHom hKker h hexp y (Additive.ofMul z ⊗ₜ[ℤ] Additive.ofMul m)
      = Additive.ofMul (m ^ (kummerChar h z (kerGalEquiv hKker y)).val) := by
  letI := zmodModuleOfExp (ℓ := ℓ) hexp
  show (kummerCharHom h (kerGalEquiv hKker y) (Additive.ofMul z)) • (Additive.ofMul m) = _
  rw [zmod_smul_eq_val_nsmul, kummerCharHom_apply]
  exact (ofMul_pow _ _).symm

theorem kummerTensorHom_tmul' (y : ↥φ.ker) (u : Additive (↥K)ˣ) (v : Additive M) :
    kummerTensorHom hKker h hexp y (u ⊗ₜ[ℤ] v)
      = Additive.ofMul (v.toMul ^ (kummerChar h u.toMul (kerGalEquiv hKker y)).val) :=
  kummerTensorHom_tmul hKker h hexp y u.toMul v.toMul

/-- The assembled homomorphism is a homomorphism of the argument as well. -/
theorem kummerTensorHom_mul (y y' : ↥φ.ker) (t : Additive (↥K)ˣ ⊗[ℤ] Additive M) :
    kummerTensorHom hKker h hexp (y * y') t
      = kummerTensorHom hKker h hexp y t + kummerTensorHom hKker h hexp y' t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      rw [kummerTensorHom_tmul', kummerTensorHom_tmul', kummerTensorHom_tmul', ← ofMul_mul,
        ← pow_add]
      refine congrArg Additive.ofMul (pow_eq_pow_of_pow_eq_one (hexp _) ?_)
      push_cast [ZMod.natCast_zmod_val]
      rw [_root_.map_mul, kummerChar_mul]
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']; abel

/-- **The homomorphism of the kernel of the base realization assembled out of a tensor.** -/
noncomputable def kummerTensorKernelHom (t : Additive (↥K)ˣ ⊗[ℤ] Additive M) : ↥φ.ker →* M where
  toFun y := (kummerTensorHom hKker h hexp y t).toMul
  map_one' := by
    have hone := kummerTensorHom_mul hKker h hexp 1 1 t
    rw [mul_one] at hone
    have hz : kummerTensorHom hKker h hexp 1 t = 0 :=
      add_left_cancel (a := kummerTensorHom hKker h hexp 1 t)
        (b := kummerTensorHom hKker h hexp 1 t) (c := 0) (by rw [add_zero]; exact hone.symm)
    show (kummerTensorHom hKker h hexp 1 t).toMul = 1
    rw [hz]
    rfl
  map_mul' y y' := congrArg Additive.toMul (kummerTensorHom_mul hKker h hexp y y' t)

theorem kummerTensorKernelHom_apply (t : Additive (↥K)ˣ ⊗[ℤ] Additive M) (y : ↥φ.ker) :
    kummerTensorKernelHom hKker h hexp t y = (kummerTensorHom hKker h hexp y t).toMul := rfl

/-- **On the tensor a family defines, the assembled homomorphism is the homomorphism assembled out
of that family.** -/
theorem kummerTensorKernelHom_sum {T : Type*} [Fintype T] (b : T → M) (z : T → (↥K)ˣ)
    (y : ↥φ.ker) :
    kummerTensorKernelHom hKker h hexp
        (∑ i, Additive.ofMul (z i) ⊗ₜ[ℤ] Additive.ofMul (b i)) y
      = kummerKernelHom hKker h b (fun i => hexp (b i)) z y := by
  rw [kummerTensorKernelHom_apply, map_sum, kummerKernelHom_apply, toMul_sum]
  exact Finset.prod_congr rfl fun i _ =>
    congrArg Additive.toMul (kummerTensorHom_tmul hKker h hexp y (z i) (b i))

/-- Carrying the coefficient of a tensor by a map of the target carries the assembled homomorphism
by that map. -/
theorem kummerTensorHom_coeffTensor (f : M →* M) (y : ↥φ.ker)
    (t : Additive (↥K)ˣ ⊗[ℤ] Additive M) :
    kummerTensorHom hKker h hexp y (coeffTensor M f t)
      = Additive.ofMul (f (kummerTensorHom hKker h hexp y t).toMul) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      rw [coeffTensor_tmul, kummerTensorHom_tmul', kummerTensorHom_tmul']
      exact congrArg Additive.ofMul (_root_.map_pow f _ _).symm
  | add t t' ht ht' =>
      simp only [map_add]
      rw [ht, ht']
      exact (congrArg Additive.ofMul (_root_.map_mul f _ _)).symm

/-! ### Conjugating the argument -/

variable [Normal k ↥K]

/-- **Conjugating the argument by an automorphism twists the tensor**: the assembled homomorphism
at a conjugated argument is the homomorphism assembled out of the twist of the tensor by the
inverse of the automorphism the conjugating element induces on the level, together with the
exponent by which it raises the roots of unity. -/
theorem kummerTensorHom_conj {g : Gal(Ω/k)} {e : ℕ}
    (hgζ : g • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ e) (y : ↥φ.ker)
    (hy : g * (y : Gal(Ω/k)) * g⁻¹ ∈ φ.ker) (t : Additive (↥K)ˣ ⊗[ℤ] Additive M) :
    kummerTensorHom hKker h hexp ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩ t
      = kummerTensorHom hKker h hexp y
          (twistTensor M ((AlgEquiv.restrictNormalHom (↥K) g)⁻¹) e t) := by
  have hτ : galSubHom K (kerGalEquiv hKker ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩)
      = g * galSubHom K (kerGalEquiv hKker y) * g⁻¹ := by
    rw [galSubHom_kerGalEquiv, galSubHom_kerGalEquiv]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      have hs : AlgEquiv.restrictNormalHom (↥K) g •
          ((AlgEquiv.restrictNormalHom (↥K) g)⁻¹ • u.toMul) = u.toMul * (1 : (↥K)ˣ) ^ ℓ := by
        rw [smul_inv_smul, one_pow, mul_one]
      rw [twistTensor_tmul, kummerTensorHom_tmul', kummerTensorHom_tmul',
        kummerChar_conj_of_smul_eq_mul_pow h hgζ hs hτ]
      simp only [toMul_ofMul]
      rw [← pow_mul]
      refine congrArg Additive.ofMul (pow_eq_pow_of_pow_eq_one (hexp _) ?_)
      push_cast [ZMod.natCast_zmod_val]
      ring
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']

/-- **Conjugating the argument by an automorphism moves the assembled homomorphism by a map of the
target, as soon as the twist of the tensor is the tensor that map carries it to.**

No permutation of an index set is exhibited and no family is named: the whole hypothesis is one
equation between two maps of the tensor. -/
theorem kummerTensorKernelHom_conj {g : Gal(Ω/k)} {e : ℕ}
    (hgζ : g • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ e) (f : M →* M)
    {t : Additive (↥K)ˣ ⊗[ℤ] Additive M}
    (ht : twistTensor M ((AlgEquiv.restrictNormalHom (↥K) g)⁻¹) e t = coeffTensor M f t)
    (y : ↥φ.ker) (hy : g * (y : Gal(Ω/k)) * g⁻¹ ∈ φ.ker) :
    kummerTensorKernelHom hKker h hexp t ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩
      = f (kummerTensorKernelHom hKker h hexp t y) := by
  rw [kummerTensorKernelHom_apply, kummerTensorHom_conj hKker h hexp hgζ y hy t, ht,
    kummerTensorHom_coeffTensor]
  rfl

end Tensor

end InverseGalois.Shafarevich
