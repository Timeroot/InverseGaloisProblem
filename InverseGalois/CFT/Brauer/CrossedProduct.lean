import Mathlib

/-!
# Crossed product algebras

Let `L / K` be a Galois extension of fields with group `G = Gal(L/K)`, and let
`f : G × G → Lˣ` be a multiplicative `2`-cocycle for the natural action of `G` on `Lˣ`.
The *crossed product* `(L, G, f)` is the free left `L`-module on symbols `u g`, `g : G`,
with multiplication determined by

`(a * u g) * (b * u h) = a * g b * f (g, h) * u (g * h)`.

## Main definitions

* `InverseGalois.CFT.CrossedProduct hf`: the underlying type, a copy of `G →₀ L`.
* `InverseGalois.CFT.CrossedProduct.single hf g a`: the element `a * u g`.
* `InverseGalois.CFT.CrossedProduct.incl`: the ring embedding of `L`.
* `InverseGalois.CFT.CrossedProduct.basisUnits`: the `L`-basis given by the symbols `u g`.

## Main statements

* `InverseGalois.CFT.CrossedProduct.single_mul_single`: the defining multiplication rule.
* `InverseGalois.CFT.CrossedProduct.single_mul_incl`: the symbol `u g` conjugates `L` by `g`.
* `InverseGalois.CFT.CrossedProduct.finrank_eq`: the dimension over `K` is `|G| ^ 2`.

-/

namespace InverseGalois.CFT

open groupCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {f : Gal(L/K) × Gal(L/K) → Lˣ}

/-- The crossed product algebra `(L, Gal(L/K), f)` attached to a multiplicative `2`-cocycle
`f : Gal(L/K) × Gal(L/K) → Lˣ`.  As a left `L`-module it is free on the symbols `u g`,
`g : Gal(L/K)`, here realised as the finitely supported functions `Gal(L/K) →₀ L`. -/
def CrossedProduct (_hf : IsMulCocycle₂ f) : Type _ := Gal(L/K) →₀ L

namespace CrossedProduct

variable {hf : IsMulCocycle₂ f}

noncomputable instance instAddCommGroup : AddCommGroup (CrossedProduct hf) :=
  inferInstanceAs (AddCommGroup (Gal(L/K) →₀ L))

noncomputable instance instModule : Module L (CrossedProduct hf) :=
  inferInstanceAs (Module L (Gal(L/K) →₀ L))

/-- The element `a * u g` of the crossed product. -/
noncomputable def single (hf : IsMulCocycle₂ f) (g : Gal(L/K)) (a : L) : CrossedProduct hf :=
  Finsupp.single g a

theorem single_congr {g : Gal(L/K)} {a b : L} (h : a = b) :
    single hf g a = single hf g b := by rw [h]

/-- Every element of the crossed product is a sum of elements `a * u g`. -/
@[elab_as_elim]
theorem induction_linear {motive : CrossedProduct hf → Prop} (x : CrossedProduct hf)
    (zero : motive 0) (add : ∀ p q : CrossedProduct hf, motive p → motive q → motive (p + q))
    (single : ∀ (g : Gal(L/K)) (a : L), motive (CrossedProduct.single hf g a)) : motive x :=
  Finsupp.induction_linear (M := L) (ι := Gal(L/K)) x zero add single

noncomputable instance instMul : Mul (CrossedProduct hf) where
  mul x y :=
    Finsupp.sum (x : Gal(L/K) →₀ L) fun g a =>
      Finsupp.sum (y : Gal(L/K) →₀ L) fun h b =>
        single hf (g * h) (a * g b * ((f (g, h) : Lˣ) : L))

theorem mul_def (x y : CrossedProduct hf) :
    x * y =
      Finsupp.sum (x : Gal(L/K) →₀ L) fun g a =>
        Finsupp.sum (y : Gal(L/K) →₀ L) fun h b =>
          single hf (g * h) (a * g b * ((f (g, h) : Lˣ) : L)) :=
  rfl

/-- The defining multiplication rule of the crossed product. -/
theorem single_mul_single (g h : Gal(L/K)) (a b : L) :
    single hf g a * single hf h b
      = single hf (g * h) (a * g b * ((f (g, h) : Lˣ) : L)) := by
  rw [mul_def]
  simp only [single]
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index] <;> simp

theorem zero_mul' (x : CrossedProduct hf) : (0 : CrossedProduct hf) * x = 0 := by
  rw [mul_def]
  exact Finsupp.sum_zero_index

theorem mul_zero' (x : CrossedProduct hf) : x * (0 : CrossedProduct hf) = 0 := by
  rw [mul_def]
  simp only [Finsupp.sum_zero_index, Finsupp.sum_fun_zero]

theorem add_mul' (x y z : CrossedProduct hf) : (x + y) * z = x * z + y * z := by
  simp only [mul_def]
  refine Finsupp.sum_add_index' (fun g => ?_) (fun g a₁ a₂ => ?_)
  · simp only [single, zero_mul, Finsupp.single_zero, Finsupp.sum_fun_zero]
  · simp only [single, add_mul, Finsupp.single_add, Finsupp.sum_add]

theorem mul_add' (x y z : CrossedProduct hf) : x * (y + z) = x * y + x * z := by
  simp only [mul_def]
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun g _ => ?_
  refine Finsupp.sum_add_index' (fun h => ?_) (fun h b₁ b₂ => ?_)
  · simp only [single, map_zero, mul_zero, zero_mul, Finsupp.single_zero]
  · simp only [single, map_add, mul_add, add_mul, Finsupp.single_add]

noncomputable instance instOne : One (CrossedProduct hf) where
  one := single hf 1 (((f (1, 1))⁻¹ : Lˣ) : L)

theorem one_def : (1 : CrossedProduct hf) = single hf 1 (((f (1, 1))⁻¹ : Lˣ) : L) := rfl

/-- The value of the cocycle at `(1, 1)` is a unit, so its inverse cancels it. -/
theorem inv_val_mul_val : ((((f (1, 1))⁻¹ : Lˣ) : L)) * ((f (1, 1) : Lˣ) : L) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem val_cocycle_fst_one (hf : IsMulCocycle₂ f) (g : Gal(L/K)) :
    ((f (g, 1) : Lˣ) : L) = g ((f (1, 1) : Lˣ) : L) := by
  rw [map_one_snd_of_isMulCocycle₂ hf g]
  simp

/-- Applying `g` to the inverse of `f (1, 1)` cancels the value `f (g, 1)`. -/
theorem map_inv_mul_cocycle (hf : IsMulCocycle₂ f) (g : Gal(L/K)) :
    g ((((f (1, 1))⁻¹ : Lˣ) : L)) * ((f (g, 1) : Lˣ) : L) = 1 := by
  rw [val_cocycle_fst_one hf g, ← map_mul, inv_val_mul_val (f := f), map_one]

theorem one_mul' (x : CrossedProduct hf) : (1 : CrossedProduct hf) * x = x := by
  induction x using CrossedProduct.induction_linear with
  | zero => exact mul_zero' 1
  | add p q hp hq => rw [mul_add', hp, hq]
  | single h b =>
    rw [one_def, single_mul_single, one_mul, map_one_fst_of_isMulCocycle₂ hf h,
      AlgEquiv.one_apply]
    refine single_congr ?_
    linear_combination b * inv_val_mul_val (f := f)

theorem mul_one' (x : CrossedProduct hf) : x * (1 : CrossedProduct hf) = x := by
  induction x using CrossedProduct.induction_linear with
  | zero => exact zero_mul' 1
  | add p q hp hq => rw [add_mul', hp, hq]
  | single g a =>
    rw [one_def, single_mul_single, mul_one]
    refine single_congr ?_
    linear_combination a * map_inv_mul_cocycle hf g

/-- The cocycle identity, transported to the underlying field. -/
theorem val_cocycle (hf : IsMulCocycle₂ f) (g h j : Gal(L/K)) :
    ((f (g * h, j) : Lˣ) : L) * ((f (g, h) : Lˣ) : L)
      = g ((f (h, j) : Lˣ) : L) * ((f (g, h * j) : Lˣ) : L) := by
  have := congrArg (Units.val) (hf g h j)
  simpa using this

theorem mul_assoc' (x y z : CrossedProduct hf) : x * y * z = x * (y * z) := by
  induction x using CrossedProduct.induction_linear with
  | zero => simp only [zero_mul']
  | add p q hp hq => rw [add_mul', add_mul', add_mul', hp, hq]
  | single g a =>
    induction y using CrossedProduct.induction_linear with
    | zero => simp only [zero_mul', mul_zero']
    | add p q hp hq => rw [mul_add', add_mul', add_mul', mul_add', hp, hq]
    | single h b =>
      induction z using CrossedProduct.induction_linear with
      | zero => simp only [mul_zero']
      | add p q hp hq => rw [mul_add', mul_add', mul_add', hp, hq]
      | single j c =>
        simp only [single_mul_single, mul_assoc g h j]
        refine single_congr ?_
        rw [AlgEquiv.mul_apply, map_mul, map_mul]
        linear_combination (a * g b * g (h c)) * val_cocycle hf g h j

noncomputable instance instRing : Ring (CrossedProduct hf) where
  __ := instAddCommGroup
  mul := (· * ·)
  one := 1
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  left_distrib := mul_add'
  right_distrib := add_mul'
  zero_mul := zero_mul'
  mul_zero := mul_zero'

theorem smul_single (a : L) (g : Gal(L/K)) (c : L) :
    a • single hf g c = single hf g (a * c) := by
  show (a • Finsupp.single g c : Gal(L/K) →₀ L) = Finsupp.single g (a * c)
  rw [Finsupp.smul_single, smul_eq_mul]

theorem smul_mul_assoc' (a : L) (x y : CrossedProduct hf) : a • x * y = a • (x * y) := by
  induction x using CrossedProduct.induction_linear with
  | zero => simp only [smul_zero, zero_mul]
  | add p q hp hq => rw [smul_add, add_mul, add_mul, hp, hq, smul_add]
  | single g c =>
    induction y using CrossedProduct.induction_linear with
    | zero => simp only [smul_zero, mul_zero]
    | add p q hp hq => rw [mul_add, mul_add, hp, hq, smul_add]
    | single h b =>
      rw [smul_single, single_mul_single, single_mul_single, smul_single]
      refine single_congr ?_
      ring

/-- The embedding of `L` into the crossed product, sending `a` to `a • 1`. -/
noncomputable def incl (hf : IsMulCocycle₂ f) : L →+* CrossedProduct hf where
  toFun a := a • (1 : CrossedProduct hf)
  map_one' := one_smul _ _
  map_mul' a b := by rw [smul_mul_assoc', one_mul, mul_smul]
  map_zero' := zero_smul _ _
  map_add' a b := add_smul _ _ _

theorem incl_apply (a : L) : incl hf a = a • (1 : CrossedProduct hf) := rfl

theorem incl_mul (a : L) (x : CrossedProduct hf) : incl hf a * x = a • x := by
  rw [incl_apply, smul_mul_assoc', one_mul]

theorem incl_eq_single (a : L) :
    incl hf a = single hf 1 (a * ((((f (1, 1))⁻¹ : Lˣ)) : L)) := by
  rw [incl_apply, one_def, smul_single]

/-- The symbol `u g` conjugates the copy of `L` inside the crossed product by `g`. -/
theorem single_mul_incl (g : Gal(L/K)) (a c : L) :
    single hf g a * incl hf c = incl hf (g c) * single hf g a := by
  rw [incl_eq_single, single_mul_single, incl_mul, smul_single, mul_one]
  refine single_congr ?_
  rw [map_mul]
  linear_combination (a * g c) * map_inv_mul_cocycle hf g

theorem mul_single_one (g : Gal(L/K)) (a : L) :
    single hf g 1 * incl hf a = incl hf (g a) * single hf g 1 :=
  single_mul_incl g 1 a

theorem incl_algebraMap_commutes (k : K) (x : CrossedProduct hf) :
    incl hf (algebraMap K L k) * x = x * incl hf (algebraMap K L k) := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [mul_zero, zero_mul]
  | add p q hp hq => rw [mul_add, add_mul, hp, hq]
  | single g a => rw [single_mul_incl, AlgEquiv.commutes]

noncomputable instance instAlgebra : Algebra K (CrossedProduct hf) :=
  RingHom.toAlgebra' ((incl hf).comp (algebraMap K L))
    fun k x => incl_algebraMap_commutes k x

theorem algebraMap_eq (k : K) :
    algebraMap K (CrossedProduct hf) k = incl hf (algebraMap K L k) := rfl

instance instIsScalarTower : IsScalarTower K L (CrossedProduct hf) where
  smul_assoc k a x := by
    rw [Algebra.smul_def (R := K) (A := CrossedProduct hf) k (a • x), algebraMap_eq,
      incl_mul, smul_smul, Algebra.smul_def k a]

/-- The `L`-basis of the crossed product given by the symbols `u g`, `g : Gal(L/K)`. -/
noncomputable def basisUnits (hf : IsMulCocycle₂ f) :
    Module.Basis Gal(L/K) L (CrossedProduct hf) :=
  Finsupp.basisSingleOne

@[simp]
theorem coe_basisUnits :
    ⇑(basisUnits hf) = fun g : Gal(L/K) => single hf g 1 :=
  Finsupp.coe_basisSingleOne

instance instFree : Module.Free L (CrossedProduct hf) :=
  Module.Free.of_basis (basisUnits hf)

theorem finrank_left [FiniteDimensional K L] :
    Module.finrank L (CrossedProduct hf) = Nat.card Gal(L/K) := by
  rw [Module.finrank_eq_card_basis (basisUnits hf), Nat.card_eq_fintype_card]

/-- The crossed product has dimension `|Gal(L/K)| ^ 2` over the base field `K`. -/
theorem finrank_eq [FiniteDimensional K L] [IsGalois K L] :
    Module.finrank K (CrossedProduct hf) = (Nat.card Gal(L/K)) ^ 2 := by
  rw [← Module.finrank_mul_finrank K L (CrossedProduct hf), finrank_left,
    IsGalois.card_aut_eq_finrank K L, sq]

/-- The value of the cocycle at `(1, 1)` is a unit, so it cancels its inverse. -/
theorem val_mul_inv_val : ((f (1, 1) : Lˣ) : L) * ((((f (1, 1))⁻¹ : Lˣ)) : L) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- The underlying finitely supported family of coordinates. -/
def toFinsupp (x : CrossedProduct hf) : Gal(L/K) →₀ L := x

theorem toFinsupp_injective : Function.Injective (toFinsupp (hf := hf)) := fun _ _ h => h

@[simp] theorem toFinsupp_single (g : Gal(L/K)) (a : L) :
    toFinsupp (single hf g a) = Finsupp.single g a := rfl

@[simp] theorem toFinsupp_zero : toFinsupp (0 : CrossedProduct hf) = 0 := rfl

@[simp] theorem toFinsupp_add (x y : CrossedProduct hf) :
    toFinsupp (x + y) = toFinsupp x + toFinsupp y := rfl

@[simp] theorem toFinsupp_smul (a : L) (x : CrossedProduct hf) :
    toFinsupp (a • x) = a • toFinsupp x := rfl

theorem toFinsupp_incl_mul (c : L) (x : CrossedProduct hf) (g : Gal(L/K)) :
    toFinsupp (incl hf c * x) g = c * toFinsupp x g := by
  rw [incl_mul, toFinsupp_smul, Finsupp.smul_apply, smul_eq_mul]

theorem toFinsupp_mul_incl (x : CrossedProduct hf) (c : L) (g : Gal(L/K)) :
    toFinsupp (x * incl hf c) g = g c * toFinsupp x g := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [zero_mul, toFinsupp_zero, Finsupp.coe_zero, Pi.zero_apply, mul_zero]
  | add p q hp hq =>
    rw [add_mul, toFinsupp_add, Finsupp.add_apply, hp, hq, toFinsupp_add, Finsupp.add_apply,
      mul_add]
  | single g' a =>
    rw [single_mul_incl, incl_mul, smul_single, toFinsupp_single, toFinsupp_single]
    by_cases h : g' = g
    · subst h
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne' h, Finsupp.single_eq_of_ne' h, mul_zero]

theorem exists_apply_ne {g : Gal(L/K)} (hg : g ≠ 1) : ∃ c : L, g c ≠ c := by
  by_contra h
  push_neg at h
  exact hg (AlgEquiv.ext fun c => (h c).trans (AlgEquiv.one_apply c).symm)

theorem toFinsupp_eq_zero_of_center {x : CrossedProduct hf}
    (hx : ∀ y : CrossedProduct hf, y * x = x * y) {g : Gal(L/K)} (hg : g ≠ 1) :
    toFinsupp x g = 0 := by
  obtain ⟨c, hc⟩ := exists_apply_ne hg
  have h := congrArg (fun y => toFinsupp y g) (hx (incl hf c))
  simp only [toFinsupp_incl_mul, toFinsupp_mul_incl] at h
  have h2 : (c - g c) * toFinsupp x g = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (by linear_combination -h3 : g c = c) hc
  · exact h3

theorem eq_single_one_of_center {x : CrossedProduct hf}
    (hx : ∀ y : CrossedProduct hf, y * x = x * y) :
    x = single hf 1 (toFinsupp x 1) := by
  refine toFinsupp_injective ?_
  rw [toFinsupp_single]
  ext g
  by_cases h : (1 : Gal(L/K)) = g
  · subst h
    rw [Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne' h]
    exact toFinsupp_eq_zero_of_center hx (Ne.symm h)

theorem exists_eq_incl_of_center {x : CrossedProduct hf}
    (hx : ∀ y : CrossedProduct hf, y * x = x * y) :
    ∃ a : L, x = incl hf a := by
  refine ⟨toFinsupp x 1 * ((f (1, 1) : Lˣ) : L), ?_⟩
  rw [incl_eq_single]
  conv_lhs => rw [eq_single_one_of_center hx]
  refine single_congr ?_
  linear_combination (-(toFinsupp x 1)) * val_mul_inv_val (f := f)

theorem apply_eq_self_of_center {a : L}
    (hx : ∀ y : CrossedProduct hf, y * incl hf a = incl hf a * y) (g : Gal(L/K)) :
    g a = a := by
  have h := hx (single hf g 1)
  rw [mul_single_one, incl_mul, incl_mul, smul_single, smul_single, mul_one, mul_one] at h
  have h2 := congrArg (fun z => toFinsupp z g) h
  simpa using h2

/-- The crossed product of a finite Galois extension is a central `K`-algebra. -/
instance instIsCentral [FiniteDimensional K L] [IsGalois K L] :
    Algebra.IsCentral K (CrossedProduct hf) where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    obtain ⟨a, rfl⟩ := exists_eq_incl_of_center hx
    obtain ⟨k, hk⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed a).2 fun g => apply_eq_self_of_center hx g
    exact Algebra.mem_bot.2 ⟨k, by rw [algebraMap_eq, hk]⟩

end CrossedProduct

end InverseGalois.CFT
