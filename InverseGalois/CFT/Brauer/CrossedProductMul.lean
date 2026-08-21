import Mathlib
import InverseGalois.CFT.Brauer.CrossedProductSimple
import InverseGalois.CFT.Brauer.Group

/-!
# The crossed product is multiplicative

Let `L / K` be a finite Galois extension with group `G = Gal(L/K)`.  Multiplicative `2`-cocycles
`f, f' : G × G → Lˣ` can be multiplied pointwise, and this file shows that the crossed-product
construction turns that product into the product of the corresponding classes in the Brauer group
of `K`: the class of the crossed product of `f * f'` is the product of the classes of the crossed
products of `f` and of `f'`.

The proof is an explicit matrix description of the tensor product.  Write `A`, `A'` and `B` for the
crossed products of `f`, of `f'` and of the pointwise product, and let `u g`, `u' g` and `v g`
denote their symbols.  Each factor is represented by monomial matrices of size `|G|` with entries
in `B`: the first factor acts through

`a * u j ↦ (m, h) ↦ if h = m * j then (a * (m⁻¹ (f' (m, j)))⁻¹) * v j else 0`,

the second one through

`b * u' j ↦ (m, h) ↦ if m = j * h then m⁻¹ (b * f' (j, h)) else 0`.

Both assignments are multiplicative and their images commute, all three verifications being the
cocycle identity for `f'`.  The resulting map `A ⊗[K] A' → Matrix G G B` is injective because the
source is a simple ring, and surjective because both sides have dimension `|G| ^ 4` over `K`.
Since a matrix algebra over `B` is Brauer equivalent to `B`, the classes multiply.

## Main results

* `InverseGalois.CFT.isMulCocycle₂_mul`: the pointwise product of two multiplicative `2`-cocycles
  is a multiplicative `2`-cocycle.
* `InverseGalois.CFT.isMulCocycle₂_inv`: the pointwise inverse of a multiplicative `2`-cocycle is
  a multiplicative `2`-cocycle.
* `InverseGalois.CFT.CrossedProduct.leftAlgHom`, `rightAlgHom`, `tensorHom`: the two monomial
  representations and the map they induce on the tensor product.
* `InverseGalois.CFT.CrossedProduct.tensorAlgEquiv`, `tensorAlgEquivFin`: the tensor product of two
  crossed products is a matrix algebra over the crossed product of the product cocycle.
* `InverseGalois.CFT.CrossedProduct.mk_csa_mul`: the class of the crossed product of a product of
  cocycles is the product of the classes.
-/

universe u

open scoped TensorProduct

namespace InverseGalois.CFT

open groupCohomology

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {f f' F : Gal(L/K) × Gal(L/K) → Lˣ}

/-- The pointwise product of two multiplicative `2`-cocycles is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_mul (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    IsMulCocycle₂ (fun p => f p * f' p) := by
  intro g h j
  simp only [smul_mul']
  rw [mul_mul_mul_comm, hf g h j, hf' g h j, mul_mul_mul_comm]

/-- The pointwise inverse of a multiplicative `2`-cocycle is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_inv (hf : IsMulCocycle₂ f) : IsMulCocycle₂ (fun p => (f p)⁻¹) := by
  intro g h j
  simp only [smul_inv', ← mul_inv]
  rw [hf g h j]

/-- The action of the Galois group on the units of `L`, read inside `L`. -/
theorem val_smul_units (g : Gal(L/K)) (u : Lˣ) : ((g • u : Lˣ) : L) = g (u : L) := rfl

namespace CrossedProduct

variable {hf : IsMulCocycle₂ f}

/-- Coefficients add. -/
theorem single_add (g : Gal(L/K)) (a b : L) :
    single hf g (a + b) = single hf g a + single hf g b :=
  Finsupp.single_add g a b

/-- A symbol with zero coefficient vanishes. -/
theorem single_zero' (g : Gal(L/K)) : single hf g 0 = 0 :=
  Finsupp.single_zero g

/-- The coordinates of a symbol. -/
theorem toFinsupp_single_apply [DecidableEq Gal(L/K)] (g j : Gal(L/K)) (a : L) :
    toFinsupp (single hf j a) g = if j = g then a else 0 :=
  Finsupp.single_apply

/-- Scalars from the base field act on the coefficient. -/
theorem smul_single_base (k : K) (g : Gal(L/K)) (a : L) :
    k • single hf g a = single hf g (algebraMap K L k * a) := by
  rw [← IsScalarTower.algebraMap_smul L k (single hf g a), smul_single]

/-- Coordinates of a base-field multiple. -/
theorem toFinsupp_smul_base (k : K) (x : CrossedProduct hf) (g : Gal(L/K)) :
    toFinsupp (k • x) g = algebraMap K L k * toFinsupp x g := by
  rw [← IsScalarTower.algebraMap_smul L k x, toFinsupp_smul, Finsupp.smul_apply, smul_eq_mul]

/-- Multiplying a symbol by a scalar on the right. -/
theorem single_mul_incl' (g : Gal(L/K)) (a c : L) :
    single hf g a * incl hf c = single hf g (g c * a) := by
  rw [single_mul_incl, incl_mul, smul_single]

/-- Multiplying a symbol by a scalar on the left. -/
theorem incl_mul_single (g : Gal(L/K)) (a c : L) :
    incl hf c * single hf g a = single hf g (c * a) := by
  rw [incl_mul, smul_single]

/-! ### The scalars entering the matrix representation -/

/-- The scalar by which the symbol `u j` of the first factor twists the `m`-th row. -/
noncomputable def rowScalar (f' : Gal(L/K) × Gal(L/K) → Lˣ) (m j : Gal(L/K)) : Lˣ :=
  (m⁻¹ • f' (m, j))⁻¹

/-- The cocycle identity, in the form used for the rows of the matrix representation. -/
theorem rowScalar_mul (hf' : IsMulCocycle₂ f') (m j j' : Gal(L/K)) :
    rowScalar f' m (j * j') = rowScalar f' m j * (j • rowScalar f' (m * j) j') * f' (j, j') := by
  have hsm : j • (((m * j)⁻¹ • f' (m * j, j'))⁻¹) = (m⁻¹ • f' (m * j, j'))⁻¹ := by
    rw [smul_inv', smul_smul]
    congr 2
    group
  rw [rowScalar, rowScalar, rowScalar, hsm, ← mul_inv, ← smul_mul']
  have hco := hf' m j j'
  have hmj : f' (m, j) * f' (m * j, j') = (m • f' (j, j')) * f' (m, j * j') := by
    rw [mul_comm]; exact hco
  rw [hmj, smul_mul', smul_smul, inv_mul_cancel, one_smul, mul_inv,
    mul_comm ((f' (j, j'))⁻¹), inv_mul_cancel_right]

/-- The cocycle identity, in the form used for the columns of the matrix representation. -/
theorem cocycle_swap (hf' : IsMulCocycle₂ f') (g h j : Gal(L/K)) :
    f' (g, h * j) * (g • f' (h, j)) = f' (g, h) * f' (g * h, j) := by
  rw [mul_comm (f' (g, h * j)), ← hf' g h j, mul_comm]

/-- The value of the row scalar at the identity. -/
theorem rowScalar_one (hf' : IsMulCocycle₂ f') (m : Gal(L/K)) :
    rowScalar f' m 1 = (f' (1, 1))⁻¹ := by
  rw [rowScalar, map_one_snd_of_isMulCocycle₂ hf' m, smul_smul, inv_mul_cancel, one_smul]

/-- The cocycle identity, in the form used to compare the two matrix representations. -/
theorem rowScalar_swap (hf' : IsMulCocycle₂ f') (j' k j : Gal(L/K)) :
    ((j' * k)⁻¹ • f' (j', k * j)) * rowScalar f' (j' * k) j
      = ((j' * k)⁻¹ • f' (j', k)) * rowScalar f' k j := by
  have hs : (k⁻¹ : Gal(L/K)) • f' (k, j) = ((j' * k)⁻¹ : Gal(L/K)) • (j' • f' (k, j)) := by
    rw [smul_smul]
    congr 1
    group
  have hkey : ((j' * k)⁻¹ • f' (j', k * j)) * ((k⁻¹ : Gal(L/K)) • f' (k, j))
      = ((j' * k)⁻¹ • f' (j', k)) * ((j' * k)⁻¹ • f' (j' * k, j)) := by
    rw [hs, ← smul_mul', cocycle_swap hf' j' k j, smul_mul']
  rw [rowScalar, rowScalar, mul_inv_eq_iff_eq_mul, mul_right_comm, ← hkey, mul_assoc,
    mul_inv_cancel, mul_one]

/-! ### The representation of the first factor -/

section Rep

variable [DecidableEq Gal(L/K)] {hf : IsMulCocycle₂ f} {hF : IsMulCocycle₂ F}

/-- The matrix attached to an element of the crossed product of the first cocycle. -/
noncomputable def leftMatrix (hf : IsMulCocycle₂ f) (f' : Gal(L/K) × Gal(L/K) → Lˣ)
    (hF : IsMulCocycle₂ F) (x : CrossedProduct hf) :
    Matrix Gal(L/K) Gal(L/K) (CrossedProduct hF) :=
  Matrix.of fun m h =>
    single hF (m⁻¹ * h) (toFinsupp x (m⁻¹ * h) * ((rowScalar f' m (m⁻¹ * h) : Lˣ) : L))

/-- The matrix attached to an element of the first crossed product, as a `K`-linear map. -/
noncomputable def leftLinear (hf : IsMulCocycle₂ f) (f' : Gal(L/K) × Gal(L/K) → Lˣ)
    (hF : IsMulCocycle₂ F) :
    CrossedProduct hf →ₗ[K] Matrix Gal(L/K) Gal(L/K) (CrossedProduct hF) where
  toFun := leftMatrix hf f' hF
  map_add' x y := by
    ext m h
    simp only [leftMatrix, Matrix.of_apply, Matrix.add_apply, toFinsupp_add, Finsupp.add_apply,
      add_mul, single_add]
  map_smul' k x := by
    ext m h
    simp only [leftMatrix, Matrix.of_apply, Matrix.smul_apply, toFinsupp_smul_base,
      smul_single_base, RingHom.id_apply, mul_assoc]

/-- The matrix of a symbol of the first crossed product has a single nonzero entry in each
column. -/
theorem leftLinear_apply_single (f' : Gal(L/K) × Gal(L/K) → Lˣ) (j : Gal(L/K)) (a : L)
    (m h : Gal(L/K)) :
    leftLinear hf f' hF (single hf j a) m h =
      if h = m * j then single hF j (a * ((rowScalar f' m j : Lˣ) : L)) else 0 := by
  have hiff : (j = m⁻¹ * h) ↔ (h = m * j) := by
    constructor
    · rintro rfl
      group
    · rintro rfl
      group
  show leftMatrix hf f' hF (single hf j a) m h = _
  rw [leftMatrix, Matrix.of_apply, toFinsupp_single_apply]
  by_cases hh : h = m * j
  · subst hh
    rw [inv_mul_cancel_left, if_pos rfl, if_pos rfl]
  · rw [if_neg hh, if_neg fun hc => hh (hiff.1 hc), zero_mul, single_zero']

/-- The representation of the first crossed product preserves the unit. -/
theorem leftLinear_one (hf' : IsMulCocycle₂ f') (hmul : ∀ p, F p = f p * f' p) :
    leftLinear hf f' hF (1 : CrossedProduct hf) = 1 := by
  have hval : (((f (1, 1))⁻¹ : Lˣ) : L) * (((f' (1, 1))⁻¹ : Lˣ) : L)
      = (((F (1, 1))⁻¹ : Lˣ) : L) := by
    have h0 : (F (1, 1))⁻¹ = (f (1, 1))⁻¹ * (f' (1, 1))⁻¹ := by
      rw [hmul (1, 1), mul_inv]
    rw [h0, Units.val_mul]
  ext m h
  rw [one_def, leftLinear_apply_single, Matrix.one_apply, mul_one, rowScalar_one hf']
  by_cases hh : h = m
  · subst hh
    rw [if_pos rfl, if_pos rfl, one_def]
    exact single_congr hval
  · rw [if_neg hh, if_neg fun hc => hh hc.symm]

/-- The representation of the first crossed product is multiplicative. -/
theorem leftLinear_mul [FiniteDimensional K L] (hf' : IsMulCocycle₂ f')
    (hmul : ∀ p, F p = f p * f' p) (x y : CrossedProduct hf) :
    leftLinear hf f' hF (x * y) = leftLinear hf f' hF x * leftLinear hf f' hF y := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_mul]
  | single j a =>
    induction y using CrossedProduct.induction_linear with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, mul_add]
    | single j' a' =>
      ext m h
      have hrs : ((rowScalar f' m (j * j') : Lˣ) : L)
          = ((rowScalar f' m j : Lˣ) : L) * j ((rowScalar f' (m * j) j' : Lˣ) : L)
            * ((f' (j, j') : Lˣ) : L) := by
        have h0 := congrArg (Units.val) (rowScalar_mul hf' m j j')
        rw [Units.val_mul, Units.val_mul, val_smul_units] at h0
        exact h0
      rw [Matrix.mul_apply, Finset.sum_eq_single (m * j)]
      · rw [single_mul_single, leftLinear_apply_single, leftLinear_apply_single,
          leftLinear_apply_single, if_pos rfl, ← mul_assoc m j j']
        by_cases hh : h = m * j * j'
        · rw [if_pos hh, if_pos hh, single_mul_single, hmul (j, j'), Units.val_mul, map_mul]
          refine single_congr ?_
          linear_combination (a * j a' * ((f (j, j') : Lˣ) : L)) * hrs
        · rw [if_neg hh, if_neg hh, mul_zero]
      · intro b _ hb
        rw [leftLinear_apply_single, if_neg hb, zero_mul]
      · intro hb
        exact absurd (Finset.mem_univ (m * j)) hb

/-! ### The representation of the second factor -/

/-- The matrix attached to an element of the crossed product of the second cocycle. -/
noncomputable def rightMatrix (hf' : IsMulCocycle₂ f') (hF : IsMulCocycle₂ F)
    (y : CrossedProduct hf') : Matrix Gal(L/K) Gal(L/K) (CrossedProduct hF) :=
  Matrix.of fun m h => incl hF (m⁻¹ (toFinsupp y (m * h⁻¹) * ((f' (m * h⁻¹, h) : Lˣ) : L)))

/-- The matrix attached to an element of the second crossed product, as a `K`-linear map. -/
noncomputable def rightLinear (hf' : IsMulCocycle₂ f') (hF : IsMulCocycle₂ F) :
    CrossedProduct hf' →ₗ[K] Matrix Gal(L/K) Gal(L/K) (CrossedProduct hF) where
  toFun := rightMatrix hf' hF
  map_add' x y := by
    ext m h
    simp only [rightMatrix, Matrix.of_apply, Matrix.add_apply, toFinsupp_add, Finsupp.add_apply,
      add_mul, map_add]
  map_smul' k x := by
    ext m h
    simp only [rightMatrix, Matrix.of_apply, Matrix.smul_apply, toFinsupp_smul_base,
      RingHom.id_apply, mul_assoc, map_mul, AlgEquiv.commutes]
    rw [← algebraMap_eq, ← Algebra.smul_def]

/-- The matrix of a symbol of the second crossed product has a single nonzero entry in each
column. -/
theorem rightLinear_apply_single {hf' : IsMulCocycle₂ f'} (j : Gal(L/K)) (b : L)
    (m h : Gal(L/K)) :
    rightLinear hf' hF (single hf' j b) m h =
      if m = j * h then incl hF (m⁻¹ (b * ((f' (j, h) : Lˣ) : L))) else 0 := by
  have hiff : (j = m * h⁻¹) ↔ (m = j * h) := by
    constructor
    · rintro rfl
      group
    · rintro rfl
      group
  show rightMatrix hf' hF (single hf' j b) m h = _
  rw [rightMatrix, Matrix.of_apply, toFinsupp_single_apply]
  by_cases hh : m = j * h
  · subst hh
    rw [mul_inv_cancel_right, if_pos rfl, if_pos rfl]
  · rw [if_neg hh, if_neg fun hc => hh (hiff.1 hc), zero_mul, map_zero, map_zero]

/-- The representation of the second crossed product preserves the unit. -/
theorem rightLinear_one (hf' : IsMulCocycle₂ f') :
    rightLinear hf' hF (1 : CrossedProduct hf') = 1 := by
  ext m h
  rw [one_def, rightLinear_apply_single, Matrix.one_apply, one_mul,
    map_one_fst_of_isMulCocycle₂ hf' h, Units.inv_mul, map_one, map_one]

/-- The representation of the second crossed product is multiplicative. -/
theorem rightLinear_mul [FiniteDimensional K L] (hf' : IsMulCocycle₂ f')
    (x y : CrossedProduct hf') :
    rightLinear hf' hF (x * y) = rightLinear hf' hF x * rightLinear hf' hF y := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_mul]
  | single j b =>
    induction y using CrossedProduct.induction_linear with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, mul_add]
    | single j' b' =>
      ext m h
      have hsw : ((f' (j, j' * h) : Lˣ) : L) * j ((f' (j', h) : Lˣ) : L)
          = ((f' (j, j') : Lˣ) : L) * ((f' (j * j', h) : Lˣ) : L) := by
        have h0 := congrArg (Units.val) (cocycle_swap hf' j j' h)
        rw [Units.val_mul, Units.val_mul, val_smul_units] at h0
        exact h0
      rw [Matrix.mul_apply, Finset.sum_eq_single (j⁻¹ * m)]
      · rw [single_mul_single, rightLinear_apply_single, rightLinear_apply_single,
          rightLinear_apply_single, if_pos (by group : m = j * (j⁻¹ * m))]
        by_cases hh : m = j * j' * h
        · have hk : j⁻¹ * m = j' * h := by rw [hh]; group
          have hcomp : ∀ z : L, ((j' * h)⁻¹ : Gal(L/K)) z = (m⁻¹ : Gal(L/K)) (j z) := by
            intro z
            rw [← AlgEquiv.mul_apply]
            congr 1
            rw [hh]
            group
          rw [if_pos hh, hk, if_pos rfl, ← map_mul, hcomp, ← map_mul, map_mul j b']
          congr 2
          linear_combination (-(b * j b')) * hsw
        · rw [if_neg hh, if_neg fun hc => hh (by rw [mul_assoc, ← hc]; group), mul_zero]
      · intro c _ hc
        rw [rightLinear_apply_single, if_neg fun he => hc (by rw [he, inv_mul_cancel_left]),
          zero_mul]
      · intro hb
        exact absurd (Finset.mem_univ (j⁻¹ * m)) hb

/-! ### The two representations commute -/

/-- The matrices attached to the two crossed products commute with each other. -/
theorem leftLinear_mul_rightLinear [FiniteDimensional K L] (hf' : IsMulCocycle₂ f')
    (x : CrossedProduct hf) (y : CrossedProduct hf') :
    leftLinear hf f' hF x * rightLinear hf' hF y
      = rightLinear hf' hF y * leftLinear hf f' hF x := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [map_zero, zero_mul, mul_zero]
  | add p q hp hq => rw [map_add, add_mul, mul_add, hp, hq]
  | single j a =>
    induction y using CrossedProduct.induction_linear with
    | zero => rw [map_zero, mul_zero, zero_mul]
    | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
    | single j' b =>
      ext m h
      obtain ⟨k, rfl⟩ : ∃ k, m = j' * k := ⟨j'⁻¹ * m, by group⟩
      have hLsum : (leftLinear hf f' hF (single hf j a) * rightLinear hf' hF (single hf' j' b))
            (j' * k) h
          = leftLinear hf f' hF (single hf j a) (j' * k) (j' * k * j)
            * rightLinear hf' hF (single hf' j' b) (j' * k * j) h := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_single (j' * k * j) (fun c _ hc => ?_) (fun hc => ?_)
        · rw [leftLinear_apply_single, if_neg hc, zero_mul]
        · exact absurd (Finset.mem_univ (j' * k * j)) hc
      have hRsum : (rightLinear hf' hF (single hf' j' b) * leftLinear hf f' hF (single hf j a))
            (j' * k) h
          = rightLinear hf' hF (single hf' j' b) (j' * k) k
            * leftLinear hf f' hF (single hf j a) k h := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_single k (fun c _ hc => ?_) (fun hc => ?_)
        · rw [rightLinear_apply_single, if_neg fun he => hc (mul_left_cancel he).symm, zero_mul]
        · exact absurd (Finset.mem_univ k) hc
      rw [hLsum, hRsum, leftLinear_apply_single, rightLinear_apply_single,
        rightLinear_apply_single, leftLinear_apply_single, if_pos rfl, if_pos rfl]
      by_cases hh : h = k * j
      · subst hh
        have hcomp : ∀ z : L, j (((j' * k * j)⁻¹ : Gal(L/K)) z) = ((j' * k)⁻¹ : Gal(L/K)) z := by
          intro z
          rw [← AlgEquiv.mul_apply]
          congr 1
          group
        have hsw : ((j' * k)⁻¹ : Gal(L/K)) ((f' (j', k * j) : Lˣ) : L)
              * ((rowScalar f' (j' * k) j : Lˣ) : L)
            = ((j' * k)⁻¹ : Gal(L/K)) ((f' (j', k) : Lˣ) : L)
              * ((rowScalar f' k j : Lˣ) : L) := by
          have h0 := congrArg (Units.val) (rowScalar_swap hf' j' k j)
          rw [Units.val_mul, Units.val_mul, val_smul_units, val_smul_units] at h0
          exact h0
        rw [if_pos (mul_assoc j' k j), if_pos rfl, single_mul_incl', incl_mul_single, hcomp,
          map_mul, map_mul]
        refine single_congr ?_
        linear_combination (((j' * k)⁻¹ : Gal(L/K)) b * a) * hsw
      · have hne : ¬ (j' * k * j = j' * h) := by
          intro he
          exact hh (mul_left_cancel (by rw [← mul_assoc]; exact he)).symm
        rw [if_neg hne, if_neg hh, mul_zero, mul_zero]

end Rep

/-! ### The tensor product of two crossed products -/

section Tensor

variable [DecidableEq Gal(L/K)] [FiniteDimensional K L]

/-- The representation of the first crossed product, as a map of `K`-algebras. -/
noncomputable def leftAlgHom (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (hF : IsMulCocycle₂ F) (hmul : ∀ p, F p = f p * f' p) :
    CrossedProduct hf →ₐ[K] Matrix Gal(L/K) Gal(L/K) (CrossedProduct hF) :=
  AlgHom.ofLinearMap (leftLinear hf f' hF) (leftLinear_one hf' hmul) (leftLinear_mul hf' hmul)

/-- The representation of the second crossed product, as a map of `K`-algebras. -/
noncomputable def rightAlgHom (hf' : IsMulCocycle₂ f') (hF : IsMulCocycle₂ F) :
    CrossedProduct hf' →ₐ[K] Matrix Gal(L/K) Gal(L/K) (CrossedProduct hF) :=
  AlgHom.ofLinearMap (rightLinear hf' hF) (rightLinear_one hf') (rightLinear_mul hf')

/-- The map from the tensor product of two crossed products to the matrix algebra over the
crossed product of the product cocycle. -/
noncomputable def tensorHom (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (hF : IsMulCocycle₂ F) (hmul : ∀ p, F p = f p * f' p) :
    CrossedProduct hf ⊗[K] CrossedProduct hf' →ₐ[K]
      Matrix Gal(L/K) Gal(L/K) (CrossedProduct hF) :=
  Algebra.TensorProduct.lift (leftAlgHom hf hf' hF hmul) (rightAlgHom hf' hF)
    fun x y => leftLinear_mul_rightLinear hf' x y

variable [IsGalois K L]

omit [DecidableEq Gal(L/K)] in
/-- The tensor product of two crossed products and the matrix algebra over the crossed product of
the product cocycle have the same dimension over the base field. -/
theorem finrank_tensor_eq (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (hF : IsMulCocycle₂ F) :
    Module.finrank K (CrossedProduct hf ⊗[K] CrossedProduct hf')
      = Module.finrank K (Matrix Gal(L/K) Gal(L/K) (CrossedProduct hF)) := by
  rw [Module.finrank_tensorProduct, Module.finrank_matrix, finrank_eq, finrank_eq, finrank_eq,
    Nat.card_eq_fintype_card]
  ring

/-- The map from the tensor product of two crossed products to the matrix algebra is bijective. -/
theorem tensorHom_bijective (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (hF : IsMulCocycle₂ F) (hmul : ∀ p, F p = f p * f' p) :
    Function.Bijective (tensorHom hf hf' hF hmul) := by
  haveI : IsSimpleRing (CrossedProduct hf ⊗[K] CrossedProduct hf') :=
    IsSimpleRing.tensorProduct_of_isCentral
  have hinj : Function.Injective (tensorHom hf hf' hF hmul) :=
    (tensorHom hf hf' hF hmul : CrossedProduct hf ⊗[K] CrossedProduct hf' →+*
      Matrix Gal(L/K) Gal(L/K) (CrossedProduct hF)).injective
  refine ⟨hinj, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_tensor_eq hf hf' hF)).mp ?_
  exact hinj

/-- **The tensor product of two crossed products** of the same Galois extension is the matrix
algebra, of size the degree of the extension, over the crossed product of the product cocycle. -/
noncomputable def tensorAlgEquiv (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (hF : IsMulCocycle₂ F) (hmul : ∀ p, F p = f p * f' p) :
    CrossedProduct hf ⊗[K] CrossedProduct hf' ≃ₐ[K]
      Matrix Gal(L/K) Gal(L/K) (CrossedProduct hF) :=
  AlgEquiv.ofBijective (tensorHom hf hf' hF hmul) (tensorHom_bijective hf hf' hF hmul)

/-- The tensor product of two crossed products, as a matrix algebra indexed by a standard finite
type. -/
noncomputable def tensorAlgEquivFin (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (hF : IsMulCocycle₂ F) (hmul : ∀ p, F p = f p * f' p) :
    CrossedProduct hf ⊗[K] CrossedProduct hf' ≃ₐ[K]
      Matrix (Fin (Fintype.card Gal(L/K))) (Fin (Fintype.card Gal(L/K))) (CrossedProduct hF) :=
  (tensorAlgEquiv hf hf' hF hmul).trans
    (Matrix.reindexAlgEquiv K _ (Fintype.equivFin Gal(L/K)))

end Tensor

/-- **The crossed-product construction turns multiplication of cocycles into multiplication in
the Brauer group.** -/
theorem mk_csa_mul [FiniteDimensional K L] [IsGalois K L]
    (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    (⟦csa (isMulCocycle₂_mul hf hf')⟧ : BrauerGroup K) = ⟦csa hf⟧ * ⟦csa hf'⟧ := by
  classical
  rw [BrauerGroup.mk_mul]
  refine (Quotient.sound ?_).symm
  exact IsBrauerEquivalent.of_algEquiv_matrix (n := Fintype.card Gal(L/K)) Fintype.card_ne_zero
    (tensorAlgEquivFin hf hf' (isMulCocycle₂_mul hf hf') fun _ => rfl)

end CrossedProduct

end InverseGalois.CFT
