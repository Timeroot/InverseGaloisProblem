/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity

/-!
# The general linear group as a regular Galois group

`GL ι R` is never centerless: the scalar matrices are central, so the rigidity criterion
(`Rigidity.RigidityCertificate`, which stores `center_triv`) can never be applied to it directly.
What can be applied to it is the *structure* of the group: the scalars split off.

The determinant `GL ι R → Rˣ` restricted to the scalars `u ↦ u • 1` is the power map
`u ↦ u ^ card ι`.  When that power map is bijective — over a finite field `F` with `|F| = q` and
`|ι| = n` this says exactly `gcd (n, q - 1) = 1` — multiplication

`SL ι R × Rˣ → GL ι R`,  `(A, u) ↦ A ⬝ (u • 1)`

is an isomorphism.  So in the coprime case `GL` is a *direct* product of its special linear
subgroup and a finite cyclic group, and realizing it regularly over `ℚ(T)` splits into realizing
each factor and multiplying.

Two members of the family need nothing further.  For `n = 1` the special linear group is trivial
and `GL` is the finite abelian group `Rˣ`.  For `q = 2` the unit group is trivial and `GL` *is*
`SL`, which for `n ≥ 3` is the simple group `PSL ι 𝔽₂` — the one shape in which a general linear
group over a finite field is centerless.

## Main definitions

* `Matrix.GeneralLinearGroup.slUnitsHom` — the multiplication map `SL ι R × Rˣ →* GL ι R`.
* `Matrix.GeneralLinearGroup.mulEquivProdUnits` — that map as an isomorphism, when the
  `card ι`-th power map on `Rˣ` is bijective.

## Main results

* `Matrix.GeneralLinearGroup.bijective_pow_units` — over a finite field the `n`-th power map on
  units is bijective exactly when `n` is coprime to `q - 1`.
* `Rigidity.isRegularInverseGalois_generalLinearGroup_of_prod` — the coprime reduction: a regular
  realization of `SL ι F × Fˣ` is one of `GL ι F`.
* `Rigidity.isRegularInverseGalois_generalLinearGroup_of_specialLinearGroup` — the same reduction
  carried out: for perfect `SL ι F`, a regular realization of `SL ι F` alone suffices.
* `Rigidity.isRegularInverseGalois_generalLinearGroup_one` — `GL₁` over any finite field.
* `Rigidity.isRegularInverseGalois_generalLinearGroup_of_specialLinearGroup_two` — over `𝔽₂` the
  general and special linear groups coincide.
* `Rigidity.permMulEquivGLTwo` — `GL₂(𝔽₂)` is the symmetric group on the three nonzero vectors.
* `Rigidity.isRegularInverseGalois_generalLinearGroup_two_two` — `GL₂(𝔽₂)` over `ℚ(T)`.
-/

open Matrix

noncomputable section

namespace Matrix.GeneralLinearGroup

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*} [CommRing R]

/-! ## Scalars are central -/

/-- The underlying matrix of a scalar element of the general linear group. -/
@[simp]
theorem coe_scalar (u : Rˣ) :
    ((GeneralLinearGroup.scalar ι u : GL ι R) : Matrix ι ι R) = Matrix.scalar ι (u : R) :=
  rfl

/-- **Scalar matrices are central in the general linear group.** -/
theorem commute_scalar (u : Rˣ) (M : GL ι R) :
    Commute (GeneralLinearGroup.scalar ι u) M := by
  refine Units.ext ?_
  exact Matrix.scalar_commute (u : R) (fun r' => Commute.all _ r') (M : Matrix ι ι R)

/-! ## The multiplication map `SL × units → GL` -/

/-- **Multiplication of a special linear matrix by a scalar**, as a group homomorphism
`SL ι R × Rˣ →* GL ι R`.  It is a homomorphism because the scalars are central. -/
def slUnitsHom : SpecialLinearGroup ι R × Rˣ →* GL ι R :=
  MonoidHom.noncommCoprod SpecialLinearGroup.toGL (GeneralLinearGroup.scalar ι)
    fun A u => (commute_scalar u (SpecialLinearGroup.toGL A)).symm

@[simp]
theorem slUnitsHom_apply (A : SpecialLinearGroup ι R) (u : Rˣ) :
    slUnitsHom (A, u) = SpecialLinearGroup.toGL A * GeneralLinearGroup.scalar ι u :=
  rfl

/-- The determinant of `A ⬝ (u • 1)` is `u ^ card ι`: the special linear factor contributes
nothing, and the scalar contributes its `card ι`-th power. -/
@[simp]
theorem det_slUnitsHom (A : SpecialLinearGroup ι R) (u : Rˣ) :
    GeneralLinearGroup.det (slUnitsHom (A, u)) = u ^ Fintype.card ι := by
  rw [slUnitsHom_apply, map_mul, SpecialLinearGroup.coeToGL_det, GeneralLinearGroup.det_scalar,
    one_mul]

/-- **An invertible matrix of determinant one is a special linear matrix.** -/
theorem exists_toGL_eq {M : GL ι R} (h : GeneralLinearGroup.det M = 1) :
    ∃ A : SpecialLinearGroup ι R, SpecialLinearGroup.toGL A = M := by
  refine ⟨⟨(M : Matrix ι ι R), ?_⟩, Units.ext rfl⟩
  exact congrArg Units.val h

/-! ## The isomorphism in the coprime case -/

variable (hinj : Function.Injective fun u : Rˣ => u ^ Fintype.card ι)

include hinj in
/-- If no nontrivial unit has trivial `card ι`-th power, multiplication by scalars is injective:
a product `A ⬝ (u • 1)` that is the identity has determinant `u ^ card ι = 1`, hence `u = 1`, and
then `A = 1`. -/
theorem slUnitsHom_injective :
    Function.Injective (slUnitsHom : SpecialLinearGroup ι R × Rˣ →* GL ι R) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, u⟩ h
  have hu : u ^ Fintype.card ι = (1 : Rˣ) ^ Fintype.card ι := by
    rw [one_pow, ← det_slUnitsHom A u, h, map_one]
  have hu1 : u = 1 := hinj hu
  subst hu1
  rw [slUnitsHom_apply, map_one, mul_one] at h
  have : A = 1 := SpecialLinearGroup.toGL_injective (by rw [h, map_one])
  simp [this]

/-- If every unit is a `card ι`-th power, every invertible matrix is a special linear matrix times
a scalar: divide by a scalar whose `card ι`-th power is the determinant. -/
theorem slUnitsHom_surjective (hsurj : Function.Surjective fun u : Rˣ => u ^ Fintype.card ι) :
    Function.Surjective (slUnitsHom : SpecialLinearGroup ι R × Rˣ →* GL ι R) := by
  intro M
  obtain ⟨u, hu⟩ := hsurj (GeneralLinearGroup.det M)
  have hu' : u ^ Fintype.card ι = GeneralLinearGroup.det M := hu
  have hdet : GeneralLinearGroup.det (M * (GeneralLinearGroup.scalar ι u)⁻¹) = 1 := by
    rw [map_mul, map_inv, GeneralLinearGroup.det_scalar, hu', mul_inv_cancel]
  obtain ⟨A, hA⟩ := exists_toGL_eq hdet
  refine ⟨(A, u), ?_⟩
  rw [slUnitsHom_apply, hA, inv_mul_cancel_right]

/-- **The general linear group splits as `SL × units`** whenever the `card ι`-th power map on the
units is bijective.  Over a finite field with `q` elements and `card ι = n` this is exactly the
condition `gcd (n, q - 1) = 1`. -/
def mulEquivProdUnits (hbij : Function.Bijective fun u : Rˣ => u ^ Fintype.card ι) :
    SpecialLinearGroup ι R × Rˣ ≃* GL ι R :=
  MulEquiv.ofBijective slUnitsHom ⟨slUnitsHom_injective hbij.1, slUnitsHom_surjective hbij.2⟩

/-! ## The finite field criterion -/

/-- **Over a finite field the `n`-th power map on units is bijective when `n` is coprime to
`q - 1`.**  The unit group has order `q - 1`, and raising to a power coprime to the order of a
finite group is a bijection. -/
theorem bijective_pow_units {F : Type*} [Field F] [Finite F] {N : ℕ}
    (h : (Nat.card Fˣ).Coprime N) : Function.Bijective fun u : Fˣ => u ^ N :=
  (powCoprime h).bijective

end Matrix.GeneralLinearGroup

/-! ## Regular realizations -/

namespace Rigidity

open Matrix.GeneralLinearGroup

variable {ι : Type} [DecidableEq ι] [Fintype ι] {F : Type} [Field F] [Finite F]

/-- **The coprime reduction for the general linear group.**  When `card ι` is coprime to `q - 1`
the group `GL ι F` is the direct product of `SL ι F` with the cyclic group `Fˣ`, so a regular
realization of that product is a regular realization of `GL ι F`. -/
theorem isRegularInverseGalois_generalLinearGroup_of_prod
    (hcop : (Nat.card Fˣ).Coprime (Fintype.card ι))
    (h : IsRegularInverseGalois (SpecialLinearGroup ι F × Fˣ)) :
    IsRegularInverseGalois (GL ι F) :=
  h.of_mulEquiv (mulEquivProdUnits (bijective_pow_units hcop))

/-- **The general linear group over a finite field, in the coprime case.**  When `card ι` is
coprime to `q - 1` the group is `SL ι F × Fˣ`, and a perfect group and an abelian group have no
common quotient, so `IsRegularInverseGalois.prod_of_perfect` assembles a regular realization of
the product out of one of `SL ι F` — the order of `Fˣ` divides that of `SL ι F` for `card ι ≥ 2`,
so the coprime-order product theorem is of no use here. -/
theorem isRegularInverseGalois_generalLinearGroup_of_specialLinearGroup
    (hcop : (Nat.card Fˣ).Coprime (Fintype.card ι))
    (hperf : commutator (SpecialLinearGroup ι F) = ⊤)
    (h : IsRegularInverseGalois (SpecialLinearGroup ι F)) :
    IsRegularInverseGalois (GL ι F) :=
  isRegularInverseGalois_generalLinearGroup_of_prod hcop
    (h.prod_of_perfect (RET.IsRegularInverseGalois.of_commGroup Fˣ) hperf)

/-! ### The two families that need nothing further -/

/-- A `1 × 1` matrix of determinant one is the identity. -/
instance : Subsingleton (SpecialLinearGroup (Fin 1) F) := by
  refine ⟨fun A B => ?_⟩
  have h : ∀ C : SpecialLinearGroup (Fin 1) F, (C : Matrix (Fin 1) (Fin 1) F) = 1 := by
    intro C
    have hC : (C : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
      rw [← Matrix.det_fin_one (C : Matrix (Fin 1) (Fin 1) F)]
      exact C.2
    ext i j
    fin_cases i
    fin_cases j
    simpa using hC
  exact Subtype.ext ((h A).trans (h B).symm)

instance : Unique (SpecialLinearGroup (Fin 1) F) := Unique.mk' _

/-- **`GL₁` over a finite field is a regular Galois group over `ℚ(T)`.**  It is the unit group of
the field — a finite abelian group — so the abelian realization applies. -/
theorem isRegularInverseGalois_generalLinearGroup_one :
    IsRegularInverseGalois (GL (Fin 1) F) := by
  have hcop : (Nat.card Fˣ).Coprime (Fintype.card (Fin 1)) := by
    simp
  refine isRegularInverseGalois_generalLinearGroup_of_prod hcop ?_
  exact (RET.IsRegularInverseGalois.of_commGroup Fˣ).of_mulEquiv MulEquiv.uniqueProd.symm

/-- **Over a field with trivial unit group the general and special linear groups agree.**  This is
the case `q = 2`, where `GL ι 𝔽₂ = SL ι 𝔽₂` is centerless. -/
def mulEquivSpecialLinearGroup [Subsingleton Fˣ] :
    SpecialLinearGroup ι F ≃* GL ι F :=
  letI : Unique Fˣ := Unique.mk' _
  MulEquiv.prodUnique.symm.trans
    (mulEquivProdUnits ⟨fun a b _ => Subsingleton.elim a b,
      fun _u => ⟨1, Subsingleton.elim _ _⟩⟩)

omit [Finite F] in
/-- **Over a field with trivial unit group a regular realization of `SL` is one of `GL`.** -/
theorem isRegularInverseGalois_generalLinearGroup_of_specialLinearGroup_two [Subsingleton Fˣ]
    (h : IsRegularInverseGalois (SpecialLinearGroup ι F)) :
    IsRegularInverseGalois (GL ι F) :=
  h.of_mulEquiv mulEquivSpecialLinearGroup

/-! ### `GL₂(𝔽₂)` -/

/-- The three nonzero vectors of `𝔽₂²`, indexed so that the last is the sum of the first two. -/
def nonzeroVecTwo : Fin 3 → (Fin 2 → ZMod 2) := ![![1, 0], ![0, 1], ![1, 1]]

/-- The `𝔽₂`-linear map sending the `j`-th standard basis vector to the `σ j`-th nonzero vector.
Because the third nonzero vector is the sum of the other two, this map permutes all three of them
according to `σ`, which is what makes `σ ↦ permMatrixTwo σ` multiplicative. -/
def permMatrixTwo (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j => nonzeroVecTwo (σ j.castSucc) i

/-- **The symmetric group on the three nonzero vectors of `𝔽₂²`, as invertible matrices.** -/
def permToGLTwo : Equiv.Perm (Fin 3) →* GL (Fin 2) (ZMod 2) where
  toFun σ := ⟨permMatrixTwo σ, permMatrixTwo σ⁻¹, by revert σ; decide, by revert σ; decide⟩
  map_one' := Units.ext (by decide)
  map_mul' σ τ := Units.ext (by revert σ τ; decide)

/-- A matrix is determined by where it sends the two standard basis vectors, and there are `6`
invertible `2 × 2` matrices over `𝔽₂`. -/
theorem permToGLTwo_bijective : Function.Bijective permToGLTwo := by
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · intro σ τ h
    have h' : permMatrixTwo σ = permMatrixTwo τ := congrArg Units.val h
    revert h'
    revert σ τ
    decide
  · have hGL : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
      rw [Matrix.card_GL_field]
      simp [Fin.prod_univ_two, ZMod.card]
    rw [hGL, Nat.card_eq_fintype_card]
    decide

/-- **`GL₂(𝔽₂)` is the symmetric group on three letters.** -/
def permMulEquivGLTwo : Equiv.Perm (Fin 3) ≃* GL (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective permToGLTwo permToGLTwo_bijective

/-- **`GL₂(𝔽₂)` is a regular Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_generalLinearGroup_two_two :
    IsRegularInverseGalois (GL (Fin 2) (ZMod 2)) :=
  (RET.isRegularInverseGalois_perm_fin 3).of_mulEquiv permMulEquivGLTwo

end Rigidity
