import Mathlib
import InverseGalois.CFT.Brauer.SkolemNoether

/-!
# The semilinear Skolem–Noether theorem

Let `L / K` be a field extension and let `σ : L ≃ₐ[K] L` be an automorphism of `L` over `K`.
Call a ring homomorphism `ψ : Matrix n n L →+* Matrix n n L` *`σ`-semilinear* if
`ψ (c • M) = σ c • ψ M` for every scalar `c : L`.

This file shows that every `σ`-semilinear ring endomorphism of a matrix algebra over `L` is
conjugation by a unit composed with the entrywise application of `σ`, and that the conjugating
unit is unique up to a scalar.

This is the computation behind the surjectivity of the crossed-product map
`H²(Gal(L/K), Lˣ) → Br(L/K)`: a splitting of a central simple algebra produces, for each
`σ`, a `σ`-semilinear automorphism of a matrix algebra, and the units provided below assemble
into a `2`-cocycle whose class is well defined precisely because of the uniqueness statement.

## Main results

* `InverseGalois.CFT.matrixMap`: entrywise application of an automorphism of `L`, packaged as a
  ring automorphism of `Matrix n n L`.
* `InverseGalois.CFT.semilinearUntwist`: the honest `L`-algebra endomorphism attached to a
  `σ`-semilinear ring endomorphism, obtained by applying `σ⁻¹` to all the values.
* `InverseGalois.CFT.exists_units_semilinear_conj`: **semilinear Skolem–Noether**, in the form
  `ψ M = g * M.map σ * g⁻¹`.
* `InverseGalois.CFT.exists_units_semilinear_conj_mul`: the same statement written without an
  inverse, as `ψ M * g = g * M.map σ`.
* `InverseGalois.CFT.exists_units_semilinear_conj_of_ringEquiv`: the version for a ring
  automorphism.
* `InverseGalois.CFT.exists_smul_eq_of_semilinear_conj`: the conjugating unit is unique up to a
  scalar in `Lˣ`.
* `InverseGalois.CFT.bijective_of_semilinear`: a `σ`-semilinear ring endomorphism of a matrix
  algebra is automatically bijective.
* `InverseGalois.CFT.basisSemilinear`: coordinatewise application of `σ` in a basis, a
  `σ`-semilinear additive automorphism of the underlying vector space.
* `InverseGalois.CFT.exists_addEquiv_semilinear_conj_end`: the endomorphism-algebra form of the
  theorem, `ψ f x = h (f (h⁻¹ x))` for a `σ`-semilinear additive automorphism `h` of `V`.
-/

namespace InverseGalois.CFT

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Entrywise application of an automorphism of the coefficients -/

/-- Entrywise application of a `K`-algebra automorphism `σ` of `L`, as a ring automorphism of
the matrix algebra `Matrix n n L`. -/
def matrixMap (σ : L ≃ₐ[K] L) : Matrix n n L ≃+* Matrix n n L :=
  RingEquiv.mapMatrix σ.toRingEquiv

/-- `matrixMap σ` is entrywise application of `σ`. -/
@[simp]
theorem matrixMap_apply (σ : L ≃ₐ[K] L) (M : Matrix n n L) :
    matrixMap (n := n) σ M = M.map σ := rfl

/-- The inverse of `matrixMap σ` is `matrixMap σ⁻¹`. -/
@[simp]
theorem matrixMap_symm (σ : L ≃ₐ[K] L) :
    (matrixMap (n := n) σ).symm = matrixMap (n := n) σ.symm := rfl

/-- Entrywise application of `σ` turns scaling by `c` into scaling by `σ c`. -/
theorem matrixMap_smul (σ : L ≃ₐ[K] L) (c : L) (M : Matrix n n L) :
    matrixMap (n := n) σ (c • M) = σ c • matrixMap (n := n) σ M := by
  ext i j
  simp

omit [Fintype n] [DecidableEq n] in
/-- Applying `σ` and then `σ⁻¹` entrywise is the identity on matrices. -/
@[simp]
theorem map_symm_map (σ : L ≃ₐ[K] L) (M : Matrix n n L) : (M.map σ).map σ.symm = M := by
  ext i j
  simp

omit [Fintype n] [DecidableEq n] in
/-- Applying `σ⁻¹` and then `σ` entrywise is the identity on matrices. -/
@[simp]
theorem map_map_symm (σ : L ≃ₐ[K] L) (M : Matrix n n L) : (M.map σ.symm).map σ = M := by
  ext i j
  simp

/-! ### Untwisting a semilinear endomorphism -/

/-- Given a `σ`-semilinear ring endomorphism `ψ` of `Matrix n n L`, applying `σ⁻¹` entrywise to
all of its values produces an honest `L`-algebra endomorphism of `Matrix n n L`. -/
def semilinearUntwist (σ : L ≃ₐ[K] L) (ψ : Matrix n n L →+* Matrix n n L)
    (hψ : ∀ (c : L) (M : Matrix n n L), ψ (c • M) = σ c • ψ M) :
    Matrix n n L →ₐ[L] Matrix n n L :=
  { (matrixMap (n := n) σ.symm).toRingHom.comp ψ with
    commutes' := fun r => by
      have h1 : (algebraMap L (Matrix n n L)) r = r • (1 : Matrix n n L) :=
        Algebra.algebraMap_eq_smul_one r
      show matrixMap (n := n) σ.symm (ψ ((algebraMap L (Matrix n n L)) r)) = _
      rw [h1, hψ, map_one, matrixMap_smul]
      simp }

/-- The values of `semilinearUntwist σ ψ hψ` are those of `ψ` with `σ⁻¹` applied entrywise. -/
@[simp]
theorem semilinearUntwist_apply (σ : L ≃ₐ[K] L) (ψ : Matrix n n L →+* Matrix n n L)
    (hψ : ∀ (c : L) (M : Matrix n n L), ψ (c • M) = σ c • ψ M) (M : Matrix n n L) :
    semilinearUntwist σ ψ hψ M = (ψ M).map σ.symm := rfl

/-! ### The theorem -/

/-- **Semilinear Skolem–Noether**. A `σ`-semilinear ring endomorphism of a matrix algebra over
`L` is the entrywise application of `σ` followed by conjugation by a unit. -/
theorem exists_units_semilinear_conj [Nonempty n] (σ : L ≃ₐ[K] L)
    (ψ : Matrix n n L →+* Matrix n n L)
    (hψ : ∀ (c : L) (M : Matrix n n L), ψ (c • M) = σ c • ψ M) :
    ∃ g : (Matrix n n L)ˣ, ∀ M : Matrix n n L,
      ψ M = (g : Matrix n n L) * M.map σ * ((g⁻¹ : (Matrix n n L)ˣ) : Matrix n n L) := by
  obtain ⟨u, hu⟩ := SkolemNoether.exists_conj_of_algHom_self (semilinearUntwist σ ψ hψ)
  refine ⟨Units.map (matrixMap (n := n) σ).toRingHom.toMonoidHom u, fun M => ?_⟩
  have hE : matrixMap (n := n) σ (semilinearUntwist σ ψ hψ M) = ψ M := by
    show ((ψ M).map σ.symm).map σ = ψ M
    exact map_map_symm σ (ψ M)
  rw [← hE, hu M]
  simp [map_mul]

/-- The conclusion of `exists_units_semilinear_conj` written without an inverse. -/
theorem exists_units_semilinear_conj_mul [Nonempty n] (σ : L ≃ₐ[K] L)
    (ψ : Matrix n n L →+* Matrix n n L)
    (hψ : ∀ (c : L) (M : Matrix n n L), ψ (c • M) = σ c • ψ M) :
    ∃ g : (Matrix n n L)ˣ, ∀ M : Matrix n n L,
      ψ M * (g : Matrix n n L) = (g : Matrix n n L) * M.map σ := by
  obtain ⟨g, hg⟩ := exists_units_semilinear_conj σ ψ hψ
  refine ⟨g, fun M => ?_⟩
  rw [hg M, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

/-- The version of semilinear Skolem–Noether for a ring *automorphism* of the matrix algebra. -/
theorem exists_units_semilinear_conj_of_ringEquiv [Nonempty n] (σ : L ≃ₐ[K] L)
    (ψ : Matrix n n L ≃+* Matrix n n L)
    (hψ : ∀ (c : L) (M : Matrix n n L), ψ (c • M) = σ c • ψ M) :
    ∃ g : (Matrix n n L)ˣ, ∀ M : Matrix n n L,
      ψ M = (g : Matrix n n L) * M.map σ * ((g⁻¹ : (Matrix n n L)ˣ) : Matrix n n L) :=
  exists_units_semilinear_conj σ ψ.toRingHom hψ

/-- A `σ`-semilinear ring endomorphism of a matrix algebra over `L` is automatically
bijective. -/
theorem bijective_of_semilinear [Nonempty n] (σ : L ≃ₐ[K] L)
    (ψ : Matrix n n L →+* Matrix n n L)
    (hψ : ∀ (c : L) (M : Matrix n n L), ψ (c • M) = σ c • ψ M) :
    Function.Bijective ψ := by
  obtain ⟨g, hg⟩ := exists_units_semilinear_conj σ ψ hψ
  have hfun : ⇑ψ = fun M : Matrix n n L =>
      (g : Matrix n n L) * (matrixMap (n := n) σ M) * ((g⁻¹ : (Matrix n n L)ˣ) : Matrix n n L) :=
    funext hg
  rw [hfun]
  have : Function.Bijective
      (fun M : Matrix n n L => (g : Matrix n n L) * M * ((g⁻¹ : (Matrix n n L)ˣ) : Matrix n n L)) :=
    ⟨fun M N h => by
      have := congrArg (fun X => ((g⁻¹ : (Matrix n n L)ˣ) : Matrix n n L) * X *
        (g : Matrix n n L)) h
      simpa [mul_assoc, ← Units.val_mul] using this,
     fun N => ⟨((g⁻¹ : (Matrix n n L)ˣ) : Matrix n n L) * N * (g : Matrix n n L), by
      simp [mul_assoc]⟩⟩
  exact this.comp (matrixMap (n := n) σ).bijective

/-! ### Uniqueness of the conjugating unit -/

/-- Two units implementing the same `σ`-semilinear map differ by a scalar in `Lˣ`. -/
theorem exists_smul_eq_of_semilinear_conj [Nonempty n] (σ : L ≃ₐ[K] L)
    {ψ : Matrix n n L → Matrix n n L} {g g' : (Matrix n n L)ˣ}
    (hg : ∀ M : Matrix n n L,
      ψ M = (g : Matrix n n L) * M.map σ * ((g⁻¹ : (Matrix n n L)ˣ) : Matrix n n L))
    (hg' : ∀ M : Matrix n n L,
      ψ M = (g' : Matrix n n L) * M.map σ * ((g'⁻¹ : (Matrix n n L)ˣ) : Matrix n n L)) :
    ∃ c : Lˣ, (g' : Matrix n n L) = (c : L) • (g : Matrix n n L) := by
  have hconj : ∀ N : Matrix n n L, (g : Matrix n n L) * N *
      ((g⁻¹ : (Matrix n n L)ˣ) : Matrix n n L) =
      (g' : Matrix n n L) * N * ((g'⁻¹ : (Matrix n n L)ˣ) : Matrix n n L) := by
    intro N
    have h := (hg (N.map σ.symm)).symm.trans (hg' (N.map σ.symm))
    rwa [map_map_symm] at h
  have hcomm : ∀ N : Matrix n n L,
      N * ((g'⁻¹ * g : (Matrix n n L)ˣ) : Matrix n n L) =
        ((g'⁻¹ * g : (Matrix n n L)ˣ) : Matrix n n L) * N := by
    intro N
    have h1 := congrArg (fun X => ((g'⁻¹ : (Matrix n n L)ˣ) : Matrix n n L) * X *
      (g : Matrix n n L)) (hconj N)
    simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left] at h1
    simp only [Units.val_mul, mul_assoc]
    exact h1.symm
  have hmem : ((g'⁻¹ * g : (Matrix n n L)ˣ) : Matrix n n L) ∈ Set.center (Matrix n n L) :=
    Semigroup.mem_center_iff.2 fun N => hcomm N
  rw [Matrix.center_eq_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hscalar : Matrix.scalar n c = c • (1 : Matrix n n L) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  have hc0 : c ≠ 0 := by
    intro h
    have h1 : ((g'⁻¹ * g : (Matrix n n L)ˣ) : Matrix n n L) = 0 := by
      rw [← hc, hscalar, h, zero_smul]
    have h2 := (g'⁻¹ * g).mul_inv
    rw [h1, zero_mul] at h2
    exact zero_ne_one h2
  have hgg : (g : Matrix n n L) = c • (g' : Matrix n n L) := by
    have hgv : (g' : Matrix n n L) * ((g'⁻¹ * g : (Matrix n n L)ˣ) : Matrix n n L) =
        (g : Matrix n n L) := by
      rw [← Units.val_mul, mul_inv_cancel_left]
    rw [← hgv, ← hc, hscalar, Matrix.mul_smul, mul_one]
  refine ⟨(Units.mk0 c hc0)⁻¹, ?_⟩
  rw [hgg, Units.val_inv_eq_inv_val, Units.val_mk0, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-! ### The endomorphism-algebra version -/

section End

variable {V : Type*} [AddCommGroup V] [Module L V]

/-- Coordinatewise application of `σ` in a basis `b`, as an additive automorphism of the
underlying vector space. It is `σ`-semilinear, not `L`-linear. -/
noncomputable def basisSemilinear (σ : L ≃ₐ[K] L) (b : Module.Basis n L V) : V ≃+ V :=
  (b.repr.toAddEquiv.trans (Finsupp.mapRange.addEquiv σ.toAddEquiv)).trans b.repr.symm.toAddEquiv

omit [Fintype n] [DecidableEq n] in
/-- The coordinates of `basisSemilinear σ b x` are the images under `σ` of those of `x`. -/
@[simp]
theorem repr_basisSemilinear (σ : L ≃ₐ[K] L) (b : Module.Basis n L V) (x : V) (i : n) :
    b.repr (basisSemilinear σ b x) i = σ (b.repr x i) := by
  simp [basisSemilinear]

omit [Fintype n] [DecidableEq n] in
/-- The coordinates of the inverse of `basisSemilinear σ b` are given by `σ⁻¹`. -/
@[simp]
theorem repr_basisSemilinear_symm (σ : L ≃ₐ[K] L) (b : Module.Basis n L V) (x : V) (i : n) :
    b.repr ((basisSemilinear σ b).symm x) i = σ.symm (b.repr x i) := by
  simp [basisSemilinear]

omit [Fintype n] [DecidableEq n] in
/-- `basisSemilinear σ b` is `σ`-semilinear. -/
theorem basisSemilinear_smul (σ : L ≃ₐ[K] L) (b : Module.Basis n L V) (c : L) (x : V) :
    basisSemilinear σ b (c • x) = σ c • basisSemilinear σ b x := by
  apply b.repr.injective
  ext i
  simp

/-- Conjugating an `L`-linear endomorphism by the coordinatewise `σ` applies `σ` entrywise to
its matrix. -/
theorem basisSemilinear_conj (σ : L ≃ₐ[K] L) (b : Module.Basis n L V) (f : Module.End L V) (x : V) :
    basisSemilinear σ b (f ((basisSemilinear σ b).symm x)) =
      Matrix.toLinAlgEquiv b ((LinearMap.toMatrixAlgEquiv b f).map σ) x := by
  apply b.repr.injective
  ext i
  have hL : b.repr (f ((basisSemilinear σ b).symm x)) i =
      ∑ j, LinearMap.toMatrix b b f i j * σ.symm (b.repr x j) := by
    rw [← LinearMap.toMatrix_mulVec_repr b b f ((basisSemilinear σ b).symm x)]
    simp [Matrix.mulVec, dotProduct]
  have hR : b.repr (Matrix.toLinAlgEquiv b ((LinearMap.toMatrixAlgEquiv b f).map σ) x) i =
      ∑ j, σ (LinearMap.toMatrix b b f i j) * b.repr x j := by
    show b.repr (Matrix.toLin b b ((LinearMap.toMatrixAlgEquiv b f).map σ) x) i = _
    rw [Matrix.repr_toLin]
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, LinearMap.toMatrixAlgEquiv,
      LinearMap.toMatrix]
  rw [repr_basisSemilinear, hL, hR, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- **Semilinear Skolem–Noether for endomorphism algebras**. A `σ`-semilinear ring endomorphism
of `Module.End L V`, for a nonzero finite-dimensional `L`-vector space `V`, is conjugation by a
`σ`-semilinear additive automorphism of `V`. -/
theorem exists_addEquiv_semilinear_conj_end [FiniteDimensional L V] [Nontrivial V]
    (σ : L ≃ₐ[K] L) (ψ : Module.End L V →+* Module.End L V)
    (hψ : ∀ (c : L) (f : Module.End L V), ψ (c • f) = σ c • ψ f) :
    ∃ h : V ≃+ V, (∀ (c : L) (x : V), h (c • x) = σ c • h x) ∧
      ∀ (f : Module.End L V) (x : V), ψ f x = h (f (h.symm x)) := by
  haveI : Nonempty (Fin (Module.finrank L V)) := Fin.pos_iff_nonempty.1 Module.finrank_pos
  set b := Module.finBasis L V with hb
  set E := LinearMap.toMatrixAlgEquiv b with hE
  set ψ' : Matrix (Fin (Module.finrank L V)) (Fin (Module.finrank L V)) L →+*
      Matrix (Fin (Module.finrank L V)) (Fin (Module.finrank L V)) L :=
    E.toAlgHom.toRingHom.comp (ψ.comp E.symm.toAlgHom.toRingHom) with hψ'def
  have hψ' : ∀ (c : L) (M : Matrix (Fin (Module.finrank L V)) (Fin (Module.finrank L V)) L),
      ψ' (c • M) = σ c • ψ' M := by
    intro c M
    show E (ψ (E.symm (c • M))) = σ c • E (ψ (E.symm M))
    rw [map_smul, hψ, map_smul]
  obtain ⟨g, hg⟩ := exists_units_semilinear_conj σ ψ' hψ'
  set G : (Module.End L V)ˣ := Units.map E.symm.toAlgHom.toRingHom.toMonoidHom g with hG
  set hGe : V ≃ₗ[L] V := LinearMap.GeneralLinearGroup.toLinearEquiv G with hGe_def
  refine ⟨(basisSemilinear σ b).trans hGe.toAddEquiv, fun c x => ?_, fun f x => ?_⟩
  · show hGe (basisSemilinear σ b (c • x)) = σ c • hGe (basisSemilinear σ b x)
    rw [basisSemilinear_smul, map_smul]
  · show ψ f x = hGe (basisSemilinear σ b (f ((basisSemilinear σ b).symm (hGe.symm x))))
    rw [basisSemilinear_conj]
    have hfx : ψ f = E.symm (ψ' (E f)) := by
      show ψ f = E.symm (E (ψ (E.symm (E f))))
      simp
    have hsplit : E.symm (ψ' (E f)) =
        (G : Module.End L V) * Matrix.toLinAlgEquiv b ((E f).map σ) *
          ((G⁻¹ : (Module.End L V)ˣ) : Module.End L V) := by
      rw [hg (E f)]
      simp only [hG, map_mul, Units.coe_map, Units.coe_map_inv]
      rfl
    rw [hfx, hsplit]
    show (G : Module.End L V) ((Matrix.toLinAlgEquiv b ((E f).map σ))
      (((G⁻¹ : (Module.End L V)ˣ) : Module.End L V) x)) = _
    rfl

end End

end InverseGalois.CFT
