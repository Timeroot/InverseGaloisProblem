/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicTower
import InverseGalois.CFT.Brauer.CrossedProductSplit
import InverseGalois.CFT.Brauer.H2Brauer

/-!
# Crossed products of an inflated cocycle

Let `K ⊆ L ⊆ L'` be a tower of fields with `L / K` and `L' / K` finite Galois.  Restriction of
automorphisms is a homomorphism `Gal(L'/K) → Gal(L/K)`, and composing a multiplicative `2`-cocycle
of `Gal(L/K)` with values in `Lˣ` with that homomorphism and with the inclusion of `Lˣ` into `L'ˣ`
produces a multiplicative `2`-cocycle of `Gal(L'/K)` with values in `L'ˣ`, its inflation.  The two
cocycles have the same class in the Brauer group of `K`.

The comparison is completely explicit.  Choose an `L`-basis `b` of `L'`.  Multiplication by an
element of `L'` and the semilinear action of an automorphism `σ` of `L'` are both recorded by
matrices over `L` in that basis, and inside the algebra of matrices over an algebra `A` containing
a copy of `L` with conjugating symbols `u` the matrix of `σ` multiplied by the diagonal matrix of
the symbol of the restriction of `σ` is a unit.  These units conjugate the embedded copy of `L'`
by the automorphisms of `L'` and multiply according to the inflated cocycle, so they identify the
matrix algebra with the crossed product of the inflated cocycle.

## Main results

* `InverseGalois.CFT.inflateCocycle`: the inflation of a multiplicative `2`-cochain along the
  restriction homomorphism of Galois groups.
* `InverseGalois.CFT.isMulCocycle₂_inflateCocycle`: the inflation of a multiplicative `2`-cocycle
  is a multiplicative `2`-cocycle.
* `InverseGalois.CFT.nonempty_algEquiv_matrix_inflateCocycle`: matrices over an algebra realising
  a cocycle of `Gal(L/K)` form the crossed product of the inflated cocycle.
* `InverseGalois.CFT.CrossedProduct.mk_csa_inflateCocycle`: **inflation does not change the Brauer
  class of a crossed product.**

## Tags

crossed product, Brauer group, inflation, Galois cohomology, class field theory
-/

universe u

open Module

namespace InverseGalois.CFT

open groupCohomology

/-! ### Transport of a multiplicative two-cocycle -/

section Transport

/-- Composing a multiplicative `2`-cocycle with a homomorphism of groups on the source and an
equivariant homomorphism of modules on the target gives a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_comp {G H M N : Type*} [Group G] [Group H] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction H N] (r : H →* G) (φ : M →* N)
    (hφ : ∀ (x : H) (m : M), φ (r x • m) = x • φ m)
    {c : G × G → M} (hc : IsMulCocycle₂ c) :
    IsMulCocycle₂ fun p : H × H => φ (c (r p.1, r p.2)) := by
  intro g h j
  show φ (c (r (g * h), r j)) * φ (c (r g, r h))
    = g • φ (c (r h, r j)) * φ (c (r g, r (h * j)))
  rw [map_mul r g h, map_mul r h j, ← hφ g, ← map_mul φ, ← map_mul φ]
  exact congrArg φ (hc (r g) (r h) (r j))

end Transport

/-! ### Inflation of a cocycle along a tower -/

section Inflate

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Normal K L]

variable (L' : Type u) [Field L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']

/-- The inflation of a multiplicative `2`-cochain of `Gal(L/K)` with values in `Lˣ` to a
multiplicative `2`-cochain of `Gal(L'/K)` with values in `L'ˣ`. -/
noncomputable def inflateCocycle (f : Gal(L/K) × Gal(L/K) → Lˣ) :
    Gal(L'/K) × Gal(L'/K) → L'ˣ :=
  fun p => Units.map (algebraMap L L' : L →* L')
    (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2))

variable {L'}

theorem inflateCocycle_apply (f : Gal(L/K) × Gal(L/K) → Lˣ) (σ τ : Gal(L'/K)) :
    ((inflateCocycle L' f (σ, τ) : L'ˣ) : L')
      = algebraMap L L' ((f (σ.restrictNormal L, τ.restrictNormal L) : Lˣ) : L) := rfl

/-- The inclusion of the units of the intermediate field is equivariant for the restriction
homomorphism. -/
theorem smul_units_map_algebraMap (σ : Gal(L'/K)) (v : Lˣ) :
    Units.map (algebraMap L L' : L →* L') (AlgEquiv.restrictNormalHom L σ • v)
      = σ • Units.map (algebraMap L L' : L →* L') v :=
  Units.ext (AlgEquiv.restrictNormal_commutes σ L (v : L))

/-- **The inflation of a multiplicative `2`-cocycle is a multiplicative `2`-cocycle.** -/
theorem isMulCocycle₂_inflateCocycle {f : Gal(L/K) × Gal(L/K) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (inflateCocycle L' f) :=
  isMulCocycle₂_comp (AlgEquiv.restrictNormalHom L) (Units.map (algebraMap L L' : L →* L'))
    smul_units_map_algebraMap hf

end Inflate

/-! ### The symbols of a crossed product as units -/

namespace CrossedProduct

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {f : Gal(L/K) × Gal(L/K) → Lˣ}

/-- The symbol attached to an automorphism, as a unit of the crossed product. -/
noncomputable def unitSymbol (hf : IsMulCocycle₂ f) (g : Gal(L/K)) : (CrossedProduct hf)ˣ :=
  (isUnit_single_one hf g).unit

theorem val_unitSymbol (hf : IsMulCocycle₂ f) (g : Gal(L/K)) :
    ((unitSymbol hf g : (CrossedProduct hf)ˣ) : CrossedProduct hf) = single hf g 1 :=
  IsUnit.unit_spec _

/-- The symbol attached to an automorphism conjugates the copy of `L` by that automorphism. -/
theorem inclAlgHom_conj_unitSymbol (hf : IsMulCocycle₂ f) (g : Gal(L/K)) (x : L) :
    inclAlgHom hf (g x) * ((unitSymbol hf g : (CrossedProduct hf)ˣ) : CrossedProduct hf)
      = ((unitSymbol hf g : (CrossedProduct hf)ˣ) : CrossedProduct hf) * inclAlgHom hf x := by
  rw [val_unitSymbol, inclAlgHom_apply, inclAlgHom_apply]
  exact (mul_single_one g x).symm

/-- The symbols multiply according to the cocycle. -/
theorem unitSymbol_mul (hf : IsMulCocycle₂ f) (g h : Gal(L/K)) :
    ((unitSymbol hf g : (CrossedProduct hf)ˣ) : CrossedProduct hf)
        * ((unitSymbol hf h : (CrossedProduct hf)ˣ) : CrossedProduct hf)
      = inclAlgHom hf ((f (g, h) : Lˣ) : L)
        * ((unitSymbol hf (g * h) : (CrossedProduct hf)ˣ) : CrossedProduct hf) := by
  rw [val_unitSymbol, val_unitSymbol, val_unitSymbol, inclAlgHom_apply,
    single_one_mul_single_one]

end CrossedProduct

/-! ### Matrices over an algebra realising the cocycle -/

section Matrix

variable {K L L' A : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [FiniteDimensional K L']
  [IsGalois K L] [IsGalois K L'] [Ring A] [Algebra K A] [IsSimpleRing A] [FiniteDimensional K A]
  {f : Gal(L/K) × Gal(L/K) → Lˣ}

/-- **Matrices over an algebra realising a cocycle of an intermediate field.**  If `A` is a simple
algebra of dimension `[L : K] ^ 2` containing a copy of `L` together with units conjugating that
copy by the elements of `Gal(L/K)` and multiplying according to `f`, then the algebra of matrices
over `A` indexed by an `L`-basis of `L'` is the crossed product of the inflation of `f`. -/
theorem nonempty_algEquiv_matrix_inflateCocycle_of_basis {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (b : Basis ι L L') (hf : IsMulCocycle₂ f) (emb : L →ₐ[K] A)
    (u : Gal(L/K) → Aˣ)
    (hu : ∀ (σ : Gal(L/K)) (x : L), emb (σ x) * (u σ : A) = (u σ : A) * emb x)
    (hmul : ∀ σ τ : Gal(L/K),
      (u σ : A) * (u τ : A) = emb ((f (σ, τ) : Lˣ) : L) * (u (σ * τ) : A))
    (hdim : finrank K A = finrank K L * finrank K L) :
    Nonempty (CrossedProduct (isMulCocycle₂_inflateCocycle (L' := L') hf) ≃ₐ[K]
      Matrix ι ι A) := by
  classical
  haveI : Module.Finite L L' := FiniteDimensional.right K L L'
  have hlm : ∀ z : L', Algebra.leftMulMatrix b z = coordMatrix b (fun j => z * b j) := by
    intro z
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, coordMatrix_apply]
  set ρ : L' →ₐ[K] Matrix ι ι L := (Algebra.leftMulMatrix b).restrictScalars K with hρ
  have hρ_apply : ∀ y : L', ρ y = Algebra.leftMulMatrix b y := fun y => by rw [hρ]; rfl
  set emb' : L' →ₐ[K] Matrix ι ι A := emb.mapMatrix.comp ρ with hemb'
  obtain ⟨S, hS⟩ : ∃ S : Gal(L'/K) → Matrix ι ι L,
      ∀ σ, S σ = coordMatrix b fun j => σ (b j) := ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Gal(L'/K) → Matrix ι ι A,
      ∀ σ, D σ = Matrix.diagonal fun _ => (u (σ.restrictNormal L) : A) := ⟨_, fun _ => rfl⟩
  -- the diagonal matrix of a symbol conjugates the entries by the restriction
  have hDcomm : ∀ (σ : Gal(L'/K)) (X : Matrix ι ι L),
      D σ * emb.mapMatrix X = emb.mapMatrix (X.map (σ.restrictNormal L)) * D σ := by
    intro σ X
    ext i j
    rw [hD, Matrix.diagonal_mul, Matrix.mul_diagonal, AlgHom.mapMatrix_apply,
      AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
    exact (hu (σ.restrictNormal L) (X i j)).symm
  -- the matrices of the automorphisms form a semilinear cocycle
  have hS1 : S 1 = 1 := by
    rw [hS]
    have h : (fun j => (1 : Gal(L'/K)) (b j)) = fun j => b j := by
      funext j
      rw [AlgEquiv.one_apply]
    rw [h]
    exact coordMatrix_self b
  have hSmul : ∀ σ τ : Gal(L'/K), S (σ * τ) = S σ * (S τ).map (σ.restrictNormal L) := by
    intro σ τ
    rw [hS, hS, hS]
    have h : (fun j => (σ * τ) (b j)) = fun j => σ (τ (b j)) := by
      funext j
      rw [AlgEquiv.mul_apply]
    rw [h]
    exact coordMatrix_map b σ fun j => τ (b j)
  have hsemi : ∀ (σ : Gal(L'/K)) (x : L'),
      ρ (σ x) * S σ = S σ * (ρ x).map (σ.restrictNormal L) := by
    intro σ x
    have h1 : ρ (σ x) * S σ = coordMatrix b (fun j => σ x * σ (b j)) := by
      rw [hρ_apply, hS, ← coordMatrix_smul]
    have h2 : S σ * (ρ x).map (σ.restrictNormal L)
        = coordMatrix b (fun j => σ (x * b j)) := by
      rw [hρ_apply, hlm, hS, ← coordMatrix_map b σ fun j => x * b j]
    rw [h1, h2]
    exact congrArg _ (funext fun j => (map_mul σ x (b j)).symm)
  -- the candidate units
  have hSunit : ∀ σ : Gal(L'/K), IsUnit (S σ) := by
    intro σ
    have h1 : S σ * (S σ⁻¹).map (σ.restrictNormal L) = 1 := by
      rw [← hSmul, mul_inv_cancel, hS1]
    exact ⟨⟨S σ, (S σ⁻¹).map (σ.restrictNormal L), h1, mul_eq_one_comm.mp h1⟩, rfl⟩
  have hDunit : ∀ σ : Gal(L'/K), IsUnit (D σ) := by
    intro σ
    have h1 : D σ
        * Matrix.diagonal (fun _ : ι => (((u (σ.restrictNormal L))⁻¹ : Aˣ) : A)) = 1 := by
      rw [hD, Matrix.diagonal_mul_diagonal]
      simp only [Units.mul_inv]
      exact Matrix.diagonal_one
    have h2 : Matrix.diagonal (fun _ : ι => (((u (σ.restrictNormal L))⁻¹ : Aˣ) : A))
        * D σ = 1 := by
      rw [hD, Matrix.diagonal_mul_diagonal]
      simp only [Units.inv_mul]
      exact Matrix.diagonal_one
    exact ⟨⟨D σ, _, h1, h2⟩, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Gal(L'/K) → (Matrix ι ι A)ˣ,
      ∀ σ, (W σ : Matrix ι ι A) = emb.mapMatrix (S σ) * D σ :=
    ⟨fun σ => (((hSunit σ).map emb.mapMatrix).mul (hDunit σ)).unit, fun _ => IsUnit.unit_spec _⟩
  -- the units conjugate the copy of `L'`
  have hu' : ∀ (σ : Gal(L'/K)) (x : L'),
      emb' (σ x) * (W σ : Matrix ι ι A) = (W σ : Matrix ι ι A) * emb' x := by
    intro σ x
    rw [hW, hemb']
    simp only [AlgHom.comp_apply]
    calc emb.mapMatrix (ρ (σ x)) * (emb.mapMatrix (S σ) * D σ)
        = emb.mapMatrix (ρ (σ x) * S σ) * D σ := by rw [map_mul, mul_assoc]
      _ = emb.mapMatrix (S σ * (ρ x).map (σ.restrictNormal L)) * D σ := by rw [hsemi σ x]
      _ = emb.mapMatrix (S σ) * (emb.mapMatrix ((ρ x).map (σ.restrictNormal L)) * D σ) := by
            rw [map_mul, mul_assoc]
      _ = emb.mapMatrix (S σ) * (D σ * emb.mapMatrix (ρ x)) := by rw [← hDcomm σ (ρ x)]
      _ = emb.mapMatrix (S σ) * D σ * emb.mapMatrix (ρ x) := by rw [mul_assoc]
  -- the units multiply according to the inflated cocycle
  have hcomm : ∀ (c : L) (X : Matrix ι ι L),
      Matrix.diagonal (fun _ : ι => emb c) * emb.mapMatrix X
        = emb.mapMatrix X * Matrix.diagonal (fun _ : ι => emb c) := by
    intro c X
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, AlgHom.mapMatrix_apply, Matrix.map_apply,
      ← map_mul, ← map_mul, mul_comm]
  have hρalg : ∀ c : L, ρ (algebraMap L L' c) = Matrix.diagonal fun _ : ι => c := by
    intro c
    rw [hρ_apply, show Algebra.leftMulMatrix b (algebraMap L L' c)
      = algebraMap L (Matrix ι ι L) c from (Algebra.leftMulMatrix b).commutes c,
      Matrix.algebraMap_eq_diagonal]
    congr 1
  have hembalg : ∀ c : L, emb' (algebraMap L L' c) = Matrix.diagonal fun _ : ι => emb c := by
    intro c
    rw [hemb']
    simp only [AlgHom.comp_apply]
    rw [hρalg, AlgHom.mapMatrix_apply, Matrix.diagonal_map (map_zero emb)]
  have hmul' : ∀ σ τ : Gal(L'/K),
      (W σ : Matrix ι ι A) * (W τ : Matrix ι ι A)
        = emb' ((inflateCocycle L' f (σ, τ) : L'ˣ) : L') * (W (σ * τ) : Matrix ι ι A) := by
    intro σ τ
    have hr : (σ * τ).restrictNormal L = σ.restrictNormal L * τ.restrictNormal L :=
      map_mul (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L) σ τ
    have hLHS : (W σ : Matrix ι ι A) * (W τ : Matrix ι ι A)
        = emb.mapMatrix (S (σ * τ)) * (D σ * D τ) := by
      rw [hW, hW]
      calc emb.mapMatrix (S σ) * D σ * (emb.mapMatrix (S τ) * D τ)
          = emb.mapMatrix (S σ) * (D σ * emb.mapMatrix (S τ)) * D τ := by
            simp only [mul_assoc]
        _ = emb.mapMatrix (S σ)
              * (emb.mapMatrix ((S τ).map (σ.restrictNormal L)) * D σ) * D τ := by
            rw [hDcomm σ (S τ)]
        _ = emb.mapMatrix (S σ * (S τ).map (σ.restrictNormal L)) * (D σ * D τ) := by
            rw [map_mul]
            simp only [mul_assoc]
        _ = emb.mapMatrix (S (σ * τ)) * (D σ * D τ) := by rw [hSmul]
    have hDD : D σ * D τ = Matrix.diagonal
        (fun _ : ι => emb ((f (σ.restrictNormal L, τ.restrictNormal L) : Lˣ) : L)
          * (u ((σ * τ).restrictNormal L) : A)) := by
      rw [hD, hD, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [hmul (σ.restrictNormal L) (τ.restrictNormal L), hr]
    have hRHS : emb' ((inflateCocycle L' f (σ, τ) : L'ˣ) : L') * (W (σ * τ) : Matrix ι ι A)
        = emb.mapMatrix (S (σ * τ)) * Matrix.diagonal
            (fun _ : ι => emb ((f (σ.restrictNormal L, τ.restrictNormal L) : Lˣ) : L)
              * (u ((σ * τ).restrictNormal L) : A)) := by
      rw [inflateCocycle_apply, hembalg, hW, ← mul_assoc, hcomm, mul_assoc, hD,
        Matrix.diagonal_mul_diagonal]
    rw [hLHS, hDD, hRHS]
  -- the dimension count
  have hcard : finrank K L' = finrank K L * Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b]
    exact (Module.finrank_mul_finrank K L L').symm
  have hdim' : finrank K (Matrix ι ι A) = finrank K L' * finrank K L' := by
    rw [Module.finrank_matrix, hdim, hcard]
    ring
  exact ⟨AlgEquiv.ofBijective
    (crossedProductAlgHom emb' W (isMulCocycle₂_inflateCocycle hf) hu' hmul')
    (crossedProductAlgHom_bijective emb' W (isMulCocycle₂_inflateCocycle hf) hu' hmul' hdim')⟩

/-- **Matrices over an algebra realising a cocycle of an intermediate field.**  The number of rows
is the degree of the larger extension over the intermediate one. -/
theorem nonempty_algEquiv_matrix_inflateCocycle (hf : IsMulCocycle₂ f) (emb : L →ₐ[K] A)
    (u : Gal(L/K) → Aˣ)
    (hu : ∀ (σ : Gal(L/K)) (x : L), emb (σ x) * (u σ : A) = (u σ : A) * emb x)
    (hmul : ∀ σ τ : Gal(L/K),
      (u σ : A) * (u τ : A) = emb ((f (σ, τ) : Lˣ) : L) * (u (σ * τ) : A))
    (hdim : finrank K A = finrank K L * finrank K L) :
    Nonempty (CrossedProduct (isMulCocycle₂_inflateCocycle (L' := L') hf) ≃ₐ[K]
      Matrix (Fin (finrank L L')) (Fin (finrank L L')) A) := by
  haveI : Module.Finite L L' := FiniteDimensional.right K L L'
  haveI : Nonempty (Fin (finrank L L')) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact nonempty_algEquiv_matrix_inflateCocycle_of_basis (Module.finBasis L L') hf emb u hu hmul
    hdim

end Matrix

/-! ### Inflation preserves the Brauer class -/

namespace CrossedProduct

variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [FiniteDimensional K L']
  [IsGalois K L] [IsGalois K L'] {f : Gal(L/K) × Gal(L/K) → Lˣ}

/-- **Inflation does not change the Brauer class of a crossed product.**  For a tower
`K ⊆ L ⊆ L'` of finite Galois extensions of `K`, the crossed product of a multiplicative
`2`-cocycle of `Gal(L/K)` and the crossed product of its inflation to `Gal(L'/K)` have the same
class in the Brauer group of `K`. -/
theorem mk_csa_inflateCocycle (hf : IsMulCocycle₂ f) :
    (⟦csa (isMulCocycle₂_inflateCocycle (L' := L') hf)⟧ : BrauerGroup K) = ⟦csa hf⟧ := by
  haveI : Module.Finite L L' := FiniteDimensional.right K L L'
  have hdim : finrank K (CrossedProduct hf) = finrank K L * finrank K L := by
    rw [CrossedProduct.finrank_eq, IsGalois.card_aut_eq_finrank K L, sq]
  obtain ⟨e⟩ := nonempty_algEquiv_matrix_inflateCocycle (L' := L') hf (inclAlgHom hf)
    (unitSymbol hf) (inclAlgHom_conj_unitSymbol hf) (unitSymbol_mul hf) hdim
  have hd : finrank L L' ≠ 0 := Module.finrank_pos.ne'
  exact Quotient.sound (IsBrauerEquivalent.of_algEquiv_matrix hd e)

end CrossedProduct

end InverseGalois.CFT
