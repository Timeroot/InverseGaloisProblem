import Mathlib
import InverseGalois.CFT.Brauer.CrossedProduct
import InverseGalois.CFT.Brauer.CrossedProductSimple

/-!
# Cohomologous cocycles give isomorphic crossed products

Let `L / K` be a Galois extension of fields with group `G = Gal(L/K)` and let
`f, f' : G × G → Lˣ` be multiplicative `2`-cocycles.  If `f'` differs from `f` by the
coboundary of a function `c : G → Lˣ`, in the sense that
`f' (g, h) = f (g, h) * (g • c h / c (g * h) * c g)`,
then the two crossed product algebras are isomorphic as `K`-algebras, by the map that
rescales the symbol `u g` by `c g`.

## Main results

* `InverseGalois.CFT.CrossedProduct.algEquivOfCoboundary`: the `K`-algebra isomorphism
  `CrossedProduct hf' ≃ₐ[K] CrossedProduct hf` attached to a coboundary relation
  `f' = f * ∂c`.
* `InverseGalois.CFT.CrossedProduct.nonempty_algEquiv_of_isMulCoboundary₂`: two cocycles whose
  ratio is a `2`-coboundary have isomorphic crossed products.
* `InverseGalois.CFT.isMulCocycle₂_one`: the constant function `1` is a `2`-cocycle.
* `InverseGalois.CFT.CrossedProduct.algEquivEndOfOne`: the crossed product of the trivial
  cocycle is the endomorphism algebra `Module.End K L`, and
  `InverseGalois.CFT.CrossedProduct.algEquivMatrixOfOne` is the matrix form of this.
* `InverseGalois.CFT.CrossedProduct.nonempty_algEquivEnd_of_isMulCoboundary₂`: the crossed
  product of a cocycle which is a coboundary is the endomorphism algebra `Module.End K L`.
* `InverseGalois.CFT.CrossedProduct.nonempty_algEquivMatrix_of_isMulCoboundary₂`: the same
  statement in terms of matrices over `K`.

-/

namespace InverseGalois.CFT

open groupCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {f f' : Gal(L/K) × Gal(L/K) → Lˣ}

/-- The constant function `1` is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_one (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsMulCocycle₂ (fun _ : Gal(L/K) × Gal(L/K) => (1 : Lˣ)) := by
  intro g h j
  simp

namespace CrossedProduct

section Coboundary

variable {hf : IsMulCocycle₂ f} {hf' : IsMulCocycle₂ f'} {c : Gal(L/K) → Lˣ}

/-- The coboundary relation `f' = f * ∂c`, cleared of denominators. -/
theorem units_mul_coboundary
    (hc : ∀ g h : Gal(L/K), f' (g, h) = f (g, h) * (g • c h / c (g * h) * c g))
    (g h : Gal(L/K)) :
    f' (g, h) * c (g * h) = f (g, h) * (g • c h) * c g := by
  rw [hc, div_mul_eq_mul_div, mul_div_assoc']
  simp [mul_assoc]

/-- The coboundary relation `f' = f * ∂c`, cleared of denominators and read inside `L`. -/
theorem val_mul_coboundary
    (hc : ∀ g h : Gal(L/K), f' (g, h) = f (g, h) * (g • c h / c (g * h) * c g))
    (g h : Gal(L/K)) :
    ((f' (g, h) : Lˣ) : L) * ((c (g * h) : Lˣ) : L)
      = ((f (g, h) : Lˣ) : L) * g ((c h : Lˣ) : L) * ((c g : Lˣ) : L) := by
  have := congrArg (Units.val) (units_mul_coboundary hc g h)
  simpa using this

/-- The `L`-linear equivalence between two crossed products attached to cohomologous cocycles:
it rescales the symbol `u g` by `c g`. -/
noncomputable def linearEquivOfCoboundary (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (c : Gal(L/K) → Lˣ) : CrossedProduct hf' ≃ₗ[L] CrossedProduct hf :=
  (basisUnits hf').equiv ((basisUnits hf).unitsSMul c) (Equiv.refl _)

@[simp]
theorem linearEquivOfCoboundary_single (g : Gal(L/K)) (a : L) :
    linearEquivOfCoboundary hf hf' c (single hf' g a) = single hf g (a * ((c g : Lˣ) : L)) := by
  have h1 : single hf' g a = a • (basisUnits hf') g := by
    rw [coe_basisUnits, smul_single, mul_one]
  rw [h1, map_smul, linearEquivOfCoboundary, Module.Basis.equiv_apply,
    Module.Basis.unitsSMul_apply, Equiv.refl_apply, Units.smul_def, coe_basisUnits, smul_single,
    smul_single, mul_one]

/-- The rescaling map takes the unit of one crossed product to the unit of the other. -/
theorem linearEquivOfCoboundary_one
    (hc : ∀ g h : Gal(L/K), f' (g, h) = f (g, h) * (g • c h / c (g * h) * c g)) :
    linearEquivOfCoboundary hf hf' c 1 = 1 := by
  have h0 : f' (1, 1) = f (1, 1) * c 1 := by
    have h1 := units_mul_coboundary hc 1 1
    rw [one_mul, one_smul] at h1
    exact mul_right_cancel h1
  have h2 : (f' (1, 1))⁻¹ * c 1 = (f (1, 1))⁻¹ := by
    rw [h0, mul_inv, mul_assoc, inv_mul_cancel, mul_one]
  rw [one_def, linearEquivOfCoboundary_single, one_def]
  refine single_congr ?_
  have := congrArg (Units.val) h2
  simpa using this

/-- The rescaling map is multiplicative. -/
theorem linearEquivOfCoboundary_mul
    (hc : ∀ g h : Gal(L/K), f' (g, h) = f (g, h) * (g • c h / c (g * h) * c g))
    (x y : CrossedProduct hf') :
    linearEquivOfCoboundary hf hf' c (x * y)
      = linearEquivOfCoboundary hf hf' c x * linearEquivOfCoboundary hf hf' c y := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_mul]
  | single g a =>
    induction y using CrossedProduct.induction_linear with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, mul_add]
    | single h b =>
      rw [single_mul_single, linearEquivOfCoboundary_single, linearEquivOfCoboundary_single,
        linearEquivOfCoboundary_single, single_mul_single]
      refine single_congr ?_
      rw [map_mul]
      linear_combination (a * g b) * val_mul_coboundary hc g h

/-- Cohomologous cocycles have isomorphic crossed products: if `f' = f * ∂c`, rescaling the
symbol `u g` by `c g` is a `K`-algebra isomorphism `CrossedProduct hf' ≃ₐ[K] CrossedProduct hf`. -/
noncomputable def algEquivOfCoboundary (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (c : Gal(L/K) → Lˣ)
    (hc : ∀ g h : Gal(L/K), f' (g, h) = f (g, h) * (g • c h / c (g * h) * c g)) :
    CrossedProduct hf' ≃ₐ[K] CrossedProduct hf :=
  AlgEquiv.ofLinearEquiv ((linearEquivOfCoboundary hf hf' c).restrictScalars K)
    (linearEquivOfCoboundary_one hc) (linearEquivOfCoboundary_mul hc)

@[simp]
theorem algEquivOfCoboundary_single
    (hc : ∀ g h : Gal(L/K), f' (g, h) = f (g, h) * (g • c h / c (g * h) * c g))
    (g : Gal(L/K)) (a : L) :
    algEquivOfCoboundary hf hf' c hc (single hf' g a) = single hf g (a * ((c g : Lˣ) : L)) :=
  linearEquivOfCoboundary_single (hf := hf) (hf' := hf') (c := c) g a

end Coboundary

/-- Two cocycles whose ratio is a `2`-coboundary have isomorphic crossed products. -/
theorem nonempty_algEquiv_of_isMulCoboundary₂ (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (h : IsMulCoboundary₂ fun p : Gal(L/K) × Gal(L/K) => f' p / f p) :
    Nonempty (CrossedProduct hf ≃ₐ[K] CrossedProduct hf') := by
  obtain ⟨x, hx⟩ := h
  refine ⟨(algEquivOfCoboundary hf hf' x fun g h => ?_).symm⟩
  rw [hx g h, mul_div_cancel]

section Trivial

variable (K L)

/-- The action of the crossed product of the trivial cocycle on `L`: the symbol `u g` acts as
the field automorphism `g`, and the coefficient `a` acts by multiplication. -/
noncomputable def toEndLinear :
    CrossedProduct (isMulCocycle₂_one K L) →ₗ[L] Module.End K L :=
  (basisUnits (isMulCocycle₂_one K L)).constr K fun g : Gal(L/K) => g.toLinearMap

variable {K L}

@[simp]
theorem toEndLinear_single (g : Gal(L/K)) (a y : L) :
    toEndLinear K L (single (isMulCocycle₂_one K L) g a) y = a * g y := by
  have h1 : single (isMulCocycle₂_one K L) g a
      = a • (basisUnits (isMulCocycle₂_one K L)) g := by
    rw [coe_basisUnits, smul_single, mul_one]
  rw [h1, map_smul, toEndLinear, Module.Basis.constr_basis, LinearMap.smul_apply,
    AlgEquiv.toLinearMap_apply, smul_eq_mul]

/-- The action of the crossed product of the trivial cocycle preserves the unit. -/
theorem toEndLinear_one : toEndLinear K L 1 = 1 := by
  refine LinearMap.ext fun y => ?_
  rw [one_def, toEndLinear_single]
  simp

/-- The action of the crossed product of the trivial cocycle is multiplicative. -/
theorem toEndLinear_mul (x y : CrossedProduct (isMulCocycle₂_one K L)) :
    toEndLinear K L (x * y) = toEndLinear K L x * toEndLinear K L y := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_mul]
  | single g a =>
    induction y using CrossedProduct.induction_linear with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, mul_add]
    | single h b =>
      refine LinearMap.ext fun z => ?_
      rw [single_mul_single, toEndLinear_single, Module.End.mul_apply, toEndLinear_single,
        toEndLinear_single, AlgEquiv.mul_apply, map_mul]
      simp [mul_assoc]

variable (K L)

/-- The `K`-algebra homomorphism from the crossed product of the trivial cocycle to the
endomorphism algebra of `L`. -/
noncomputable def toEndAlgHom :
    CrossedProduct (isMulCocycle₂_one K L) →ₐ[K] Module.End K L :=
  AlgHom.ofLinearMap ((toEndLinear K L).restrictScalars K) toEndLinear_one toEndLinear_mul

@[simp]
theorem toEndAlgHom_apply (x : CrossedProduct (isMulCocycle₂_one K L)) :
    toEndAlgHom K L x = toEndLinear K L x := rfl

/-- Dedekind's linear independence of characters, for the automorphisms of `L` over `K`. -/
theorem linearIndependent_toLinearMap_aut :
    LinearIndependent L fun g : Gal(L/K) => g.toLinearMap :=
  (linearIndependent_toLinearMap K L L).comp (fun g : Gal(L/K) => (g : L →ₐ[K] L))
    fun _ _ hg => AlgEquiv.ext fun x => DFunLike.ext_iff.1 hg x

variable {K L}

/-- The action map is the linear combination map of the family of field automorphisms. -/
theorem toEndLinear_eq_linearCombination (x : CrossedProduct (isMulCocycle₂_one K L)) :
    toEndLinear K L x
      = Finsupp.linearCombination L (fun g : Gal(L/K) => g.toLinearMap)
          ((basisUnits (isMulCocycle₂_one K L)).repr x) := by
  rw [toEndLinear, Module.Basis.constr_apply, Finsupp.linearCombination_apply]

/-- The crossed product of the trivial cocycle acts faithfully on `L`. -/
theorem toEndLinear_injective : Function.Injective (toEndLinear K L) := by
  intro x y hxy
  refine (basisUnits (isMulCocycle₂_one K L)).repr.injective ?_
  refine linearIndependent_toLinearMap_aut K L ?_
  rw [← toEndLinear_eq_linearCombination, ← toEndLinear_eq_linearCombination, hxy]

/-- The crossed product of the trivial cocycle has the dimension of the endomorphism algebra. -/
theorem finrank_eq_finrank_end [FiniteDimensional K L] [IsGalois K L] :
    Module.finrank K (CrossedProduct (isMulCocycle₂_one K L))
      = Module.finrank K (Module.End K L) := by
  rw [finrank_eq, Module.finrank_linearMap K K L L, IsGalois.card_aut_eq_finrank K L, sq]

/-- The action of the crossed product of the trivial cocycle on `L` is bijective. -/
theorem toEndAlgHom_bijective [FiniteDimensional K L] [IsGalois K L] :
    Function.Bijective (toEndAlgHom K L) := by
  refine ⟨toEndLinear_injective, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (toEndLinear K L).restrictScalars K) finrank_eq_finrank_end).1 toEndLinear_injective

variable (K L)

/-- The crossed product of the trivial cocycle is the endomorphism algebra of `L`. -/
noncomputable def algEquivEndOfOne [FiniteDimensional K L] [IsGalois K L] :
    CrossedProduct (isMulCocycle₂_one K L) ≃ₐ[K] Module.End K L :=
  AlgEquiv.ofBijective (toEndAlgHom K L) toEndAlgHom_bijective

/-- The crossed product of the trivial cocycle is a matrix algebra over `K`. -/
noncomputable def algEquivMatrixOfOne [FiniteDimensional K L] [IsGalois K L] :
    CrossedProduct (isMulCocycle₂_one K L)
      ≃ₐ[K] Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K :=
  (algEquivEndOfOne K L).trans (LinearMap.toMatrixAlgEquiv (Module.finBasis K L))

variable {K L}

/-- A crossed product whose cocycle is a `2`-coboundary is the endomorphism algebra of `L`. -/
theorem nonempty_algEquivEnd_of_isMulCoboundary₂ [FiniteDimensional K L] [IsGalois K L]
    (hf : IsMulCocycle₂ f) (h : IsMulCoboundary₂ f) :
    Nonempty (CrossedProduct hf ≃ₐ[K] Module.End K L) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨AlgEquiv.trans (algEquivOfCoboundary (isMulCocycle₂_one K L) hf x fun g h => ?_)
    (algEquivEndOfOne K L)⟩
  rw [one_mul]
  exact (hx g h).symm

/-- A crossed product whose cocycle is a `2`-coboundary is a matrix algebra over `K`. -/
theorem nonempty_algEquivMatrix_of_isMulCoboundary₂ [FiniteDimensional K L] [IsGalois K L]
    (hf : IsMulCocycle₂ f) (h : IsMulCoboundary₂ f) :
    Nonempty (CrossedProduct hf
      ≃ₐ[K] Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K) :=
  (nonempty_algEquivEnd_of_isMulCoboundary₂ hf h).map fun e =>
    e.trans (LinearMap.toMatrixAlgEquiv (Module.finBasis K L))

end Trivial

end CrossedProduct

end InverseGalois.CFT
