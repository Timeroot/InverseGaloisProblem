import Mathlib
import InverseGalois.CFT.Brauer.BaseChange
import InverseGalois.CFT.Brauer.CrossedProductSimple

/-!
# A Galois extension splits its own crossed products

Let `L / K` be a finite Galois extension with group `G = Gal(L/K)` and let `f : G × G → Lˣ` be a
multiplicative `2`-cocycle.  The crossed product `A = CrossedProduct hf` is a central simple
`K`-algebra of dimension `|G| ^ 2`, and this file shows that `L` splits it: the class of `A` in
the Brauer group of `K` lies in the relative Brauer group `Br(L / K)`.

The mechanism is the right regular representation.  The algebra `A` is an `L`-vector space of
dimension `|G|` through the embedding `incl : L → A`, and right multiplication by an element of
`A` is `L`-linear for that structure.  Together with the scalar action of `L` this produces an
`L`-algebra map

`L ⊗[K] Aᵐᵒᵖ → End_L A`,

which is injective because the source is a simple ring, and then bijective because both sides have
dimension `|G| ^ 2` over `L`.  Choosing an `L`-basis of `A` turns the target into a matrix algebra,
so the base change of `Aᵐᵒᵖ` to `L` is split; since the class of `Aᵐᵒᵖ` is the inverse of the class
of `A`, the class of `A` is split as well.

## Main results

* `InverseGalois.CFT.CrossedProduct.rmulHom`: right multiplication as a `K`-algebra map from the
  opposite algebra to the `L`-linear endomorphisms.
* `InverseGalois.CFT.CrossedProduct.toEnd`: the induced `L`-algebra map on `L ⊗[K] Aᵐᵒᵖ`.
* `InverseGalois.CFT.CrossedProduct.toEnd_bijective`: it is bijective.
* `InverseGalois.CFT.CrossedProduct.algEquivEndOp`, `algEquivMatrixOp`: the resulting isomorphisms
  of the base change with an endomorphism algebra and with a matrix algebra.
* `InverseGalois.CFT.CrossedProduct.mk_csa_mem_relative`: the class of the crossed product lies in
  the relative Brauer group `Br(L / K)`.
-/

universe u

open Module
open scoped TensorProduct

namespace InverseGalois.CFT

open groupCohomology

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {f : Gal(L/K) × Gal(L/K) → Lˣ}

namespace CrossedProduct

variable {hf : IsMulCocycle₂ f}

/-! ### The right regular representation -/

/-- Right multiplication in the crossed product, as a `K`-algebra map from the opposite algebra
to the algebra of `L`-linear endomorphisms of the crossed product. -/
noncomputable def rmulHom (hf : IsMulCocycle₂ f) :
    (CrossedProduct hf)ᵐᵒᵖ →ₐ[K] Module.End L (CrossedProduct hf) where
  toFun a :=
    { toFun := fun x => x * a.unop
      map_add' := fun x y => add_mul' x y a.unop
      map_smul' := fun c x => smul_mul_assoc' c x a.unop }
  map_one' := LinearMap.ext fun x => mul_one x
  map_mul' a b := LinearMap.ext fun x => (mul_assoc x b.unop a.unop).symm
  map_zero' := LinearMap.ext fun x => mul_zero x
  map_add' a b := LinearMap.ext fun x => mul_add x a.unop b.unop
  commutes' k := LinearMap.ext fun x => by
    show x * algebraMap K (CrossedProduct hf) k = k • x
    rw [Algebra.smul_def, algebraMap_eq, ← incl_algebraMap_commutes k x]

@[simp]
theorem rmulHom_apply (a : (CrossedProduct hf)ᵐᵒᵖ) (x : CrossedProduct hf) :
    rmulHom hf a x = x * a.unop := rfl

/-- The scalar action of `L` and right multiplication by an element of the crossed product
commute. -/
theorem commute_ofId_rmulHom (c : L) (a : (CrossedProduct hf)ᵐᵒᵖ) :
    Commute (Algebra.ofId L (Module.End L (CrossedProduct hf)) c) (rmulHom hf a) := by
  refine LinearMap.ext fun x => ?_
  show c • (x * a.unop) = (c • x) * a.unop
  rw [smul_mul_assoc']

/-- The `L`-algebra map from the base change of the opposite crossed product to the `L`-linear
endomorphisms of the crossed product, sending `c ⊗ a` to `x ↦ c • (x * a)`. -/
noncomputable def toEnd (hf : IsMulCocycle₂ f) :
    L ⊗[K] (CrossedProduct hf)ᵐᵒᵖ →ₐ[L] Module.End L (CrossedProduct hf) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (rmulHom hf) commute_ofId_rmulHom

@[simp]
theorem toEnd_tmul (c : L) (a : (CrossedProduct hf)ᵐᵒᵖ) (x : CrossedProduct hf) :
    toEnd hf (c ⊗ₜ a) x = c • (x * a.unop) := rfl

/-! ### Bijectivity -/

variable [FiniteDimensional K L]

/-- The crossed product is a finite-dimensional `L`-vector space. -/
instance instFiniteLeft : Module.Finite L (CrossedProduct hf) :=
  Module.Finite.of_basis (basisUnits hf)

variable [IsGalois K L]

/-- The base change of the opposite crossed product and the endomorphism algebra have the same
dimension over `L`, namely the square of the degree of `L / K`. -/
theorem finrank_tensorOp :
    finrank L (L ⊗[K] (CrossedProduct hf)ᵐᵒᵖ) = finrank L (Module.End L (CrossedProduct hf)) := by
  have hop : finrank K (CrossedProduct hf)ᵐᵒᵖ = finrank K (CrossedProduct hf) :=
    (MulOpposite.opLinearEquiv K (M := CrossedProduct hf)).symm.finrank_eq
  rw [Module.finrank_baseChange, hop, finrank_eq, Module.finrank_linearMap L L, finrank_left,
    sq]

/-- The right regular representation of the crossed product is injective on the base change. -/
theorem toEnd_injective : Function.Injective (toEnd hf) :=
  (toEnd hf : L ⊗[K] (CrossedProduct hf)ᵐᵒᵖ →+* Module.End L (CrossedProduct hf)).injective

/-- The right regular representation identifies the base change of the opposite crossed product
with the full endomorphism algebra. -/
theorem toEnd_bijective : Function.Bijective (toEnd hf) :=
  ⟨toEnd_injective, by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank finrank_tensorOp).mp ?_
    exact toEnd_injective⟩

/-- The base change of the opposite crossed product to `L` is the algebra of `L`-linear
endomorphisms of the crossed product. -/
noncomputable def algEquivEndOp (hf : IsMulCocycle₂ f) :
    L ⊗[K] (CrossedProduct hf)ᵐᵒᵖ ≃ₐ[L] Module.End L (CrossedProduct hf) :=
  AlgEquiv.ofBijective (toEnd hf) toEnd_bijective

/-- The base change of the opposite crossed product to `L` is a matrix algebra over `L`, of size
the degree of `L / K`. -/
noncomputable def algEquivMatrixOp (hf : IsMulCocycle₂ f) :
    L ⊗[K] (CrossedProduct hf)ᵐᵒᵖ ≃ₐ[L]
      Matrix (Fin (finrank L (CrossedProduct hf))) (Fin (finrank L (CrossedProduct hf))) L :=
  (algEquivEndOp hf).trans (algEquivMatrix (Module.finBasis L (CrossedProduct hf)))

/-! ### The class of a crossed product is split by `L` -/

omit [IsGalois K L] in
/-- The degree of the crossed product over `L` is nonzero. -/
theorem finrank_left_ne_zero : finrank L (CrossedProduct hf) ≠ 0 := by
  rw [finrank_left]
  exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

/-- **A Galois extension splits its own crossed products.**  The class of the crossed product of
`L / K` and a `2`-cocycle lies in the relative Brauer group `Br(L / K)`. -/
theorem mk_csa_mem_relative (hf : IsMulCocycle₂ f) :
    (⟦csa hf⟧ : BrauerGroup K) ∈ BrauerGroup.relative K L := by
  refine (Subgroup.inv_mem_iff _).mp ?_
  rw [BrauerGroup.mk_inv]
  exact BrauerGroup.mk_mem_relative_of_algEquiv_matrix L finrank_left_ne_zero
    (algEquivMatrixOp hf)

end CrossedProduct

end InverseGalois.CFT
