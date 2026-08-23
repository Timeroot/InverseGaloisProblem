import Mathlib
import InverseGalois.CFT.Brauer.CrossedProductMul
import InverseGalois.CFT.Brauer.Kernel

/-!
# The crossed product homomorphism `H²(Gal(L/K), Lˣ) → Br(K)`

Let `L / K` be a finite Galois extension.  Attaching to a multiplicative `2`-cocycle its crossed
product induces a well-defined map on cohomology classes, because cohomologous cocycles have
isomorphic crossed products; the map is a group homomorphism because the crossed product of a
product of cocycles is Brauer equivalent to the product of the crossed products; and it is
injective because a crossed product is trivial in the Brauer group exactly when its cocycle is a
coboundary.  Its image lands in the relative Brauer group `Br(L / K)`.

This realises `H²(Gal(L/K), Lˣ)` as a subgroup of `Br(L / K)`.

## Main results

* `InverseGalois.CFT.CrossedProduct.mk_csa_one`, `InverseGalois.CFT.CrossedProduct.mk_csa_inv`:
  the crossed product of the trivial cocycle is trivial, and inverting a cocycle inverts the
  Brauer class.
* `InverseGalois.CFT.CrossedProduct.mk_csa_eq_mk_csa_iff`: two crossed products have the same
  Brauer class exactly when their cocycles are cohomologous.
* `InverseGalois.CFT.brauerOfH2`: the Brauer class attached to a class in
  `H²(Gal(L/K), Lˣ)`, together with `InverseGalois.CFT.brauerOfH2_apply` computing it on a
  cocycle.
* `InverseGalois.CFT.brauerHom`: the group homomorphism
  `Multiplicative (H²(Gal(L/K), Lˣ)) →* Br(K)`.
* `InverseGalois.CFT.brauerHom_injective` and `InverseGalois.CFT.brauerHom_mem_relative`: it is
  injective, with image inside the relative Brauer group `Br(L / K)`.
-/

universe u

open Module

namespace InverseGalois.CFT

open groupCohomology

/-! ### Brauer classes of crossed products -/

section Basic

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {f f' : Gal(L/K) × Gal(L/K) → Lˣ}

namespace CrossedProduct

/-- Cocycles that agree have the same Brauer class. -/
theorem mk_csa_congr (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') (h : f = f') :
    (⟦csa hf⟧ : BrauerGroup K) = ⟦csa hf'⟧ := by
  subst h
  rfl

/-- The crossed product of the trivial cocycle is trivial in the Brauer group. -/
theorem mk_csa_one : (⟦csa (isMulCocycle₂_one K L)⟧ : BrauerGroup K) = 1 :=
  BrauerGroup.mk_eq_one_of_algEquiv_matrix Module.finrank_pos.ne' (algEquivMatrixOfOne K L)

/-- Inverting a cocycle inverts the Brauer class of its crossed product. -/
theorem mk_csa_inv (hf : IsMulCocycle₂ f) :
    (⟦csa (isMulCocycle₂_inv hf)⟧ : BrauerGroup K) = (⟦csa hf⟧ : BrauerGroup K)⁻¹ := by
  have h := mk_csa_mul hf (isMulCocycle₂_inv hf)
  rw [mk_csa_congr (isMulCocycle₂_mul hf (isMulCocycle₂_inv hf)) (isMulCocycle₂_one K L)
    (funext fun p => mul_inv_cancel (f p)), mk_csa_one] at h
  rw [eq_inv_iff_mul_eq_one, mul_comm]
  exact h.symm

/-- **Two crossed products have the same Brauer class exactly when their cocycles are
cohomologous.** -/
theorem mk_csa_eq_mk_csa_iff (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    (⟦csa hf⟧ : BrauerGroup K) = ⟦csa hf'⟧ ↔
      IsMulCoboundary₂ (fun p : Gal(L/K) × Gal(L/K) => f p / f' p) := by
  constructor
  · intro h
    have hmul := mk_csa_mul hf (isMulCocycle₂_inv hf')
    rw [h, mk_csa_inv hf', mul_inv_cancel] at hmul
    have := (mk_csa_eq_one_iff (isMulCocycle₂_mul hf (isMulCocycle₂_inv hf'))).mp hmul
    simpa only [div_eq_mul_inv] using this
  · intro h
    obtain ⟨e⟩ := nonempty_algEquiv_of_isMulCoboundary₂ hf' hf h
    exact (Quotient.sound (IsBrauerEquivalent.of_algEquiv e)).symm

end CrossedProduct

end Basic

/-! ### The homomorphism out of `H²` -/

section Hom

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The Brauer class attached to a class in `H²(Gal(L/K), Lˣ)`: the class of the crossed product
of any cocycle representing it. -/
noncomputable def brauerOfH2 (x : H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) : BrauerGroup K :=
  ⟦CrossedProduct.csa (exists_isMulCocycle₂_H2π_eq x).choose_spec.choose⟧

variable {f f' : Gal(L/K) × Gal(L/K) → Lˣ}

/-- `brauerOfH2` is computed by the crossed product of any representing cocycle. -/
theorem brauerOfH2_apply (hf : IsMulCocycle₂ f) :
    brauerOfH2 (H2π (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) (cocyclesOfIsMulCocycle₂ hf))
      = ⟦CrossedProduct.csa hf⟧ := by
  set x := H2π (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) (cocyclesOfIsMulCocycle₂ hf) with hx
  have h := (exists_isMulCocycle₂_H2π_eq x).choose_spec.choose_spec
  rw [hx] at h
  exact (CrossedProduct.mk_csa_eq_mk_csa_iff _ hf).mpr
    ((H2π_eq_H2π_iff_isMulCoboundary₂_div _ hf).mp h)

/-- The class of a product of cocycles is the product of the classes. -/
theorem brauerOfH2_add (x y : H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) :
    brauerOfH2 (x + y) = brauerOfH2 x * brauerOfH2 y := by
  obtain ⟨f, hf, rfl⟩ := exists_isMulCocycle₂_H2π_eq x
  obtain ⟨f', hf', rfl⟩ := exists_isMulCocycle₂_H2π_eq y
  have hsum : cocyclesOfIsMulCocycle₂ hf + cocyclesOfIsMulCocycle₂ hf'
      = cocyclesOfIsMulCocycle₂ (isMulCocycle₂_mul hf hf') := Subtype.ext rfl
  rw [← map_add, hsum, brauerOfH2_apply, brauerOfH2_apply, brauerOfH2_apply,
    CrossedProduct.mk_csa_mul hf hf']

/-- The class of the zero cohomology class is trivial. -/
theorem brauerOfH2_zero :
    brauerOfH2 (0 : H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) = (1 : BrauerGroup K) := by
  have h : (0 : H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ))
      = H2π _ (cocyclesOfIsMulCocycle₂ (isMulCocycle₂_one K L)) :=
    ((H2π_eq_zero_iff_isMulCoboundary₂ (isMulCocycle₂_one K L)).mpr
      ⟨fun _ => 1, by simp⟩).symm
  rw [h, brauerOfH2_apply, CrossedProduct.mk_csa_one]

/-- **The crossed product homomorphism.**  The second cohomology group of `Gal(L/K)` with
coefficients in `Lˣ` maps to the Brauer group of `K`. -/
noncomputable def brauerHom :
    Multiplicative (H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) →* BrauerGroup K where
  toFun x := brauerOfH2 (Multiplicative.toAdd x)
  map_one' := brauerOfH2_zero
  map_mul' _ _ := brauerOfH2_add _ _

/-- The homomorphism is computed on a cocycle by its crossed product. -/
theorem brauerHom_apply (hf : IsMulCocycle₂ f) :
    brauerHom (Multiplicative.ofAdd
        (H2π (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) (cocyclesOfIsMulCocycle₂ hf)))
      = ⟦CrossedProduct.csa hf⟧ :=
  brauerOfH2_apply hf

/-- The class attached to a cohomology class is trivial only for the zero class. -/
theorem brauerOfH2_eq_one_iff (x : H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) :
    brauerOfH2 x = (1 : BrauerGroup K) ↔ x = 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_isMulCocycle₂_H2π_eq x
  rw [brauerOfH2_apply hf, CrossedProduct.mk_csa_eq_one_iff_H2π_eq_zero hf]

/-- **The crossed product homomorphism is injective.** -/
theorem brauerHom_injective :
    Function.Injective (brauerHom (K := K) (L := L)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  exact (brauerOfH2_eq_one_iff (Multiplicative.toAdd x)).mp hx

/-- The image of the crossed product homomorphism lies in the relative Brauer group. -/
theorem brauerHom_mem_relative (x : Multiplicative (H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ))) :
    brauerHom x ∈ BrauerGroup.relative K L := by
  obtain ⟨f, hf, hx⟩ := exists_isMulCocycle₂_H2π_eq (Multiplicative.toAdd x)
  have : brauerHom x = ⟦CrossedProduct.csa hf⟧ := by
    show brauerOfH2 (Multiplicative.toAdd x) = _
    rw [← hx, brauerOfH2_apply hf]
  rw [this]
  exact CrossedProduct.mk_csa_mem_relative hf

end Hom

end InverseGalois.CFT
