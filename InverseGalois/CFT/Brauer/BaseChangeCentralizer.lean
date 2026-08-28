/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.Centralizer

/-!
# Extending scalars to a subfield of a central simple algebra

Let `A` be a finite-dimensional central simple algebra over a field `K`, let `L` be a field between
`K` and `A`, and let `B` be the centralizer of `L` in `A`.  Right multiplication makes `A` a module
over the opposite ring of `B`, and left multiplication together with the right action of `L`
identifies `L ⊗[K] A` with the algebra of `B`-linear endomorphisms of `A`.  Counting dimensions
shows that `A` is free of rank `[L : K]` over `B`, so that endomorphism algebra is the algebra of
`[L : K]`-by-`[L : K]` matrices over `B`.

Extending scalars to `L` therefore replaces `A` by matrices over the centralizer of `L`, which is
the computation of the restriction map on Brauer groups.  Taking `B` to be `L` itself recovers the
statement that a self-centralizing subfield splits the algebra.

## Main definitions

* `InverseGalois.CFT.Centralizer.BMod`: a copy of `A` carrying the right action of `B`.
* `InverseGalois.CFT.Centralizer.toEndB`: the canonical map from `L ⊗[K] A` to the `B`-linear
  endomorphisms of `A`.

## Main results

* `InverseGalois.CFT.Centralizer.exists_algEquiv_matrix_of_range_eq_centralizer`: **extending
  scalars to a subfield turns a central simple algebra into matrices over the centralizer of that
  subfield.**

## Tags

central simple algebra, centralizer, base change, Brauer group
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u v w t

open scoped TensorProduct

open Module

namespace InverseGalois.CFT.Centralizer

variable {K : Type u} {A : Type v} {L : Type w} {B : Type t}
variable [Field K] [Ring A] [Algebra K A] [Field L] [Algebra K L]
variable [Ring B] [Algebra K B] [Algebra L B] [IsScalarTower K L B]

/-! ### The algebra as a right module over a subalgebra -/

/-- A copy of `A` carrying the right action of `B` along a `K`-algebra homomorphism
`g : B →ₐ[K] A`, together with the right action of `L` obtained from it.  The subfield `L` is
recorded in the type so that the two scalar actions of `K` and of `L` stay apart. -/
def BMod (_L : Type w) (_g : B →ₐ[K] A) : Type v := A

namespace BMod

/-- The tautological bijection from `A` to `BMod L g`. -/
def mk (_L : Type w) (_g : B →ₐ[K] A) : A → BMod _L _g := id

/-- The tautological bijection from `BMod L g` to `A`. -/
def val {g : B →ₐ[K] A} : BMod L g → A := id

omit [Field L] [Algebra K L] [Algebra L B] [IsScalarTower K L B] in
/-- The two tautological bijections attached to `BMod L g` are mutually inverse. -/
@[simp] theorem val_mk (g : B →ₐ[K] A) (x : A) : val (mk L g x) = x := rfl

omit [Field L] [Algebra K L] [Algebra L B] [IsScalarTower K L B] in
/-- The two tautological bijections attached to `BMod L g` are mutually inverse. -/
@[simp] theorem mk_val {g : B →ₐ[K] A} (x : BMod L g) : mk L g (val x) = x := rfl

omit [Field L] [Algebra K L] [Algebra L B] [IsScalarTower K L B] in
/-- Elements of `BMod L g` are determined by their underlying elements of `A`. -/
theorem val_injective {g : B →ₐ[K] A} : Function.Injective (val : BMod L g → A) := fun _ _ h ↦ h

instance (g : B →ₐ[K] A) : AddCommGroup (BMod L g) := inferInstanceAs (AddCommGroup A)

instance (g : B →ₐ[K] A) : Module K (BMod L g) := inferInstanceAs (Module K A)

instance (g : B →ₐ[K] A) [FiniteDimensional K A] : FiniteDimensional K (BMod L g) :=
  inferInstanceAs (FiniteDimensional K A)

instance (g : B →ₐ[K] A) [Nontrivial A] : Nontrivial (BMod L g) :=
  inferInstanceAs (Nontrivial A)

/-- The ring homomorphism `Bᵐᵒᵖ →+* Aᵐᵒᵖ` underlying right multiplication along `g`. -/
def rop (g : B →ₐ[K] A) : Bᵐᵒᵖ →+* Aᵐᵒᵖ where
  toFun b := MulOpposite.op (g b.unop)
  map_one' := by simp
  map_mul' x y := by
    simp only [MulOpposite.unop_mul, map_mul, ← MulOpposite.op_mul]
  map_zero' := by simp
  map_add' x y := by simp

instance module (g : B →ₐ[K] A) : Module Bᵐᵒᵖ (BMod L g) :=
  letI : Module Aᵐᵒᵖ (BMod L g) := inferInstanceAs (Module Aᵐᵒᵖ A)
  Module.compHom (BMod L g) (rop g)

omit [Field L] [Algebra K L] [Algebra L B] [IsScalarTower K L B] in
/-- The scalar action of the opposite of `B` on `BMod L g` is right multiplication along `g`. -/
@[simp] theorem val_smul (g : B →ₐ[K] A) (b : Bᵐᵒᵖ) (x : BMod L g) :
    val (b • x) = val x * g b.unop := rfl

omit [Field L] [Algebra K L] [Algebra L B] [IsScalarTower K L B] in
/-- The scalar action of `K` on `BMod L g` is multiplication in `A`. -/
@[simp] theorem val_smulK (g : B →ₐ[K] A) (k : K) (x : BMod L g) :
    val (k • x) = algebraMap K A k * val x := Algebra.smul_def k (val x)

instance moduleL (g : B →ₐ[K] A) : Module L (BMod L g) :=
  Module.compHom (BMod L g) (algebraMap L Bᵐᵒᵖ)

omit [Algebra K L] [IsScalarTower K L B] in
/-- The scalar action of `L` on `BMod L g` is right multiplication along `g`. -/
@[simp] theorem val_smulL (g : B →ₐ[K] A) (l : L) (x : BMod L g) :
    val (l • x) = val x * g (algebraMap L B l) := rfl

instance (g : B →ₐ[K] A) : IsScalarTower K Bᵐᵒᵖ (BMod L g) where
  smul_assoc k b x := val_injective <| by
    rw [val_smul, val_smulK, val_smul, MulOpposite.unop_smul, Algebra.smul_def, map_mul,
      AlgHom.commutes, ← mul_assoc, ← Algebra.commutes k (val x), mul_assoc]

instance (g : B →ₐ[K] A) : IsScalarTower L Bᵐᵒᵖ (BMod L g) where
  smul_assoc l b x := val_injective <| by
    rw [val_smul, val_smulL, val_smul, MulOpposite.unop_smul, Algebra.smul_def,
      Algebra.commutes, map_mul, mul_assoc]

instance (g : B →ₐ[K] A) : IsScalarTower K L (BMod L g) where
  smul_assoc k l x := val_injective <| by
    rw [val_smulL, val_smulK, val_smulL, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, map_mul, AlgHom.commutes, ← mul_assoc, ← mul_assoc,
      Algebra.commutes k (val x)]

instance (g : B →ₐ[K] A) : SMulCommClass Bᵐᵒᵖ K (BMod L g) where
  smul_comm b k x := val_injective <| by
    rw [val_smul, val_smulK, val_smulK, val_smul, mul_assoc]

omit [Field L] [Algebra K L] [Algebra L B] [IsScalarTower K L B] in
/-- The `K`-dimension of `BMod L g` is the `K`-dimension of `A`. -/
@[simp] theorem finrank_eq (g : B →ₐ[K] A) : finrank K (BMod L g) = finrank K A := rfl

end BMod

/-- Left multiplication of `A` on `BMod L g`, as a `K`-algebra homomorphism into the algebra of
endomorphisms commuting with the right action of `B`. -/
def lmulB (g : B →ₐ[K] A) : A →ₐ[K] Module.End Bᵐᵒᵖ (BMod L g) where
  toFun a :=
    { toFun := fun x ↦ BMod.mk L g (a * BMod.val x)
      map_add' := fun x y ↦ mul_add a (BMod.val x) (BMod.val y)
      map_smul' := fun b x ↦ BMod.val_injective (by
        simp only [BMod.val_mk, BMod.val_smul, RingHom.id_apply, mul_assoc]) }
  map_one' := by
    ext x
    exact one_mul (BMod.val x)
  map_mul' a b := by
    ext x
    exact mul_assoc a b (BMod.val x)
  map_zero' := by
    ext x
    exact zero_mul (BMod.val x)
  map_add' a b := by
    ext x
    exact add_mul a b (BMod.val x)
  commutes' k := by
    ext x
    exact (Algebra.smul_def k (BMod.val x)).symm

omit [Field L] [Algebra K L] [Algebra L B] [IsScalarTower K L B] in
/-- Left multiplication on `BMod L g` is left multiplication in `A`. -/
@[simp] theorem val_lmulB (g : B →ₐ[K] A) (a : A) (x : BMod L g) :
    BMod.val (lmulB g a x) = a * BMod.val x := rfl

/-- The canonical `L`-algebra homomorphism from `L ⊗[K] A` to the algebra of endomorphisms of `A`
commuting with the right action of `B`: the first factor acts by right multiplication and the
second by left multiplication. -/
noncomputable def toEndB (g : B →ₐ[K] A) [SMulCommClass Bᵐᵒᵖ L (BMod L g)] :
    (L ⊗[K] A) →ₐ[L] Module.End Bᵐᵒᵖ (BMod L g) :=
  Algebra.TensorProduct.lift (Algebra.ofId L (Module.End Bᵐᵒᵖ (BMod L g))) (lmulB g)
    (fun l a ↦ LinearMap.ext fun x ↦ BMod.val_injective (by
      simp only [Module.End.mul_apply, Algebra.ofId_apply, Module.algebraMap_end_eq_smul_id,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq, BMod.val_smulL, val_lmulB, mul_assoc]))

/-! ### Base change to a subfield -/

variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- **Extending scalars to a subfield turns a central simple algebra into matrices over the
centralizer of that subfield.**  Here the subfield is the image of `L` in `A` and the centralizer
is the image of `B`. -/
theorem exists_algEquiv_matrix_of_range_eq_centralizer (g : B →ₐ[K] A)
    (hginj : Function.Injective g)
    (hgr : g.range =
      Subalgebra.centralizer K ((g.comp (IsScalarTower.toAlgHom K L B)).range : Set A)) :
    Nonempty ((L ⊗[K] A) ≃ₐ[L]
      Matrix (Fin (finrank K L)) (Fin (finrank K L)) B) := by
  classical
  set f : L →ₐ[K] A := g.comp (IsScalarTower.toAlgHom K L B) with hf
  have hfl : ∀ l : L, f l = g (algebraMap L B l) := fun _ ↦ rfl
  -- Elements of `B` commute with elements of `L` inside `A`.
  have hcomm : ∀ (l : L) (b : B), g (algebraMap L B l) * g b = g b * g (algebraMap L B l) := by
    intro l b
    have hb : g b ∈ Subalgebra.centralizer K ((f.range : Set A)) := by
      rw [← hgr]; exact ⟨b, rfl⟩
    have := hb (f l) ⟨l, rfl⟩
    rw [hfl] at this
    exact this
  -- Finiteness and simplicity of the two subalgebras.
  haveI : FiniteDimensional K L :=
    Module.Finite.of_injective f.toLinearMap f.toRingHom.injective
  haveI : FiniteDimensional K B := Module.Finite.of_injective g.toLinearMap hginj
  haveI : Module.Finite L B := Module.Finite.of_restrictScalars_finite K L B
  have hLr : finrank K L = finrank K f.range :=
    (AlgEquiv.ofInjective f f.toRingHom.injective).toLinearEquiv.finrank_eq
  haveI : IsSimpleRing f.range :=
    IsSimpleRing.of_ringEquiv (AlgEquiv.ofInjective f f.toRingHom.injective).toRingEquiv
      inferInstance
  haveI hCs : IsSimpleRing ↥(Subalgebra.centralizer K ((f.range : Set A))) :=
    isSimpleRing_centralizer f.range
  have egr : B ≃ₐ[K] ↥g.range := AlgEquiv.ofInjective g hginj
  rw [hgr] at egr
  haveI : IsSimpleRing B := IsSimpleRing.of_ringEquiv egr.symm.toRingEquiv hCs
  -- The dimension count.
  have hBC : finrank K B = finrank K ↥(Subalgebra.centralizer K ((f.range : Set A))) :=
    egr.toLinearEquiv.finrank_eq
  have hdA : finrank K L * finrank K B = finrank K A := by
    rw [hLr, hBC]
    exact finrank_mul_finrank_centralizer f.range
  have hLpos : 0 < finrank K L := Module.finrank_pos_iff.2 inferInstance
  have hLB : finrank K L * finrank L B = finrank K B := Module.finrank_mul_finrank K L B
  -- `A` is free of rank `[L : K]` over `B`.
  have hfree : finrank K (BMod L g) = finrank K (Fin (finrank K L) → B) := by
    rw [BMod.finrank_eq, Module.finrank_pi_fintype K (M := fun _ : Fin (finrank K L) ↦ B)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact hdA.symm
  obtain ⟨e⟩ := SkolemNoether.nonempty_linearEquiv_of_finrank_eq K Bᵐᵒᵖ (BMod L g)
    (Fin (finrank K L) → B) hfree
  -- The three identifications assembling the endomorphism algebra into matrices.
  letI : SMulCommClass Bᵐᵒᵖ L (BMod L g) := ⟨fun b l x ↦ BMod.val_injective (by
    show (BMod.val x * g (algebraMap L B l)) * g b.unop
      = (BMod.val x * g b.unop) * g (algebraMap L B l)
    rw [mul_assoc, mul_assoc, hcomm l b.unop])⟩
  let E : Module.End Bᵐᵒᵖ (BMod L g) ≃ₐ[L]
      Matrix (Fin (finrank K L)) (Fin (finrank K L)) B :=
    (e.conjAlgEquiv L).trans
      ((endVecAlgEquivMatrixEnd (Fin (finrank K L)) L Bᵐᵒᵖ B).trans
        (AlgEquiv.mapMatrix (AlgEquiv.moduleEndSelfOp (R := L) (A := B)).symm))
  haveI : FiniteDimensional L (Module.End Bᵐᵒᵖ (BMod L g)) :=
    Module.Finite.equiv E.symm.toLinearEquiv
  -- `L ⊗[K] A` is simple, so the canonical map is injective, and the dimensions agree.
  haveI : IsSimpleRing (A ⊗[K] L) := IsSimpleRing.tensorProduct_of_isCentral
  haveI : IsSimpleRing (L ⊗[K] A) :=
    IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm K A L).toRingEquiv inferInstance
  haveI : Nontrivial (Module.End Bᵐᵒᵖ (BMod L g)) := inferInstance
  have hinj : Function.Injective (toEndB g) :=
    RingHom.injective (S := Module.End Bᵐᵒᵖ (BMod L g)) (toEndB g).toRingHom
  have hdim : finrank L (L ⊗[K] A) = finrank L (Module.End Bᵐᵒᵖ (BMod L g)) := by
    rw [Module.finrank_baseChange, E.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp only [Fintype.card_fin]
    rw [mul_assoc, hLB]
    exact hdA.symm
  have hbij : Function.Bijective (toEndB g) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  exact ⟨(AlgEquiv.ofBijective (toEndB g) hbij).trans E⟩

end InverseGalois.CFT.Centralizer
