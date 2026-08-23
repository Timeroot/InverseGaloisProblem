import Mathlib
import InverseGalois.CFT.Brauer.SkolemNoether

/-!
# The centralizer theorem for central simple algebras

Let `K` be a field, `A` a finite-dimensional central simple `K`-algebra and `B` a `K`-subalgebra
of `A` which is a simple ring. This file studies the centralizer
`C := Subalgebra.centralizer K (B : Set A)`.

The engine is the enveloping algebra `E := ↥B ⊗[K] Aᵐᵒᵖ`, which acts on `A` by
`(b ⊗ₜ op a) • x = b * x * a`; this module is `SkolemNoether.Bimod B.val`. The ring `E` is simple
and Artinian, and the centralizer `C` is precisely the endomorphism algebra of `A` over `E`, the
isomorphism sending `c` to left multiplication by `c`. Over a simple Artinian ring every finitely
generated module is a finite direct sum of copies of one fixed simple module, so an endomorphism
algebra is a matrix algebra over the endomorphism algebra of that simple module, which is a
division ring by Schur's lemma. Simplicity of `C` follows at once, and comparing the number of
copies occurring in `A` with the number occurring in `E` yields the dimension formula.

## Main results

* `InverseGalois.CFT.Centralizer.le_centralizer_centralizer`: a subalgebra is contained in the
  centralizer of its centralizer.
* `InverseGalois.CFT.Centralizer.centralizerAlgEquivEnd`: the centralizer of `B` in `A` is the
  algebra of endomorphisms of `A` commuting with the action of `↥B ⊗[K] Aᵐᵒᵖ`.
* `InverseGalois.CFT.Centralizer.isSimpleRing_centralizer`: the centralizer of a simple
  subalgebra of a central simple algebra is a simple ring.
* `InverseGalois.CFT.Centralizer.finrank_mul_finrank_centralizer`: **the centralizer theorem**,
  `finrank K B * finrank K C = finrank K A`.
* `InverseGalois.CFT.Centralizer.centralizer_centralizer`: **the double centralizer theorem**,
  the centralizer of the centralizer of `B` is `B` itself.
* `InverseGalois.CFT.Centralizer.centralizer_eq_self_iff_finrank_sq`: a commutative simple
  subalgebra is its own centralizer exactly when the square of its dimension is the dimension
  of `A`.
* `InverseGalois.CFT.Centralizer.centralizer_eq_self_of_maximal`: a commutative subalgebra that
  is maximal among commutative subalgebras is its own centralizer.
* `InverseGalois.CFT.Centralizer.exists_algEquiv_matrix_of_centralizer_eq_range`: a subfield of
  `A` which is its own centralizer splits `A`.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u v w

open scoped TensorProduct

open Module

namespace InverseGalois.CFT

namespace Centralizer

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

variable (B : Subalgebra K A)

/-! ### The centralizer as an endomorphism algebra -/

/-- A subalgebra of `A` is contained in the centralizer of its own centralizer. -/
theorem le_centralizer_centralizer :
    B ≤ Subalgebra.centralizer K (Subalgebra.centralizer K (B : Set A) : Set A) :=
  Subalgebra.le_centralizer_centralizer K

/-- An element of the centralizer of `B` commutes with every operator coming from the action
of `↥B ⊗[K] Aᵐᵒᵖ` on `A`. -/
theorem mul_toEnd (c : Subalgebra.centralizer K (B : Set A)) (t : ↥B ⊗[K] Aᵐᵒᵖ) (x : A) :
    (c : A) * SkolemNoether.toEnd B.val t x = SkolemNoether.toEnd B.val t ((c : A) * x) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
      have hb : (b : A) * (c : A) = (c : A) * (b : A) := c.2 (b : A) b.2
      simp only [SkolemNoether.toEnd_tmul, Subalgebra.coe_val]
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hb]
  | add t₁ t₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply, LinearMap.add_apply, mul_add, h₁, h₂]

/-- Left multiplication by an element of the centralizer of `B`, as an endomorphism of `A`
regarded as a module over `↥B ⊗[K] Aᵐᵒᵖ`. -/
noncomputable def lmulEnd (c : Subalgebra.centralizer K (B : Set A)) :
    Module.End (↥B ⊗[K] Aᵐᵒᵖ) (SkolemNoether.Bimod B.val) where
  toFun x := SkolemNoether.Bimod.mk B.val ((c : A) * SkolemNoether.Bimod.val x)
  map_add' x y := mul_add (c : A) (SkolemNoether.Bimod.val x) (SkolemNoether.Bimod.val y)
  map_smul' t x :=
    congrArg (SkolemNoether.Bimod.mk B.val) (mul_toEnd B c t (SkolemNoether.Bimod.val x))

@[simp]
theorem val_lmulEnd_apply (c : Subalgebra.centralizer K (B : Set A))
    (x : SkolemNoether.Bimod B.val) :
    SkolemNoether.Bimod.val (lmulEnd B c x) = (c : A) * SkolemNoether.Bimod.val x := rfl

/-- The centralizer of `B` maps to the endomorphism algebra of `A` over `↥B ⊗[K] Aᵐᵒᵖ` by
left multiplication. -/
noncomputable def toEndAlgHom :
    Subalgebra.centralizer K (B : Set A) →ₐ[K]
      Module.End (↥B ⊗[K] Aᵐᵒᵖ) (SkolemNoether.Bimod B.val) where
  toFun := lmulEnd B
  map_one' := by
    ext x
    exact one_mul (SkolemNoether.Bimod.val x)
  map_mul' c d := by
    ext x
    exact mul_assoc (c : A) (d : A) (SkolemNoether.Bimod.val x)
  map_zero' := by
    ext x
    exact zero_mul (SkolemNoether.Bimod.val x)
  map_add' c d := by
    ext x
    exact add_mul (c : A) (d : A) (SkolemNoether.Bimod.val x)
  commutes' k := by
    ext x
    exact (Algebra.smul_def k (SkolemNoether.Bimod.val x)).symm

@[simp]
theorem toEndAlgHom_apply (c : Subalgebra.centralizer K (B : Set A)) :
    toEndAlgHom B c = lmulEnd B c := rfl

/-- Left multiplication identifies the centralizer of `B` with the endomorphisms of `A` over
`↥B ⊗[K] Aᵐᵒᵖ`. -/
theorem toEndAlgHom_bijective : Function.Bijective (toEndAlgHom B) := by
  constructor
  · intro c d h
    have h1 := congrArg
      (fun φ : Module.End (↥B ⊗[K] Aᵐᵒᵖ) (SkolemNoether.Bimod B.val) ↦
        SkolemNoether.Bimod.val (φ (SkolemNoether.Bimod.mk B.val 1))) h
    simp only [toEndAlgHom_apply, val_lmulEnd_apply, SkolemNoether.Bimod.val_mk, mul_one] at h1
    exact Subtype.ext h1
  · intro φ
    have hmem : SkolemNoether.Bimod.val (φ (SkolemNoether.Bimod.mk B.val 1)) ∈
        Subalgebra.centralizer K (B : Set A) := by
      intro g hg
      have h₁ : SkolemNoether.Bimod.val (φ (SkolemNoether.Bimod.mk B.val g))
          = SkolemNoether.Bimod.val (φ (SkolemNoether.Bimod.mk B.val 1)) * g :=
        SkolemNoether.val_apply_eq φ g
      have h₂ : SkolemNoether.Bimod.val (φ (SkolemNoether.Bimod.mk B.val (B.val ⟨g, hg⟩)))
          = B.val ⟨g, hg⟩ * SkolemNoether.Bimod.val (φ (SkolemNoether.Bimod.mk B.val 1)) :=
        SkolemNoether.val_apply_algHom φ ⟨g, hg⟩
      rw [Subalgebra.coe_val] at h₂
      rw [h₁] at h₂
      exact h₂.symm
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext x
    exact (SkolemNoether.val_apply_eq φ (SkolemNoether.Bimod.val x)).symm

/-- The centralizer of `B` in `A` is the algebra of endomorphisms of `A` commuting with the
action of `↥B ⊗[K] Aᵐᵒᵖ`. -/
noncomputable def centralizerAlgEquivEnd :
    Subalgebra.centralizer K (B : Set A) ≃ₐ[K]
      Module.End (↥B ⊗[K] Aᵐᵒᵖ) (SkolemNoether.Bimod B.val) :=
  AlgEquiv.ofBijective (toEndAlgHom B) (toEndAlgHom_bijective B)

/-! ### Endomorphism algebras of modules over a simple algebra -/

/-- The dimension of a finite product of copies of a finite-dimensional vector space. -/
private theorem finrank_pi_const (F : Type u) [Field F] (P : Type*) [AddCommGroup P]
    [Module F P] [FiniteDimensional F P] (k : ℕ) :
    finrank F (Fin k → P) = k * finrank F P := by
  rw [Module.finrank_pi_fintype F (M := fun _ : Fin k ↦ P)]
  simp

/-- For a finite-dimensional simple algebra `E` over a field `F` and a nonzero finite-dimensional
`E`-module `M`, the endomorphism algebra of `M` over `E` is a simple ring, and the product of the
dimensions of `E` and of that endomorphism algebra is the square of the dimension of `M`. -/
private theorem endAux (F : Type u) (E : Type*) [Field F] [Ring E] [Algebra F E] [IsSimpleRing E]
    [FiniteDimensional F E] (M : Type*) [AddCommGroup M] [Module F M] [Module E M]
    [IsScalarTower F E M] [FiniteDimensional F M] [Nontrivial M] :
    IsSimpleRing (Module.End E M) ∧
      finrank F E * finrank F (Module.End E M) = finrank F M * finrank F M := by
  classical
  haveI : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨P, hP⟩ := IsAtomic.exists_atom (Submodule E E)
  haveI : IsSimpleModule E P := isSimpleModule_iff_isAtom.2 hP
  haveI : FiniteDimensional F P :=
    Module.Finite.of_injective (P.subtype.restrictScalars F) P.subtype_injective
  haveI : Module.Finite E M := Module.Finite.of_restrictScalars_finite F E M
  obtain ⟨n, ⟨eM⟩⟩ := (SkolemNoether.isIsotypicOfType_of_isSimpleModule E M P).linearEquiv_fun
  obtain ⟨m, ⟨eE⟩⟩ := (SkolemNoether.isIsotypicOfType_of_isSimpleModule E E P).linearEquiv_fun
  have hM : finrank F M = n * finrank F P := by
    rw [(eM.restrictScalars F).finrank_eq, finrank_pi_const F P]
  have hE : finrank F E = m * finrank F P := by
    rw [(eE.restrictScalars F).finrank_eq, finrank_pi_const F P]
  have hEndM : finrank F (Module.End E M) = n * n * finrank F (Module.End E P) := by
    rw [(eM.conjAlgEquiv F).toLinearEquiv.finrank_eq,
      (endVecAlgEquivMatrixEnd (Fin n) F E P).toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp
  have hop : finrank F (Eᵐᵒᵖ) = finrank F E := MulOpposite.finrank
  have hEndE : finrank F E = m * m * finrank F (Module.End E P) := by
    rw [← hop, (AlgEquiv.moduleEndSelf (R := F) (A := E)).toLinearEquiv.finrank_eq,
      (eE.conjAlgEquiv F).toLinearEquiv.finrank_eq,
      (endVecAlgEquivMatrixEnd (Fin m) F E P).toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp
  have hdpos : 0 < finrank F P := finrank_pos_iff.2 (IsSimpleModule.nontrivial E P)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, zero_mul] at hE
      have : 0 < finrank F E := finrank_pos_iff.2 inferInstance
      omega
    · exact h
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, zero_mul] at hM
      have : 0 < finrank F M := finrank_pos_iff.2 inferInstance
      omega
    · exact h
  have hd : finrank F P = m * finrank F (Module.End E P) :=
    Nat.eq_of_mul_eq_mul_left hmpos (by rw [← hE, hEndE]; ring)
  refine ⟨?_, ?_⟩
  · haveI : IsSimpleRing (Module.End E P) := by
      letI : DivisionRing (Module.End E P) := Module.End.instDivisionRing
      infer_instance
    haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hnpos
    exact IsSimpleRing.of_ringEquiv
      ((eM.conjAlgEquiv F).trans (endVecAlgEquivMatrixEnd (Fin n) F E P)).symm.toRingEquiv
      inferInstance
  · rw [hEndE, hEndM, hM, hd]
    ring

/-! ### The centralizer theorem -/

section Main

variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] [IsSimpleRing B]

/-- Simplicity of the centralizer of `B` in `A`, together with the dimension formula. -/
private theorem aux :
    IsSimpleRing (Subalgebra.centralizer K (B : Set A)) ∧
      finrank K B * finrank K (Subalgebra.centralizer K (B : Set A)) = finrank K A := by
  haveI : IsSimpleRing (↑B ⊗[K] Aᵐᵒᵖ) := SkolemNoether.isSimpleRing_tensor
  haveI : Nontrivial (SkolemNoether.Bimod B.val) := inferInstanceAs (Nontrivial A)
  obtain ⟨hsimp, hdim⟩ := endAux K (↑B ⊗[K] Aᵐᵒᵖ) (SkolemNoether.Bimod B.val)
  have hC : finrank K (Subalgebra.centralizer K (B : Set A))
      = finrank K (Module.End (↑B ⊗[K] Aᵐᵒᵖ) (SkolemNoether.Bimod B.val)) :=
    (centralizerAlgEquivEnd B).toLinearEquiv.finrank_eq
  have hten : finrank K (↑B ⊗[K] Aᵐᵒᵖ) = finrank K B * finrank K A := by
    rw [Module.finrank_tensorProduct, MulOpposite.finrank]
  rw [hten, SkolemNoether.Bimod.finrank_eq] at hdim
  refine ⟨IsSimpleRing.of_ringEquiv (centralizerAlgEquivEnd B).symm.toRingEquiv hsimp, ?_⟩
  have hapos : 0 < finrank K A := Module.finrank_pos_iff.2 inferInstance
  refine Nat.eq_of_mul_eq_mul_right hapos ?_
  rw [hC, ← hdim]
  ring

/-- The centralizer of a simple `K`-subalgebra of a finite-dimensional central simple
`K`-algebra is a simple ring. -/
theorem isSimpleRing_centralizer :
    IsSimpleRing (Subalgebra.centralizer K (B : Set A)) := (aux B).1

/-- **The centralizer theorem**: for a simple `K`-subalgebra `B` of a finite-dimensional central
simple `K`-algebra `A`, the product of the dimension of `B` and the dimension of its centralizer
is the dimension of `A`. -/
theorem finrank_mul_finrank_centralizer :
    finrank K B * finrank K (Subalgebra.centralizer K (B : Set A)) = finrank K A := (aux B).2

/-- **The double centralizer theorem**: a simple `K`-subalgebra of a finite-dimensional central
simple `K`-algebra is the centralizer of its centralizer. -/
theorem centralizer_centralizer :
    Subalgebra.centralizer K (Subalgebra.centralizer K (B : Set A) : Set A) = B := by
  haveI := isSimpleRing_centralizer B
  have h1 := finrank_mul_finrank_centralizer B
  have h2 := finrank_mul_finrank_centralizer (Subalgebra.centralizer K (B : Set A))
  have hcpos : 0 < finrank K (Subalgebra.centralizer K (B : Set A)) :=
    Module.finrank_pos_iff.2 inferInstance
  have hfin : finrank K
      (Subalgebra.centralizer K (Subalgebra.centralizer K (B : Set A) : Set A))
        = finrank K B := by
    refine Nat.eq_of_mul_eq_mul_left hcpos ?_
    rw [h2, ← h1]
    ring
  exact (Subalgebra.eq_of_le_of_finrank_le (le_centralizer_centralizer B) hfin.le).symm

end Main

/-! ### Maximal commutative subalgebras -/

/-- A commutative simple `K`-subalgebra `L` of a finite-dimensional central simple `K`-algebra
is its own centralizer exactly when the square of `finrank K L` is `finrank K A`. -/
theorem centralizer_eq_self_iff_finrank_sq [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (L : Subalgebra K A) [IsSimpleRing L]
    (hL : L ≤ Subalgebra.centralizer K (L : Set A)) :
    Subalgebra.centralizer K (L : Set A) = L ↔ finrank K L * finrank K L = finrank K A := by
  have h1 := finrank_mul_finrank_centralizer L
  have hlpos : 0 < finrank K L := Module.finrank_pos_iff.2 inferInstance
  constructor
  · intro h
    rw [← h1, h]
  · intro h
    have hfin : finrank K (Subalgebra.centralizer K (L : Set A)) = finrank K L :=
      Nat.eq_of_mul_eq_mul_left hlpos (by rw [h1, h])
    exact (Subalgebra.eq_of_le_of_finrank_le hL hfin.le).symm

/-- A commutative `K`-subalgebra of `A` that is maximal among commutative `K`-subalgebras is
its own centralizer. -/
theorem centralizer_eq_self_of_maximal (L : Subalgebra K A)
    (hL : L ≤ Subalgebra.centralizer K (L : Set A))
    (hmax : ∀ L' : Subalgebra K A, L ≤ L' →
      L' ≤ Subalgebra.centralizer K (L' : Set A) → L' = L) :
    Subalgebra.centralizer K (L : Set A) = L := by
  refine le_antisymm (fun c hc ↦ ?_) hL
  have hcL : ∀ g ∈ (L : Set A), g * c = c * g := hc
  have hcomm : insert c (L : Set A) ⊆
      (Subalgebra.centralizer K (insert c (L : Set A)) : Set A) := by
    intro x hx
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rcases hx with rfl | hx
    · rcases hg with rfl | hg
      · rfl
      · exact hcL g hg
    · rcases hg with rfl | hg
      · exact (hcL x hx).symm
      · exact hL hx g hg
  have hadj : Algebra.adjoin K (insert c (L : Set A))
      ≤ Subalgebra.centralizer K (insert c (L : Set A)) := Algebra.adjoin_le hcomm
  have hstep : Algebra.adjoin K (insert c (L : Set A))
      ≤ Subalgebra.centralizer K (Algebra.adjoin K (insert c (L : Set A)) : Set A) :=
    le_trans (Algebra.adjoin_le_centralizer_centralizer K (insert c (L : Set A)))
      (Subalgebra.centralizer_le K _ _ (SetLike.coe_subset_coe.2 hadj))
  have hLle : L ≤ Algebra.adjoin K (insert c (L : Set A)) := fun x hx ↦
    Algebra.subset_adjoin (Set.mem_insert_of_mem c hx)
  have heq := hmax _ hLle hstep
  have hcmem : c ∈ Algebra.adjoin K (insert c (L : Set A)) :=
    Algebra.subset_adjoin (Set.mem_insert c _)
  rwa [heq] at hcmem

/-! ### Splitting by a self-centralizing subfield -/

section Splitting

variable {L : Type w} [Field L] [Algebra K L]

/-- A copy of `A` carrying the `L`-module structure given by right multiplication along a
`K`-algebra homomorphism `f : L →ₐ[K] A`. -/
def RMod (_f : L →ₐ[K] A) : Type v := A

namespace RMod

/-- The tautological bijection from `A` to `RMod f`. -/
def mk (_f : L →ₐ[K] A) : A → RMod _f := id

/-- The tautological bijection from `RMod f` to `A`. -/
def val {f : L →ₐ[K] A} : RMod f → A := id

/-- The two tautological bijections attached to `RMod f` are mutually inverse. -/
@[simp] theorem val_mk (f : L →ₐ[K] A) (x : A) : val (mk f x) = x := rfl

/-- The two tautological bijections attached to `RMod f` are mutually inverse. -/
@[simp] theorem mk_val {f : L →ₐ[K] A} (x : RMod f) : mk f (val x) = x := rfl

/-- Elements of `RMod f` are determined by their underlying elements of `A`. -/
theorem val_injective {f : L →ₐ[K] A} : Function.Injective (val : RMod f → A) := fun _ _ h ↦ h

instance (f : L →ₐ[K] A) : AddCommGroup (RMod f) := inferInstanceAs (AddCommGroup A)

instance (f : L →ₐ[K] A) : Module K (RMod f) := inferInstanceAs (Module K A)

instance (f : L →ₐ[K] A) [FiniteDimensional K A] : FiniteDimensional K (RMod f) :=
  inferInstanceAs (FiniteDimensional K A)

instance (f : L →ₐ[K] A) [Nontrivial A] : Nontrivial (RMod f) :=
  inferInstanceAs (Nontrivial A)

/-- The ring homomorphism `L →+* Aᵐᵒᵖ` underlying right multiplication along `f`. -/
def rop (f : L →ₐ[K] A) : L →+* Aᵐᵒᵖ where
  toFun l := MulOpposite.op (f l)
  map_one' := by simp
  map_mul' l l' := by
    have h : f l * f l' = f l' * f l := by
      rw [← map_mul, ← map_mul, mul_comm l l']
    simp only [map_mul, ← MulOpposite.op_mul, h]
  map_zero' := by simp
  map_add' l l' := by simp

instance module (f : L →ₐ[K] A) : Module L (RMod f) :=
  letI : Module Aᵐᵒᵖ (RMod f) := inferInstanceAs (Module Aᵐᵒᵖ A)
  Module.compHom (RMod f) (rop f)

/-- The scalar action of `L` on `RMod f` is right multiplication along `f`. -/
@[simp] theorem val_smul (f : L →ₐ[K] A) (l : L) (x : RMod f) : val (l • x) = val x * f l := rfl

instance (f : L →ₐ[K] A) : IsScalarTower K L (RMod f) where
  smul_assoc k l x := by
    refine val_injective ?_
    have h1 : val ((k • l) • x) = val x * (algebraMap K A k * f l) := by
      rw [val_smul, Algebra.smul_def, map_mul, f.commutes k]
    have h2 : val (k • l • x) = algebraMap K A k * (val x * f l) := by
      show k • val (l • x) = _
      rw [val_smul, Algebra.smul_def]
    rw [h1, h2, ← mul_assoc, ← mul_assoc, Algebra.commutes k (val x)]

/-- The `K`-dimension of `RMod f` is the `K`-dimension of `A`. -/
@[simp] theorem finrank_eq (f : L →ₐ[K] A) : finrank K (RMod f) = finrank K A := rfl

end RMod

/-- Left multiplication of `A` on `RMod f`, as a `K`-algebra homomorphism into the algebra of
`L`-linear endomorphisms. -/
def lmulRight (f : L →ₐ[K] A) : A →ₐ[K] Module.End L (RMod f) where
  toFun a :=
    { toFun := fun x ↦ RMod.mk f (a * RMod.val x)
      map_add' := fun x y ↦ mul_add a (RMod.val x) (RMod.val y)
      map_smul' := fun l x ↦ RMod.val_injective (by
        simp only [RMod.val_mk, RMod.val_smul, RingHom.id_apply, mul_assoc]) }
  map_one' := by
    ext x
    exact one_mul (RMod.val x)
  map_mul' a b := by
    ext x
    exact mul_assoc a b (RMod.val x)
  map_zero' := by
    ext x
    exact zero_mul (RMod.val x)
  map_add' a b := by
    ext x
    exact add_mul a b (RMod.val x)
  commutes' k := by
    ext x
    exact (Algebra.smul_def k (RMod.val x)).symm

/-- Left multiplication on `RMod f` is left multiplication in `A`. -/
@[simp] theorem val_lmulRight (f : L →ₐ[K] A) (a : A) (x : RMod f) :
    RMod.val (lmulRight f a x) = a * RMod.val x := rfl

/-- The canonical `L`-algebra homomorphism from `L ⊗[K] A` to the algebra of `L`-linear
endomorphisms of `A` for the right action of `L` along `f`. -/
noncomputable def toEndSplit (f : L →ₐ[K] A) :
    (L ⊗[K] A) →ₐ[L] Module.End L (RMod f) :=
  Algebra.TensorProduct.lift (Algebra.ofId L (Module.End L (RMod f))) (lmulRight f)
    (fun l a ↦ LinearMap.ext fun x ↦ RMod.val_injective (by
      simp only [Module.End.mul_apply, Algebra.ofId_apply, Module.algebraMap_end_eq_smul_id,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq, RMod.val_smul, val_lmulRight, mul_assoc]))

variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- A subfield of a finite-dimensional central simple `K`-algebra `A` which is its own
centralizer splits `A`: extending scalars to it turns `A` into a matrix algebra. -/
theorem exists_algEquiv_matrix_of_centralizer_eq_range (f : L →ₐ[K] A)
    (hf : Subalgebra.centralizer K (f.range : Set A) = f.range) :
    ∃ n : ℕ, Nonempty ((L ⊗[K] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  classical
  haveI : FiniteDimensional K L :=
    Module.Finite.of_injective (f.toLinearMap) f.toRingHom.injective
  have hLr : finrank K L = finrank K f.range :=
    (AlgEquiv.ofInjective f f.toRingHom.injective).toLinearEquiv.finrank_eq
  haveI : IsSimpleRing f.range :=
    IsSimpleRing.of_ringEquiv (AlgEquiv.ofInjective f f.toRingHom.injective).toRingEquiv
      inferInstance
  have hsq : finrank K L * finrank K L = finrank K A := by
    have hc := finrank_mul_finrank_centralizer f.range
    rw [hf] at hc
    rw [hLr, hc]
  haveI : Module.Finite L (RMod f) := Module.Finite.of_restrictScalars_finite K L (RMod f)
  have htow : finrank K L * finrank L (RMod f) = finrank K (RMod f) :=
    Module.finrank_mul_finrank K L (RMod f)
  rw [RMod.finrank_eq] at htow
  have hlpos : 0 < finrank K L := Module.finrank_pos_iff.2 inferInstance
  have hr : finrank L (RMod f) = finrank K L :=
    Nat.eq_of_mul_eq_mul_left hlpos (by rw [htow, hsq])
  haveI : IsSimpleRing (A ⊗[K] L) := IsSimpleRing.tensorProduct_of_isCentral
  haveI : IsSimpleRing (L ⊗[K] A) :=
    IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm K A L).toRingEquiv inferInstance
  have hinj : Function.Injective (toEndSplit f) := (toEndSplit f).toRingHom.injective
  have hdim : finrank L (L ⊗[K] A) = finrank L (Module.End L (RMod f)) := by
    rw [Module.finrank_baseChange, Module.finrank_linearMap, hr, hsq]
  have hbij : Function.Bijective (toEndSplit f) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  exact ⟨finrank L (RMod f),
    ⟨(AlgEquiv.ofBijective (toEndSplit f) hbij).trans (algEquivMatrix (finBasis L (RMod f)))⟩⟩

end Splitting

end Centralizer

end InverseGalois.CFT
