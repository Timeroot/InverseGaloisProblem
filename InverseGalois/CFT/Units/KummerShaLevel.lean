/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.KummerShaBot
import InverseGalois.CFT.Units.NakayamaSpanLocal

/-!
# The coefficients of a lifting problem, as a representation of the Galois group of the level

The everywhere locally trivial classes of a level are read, through Kummer theory, on the first
cohomology of the Galois group of the level with coefficients in the units of the level tensored
with the homomorphisms of the roots of unity into the kernel of the lifting problem.  That reading
was set up against an arbitrary representation identified with the tensor product, because the
identification is what the cohomological argument uses; but there is a canonical choice, namely the
homomorphisms themselves, with the Galois group acting by transport of structure.  Making that
choice removes the representation, the identification and its equivariance from every statement, and
leaves conditions which mention only the group, the extension and the kernel.

With the choice made, the two conditions under which the everywhere locally trivial classes of a
level all vanish become: the homomorphisms of the roots of unity into the kernel have no complete
cohomology over the Galois group of the level two degrees below zero, and the comparison of Tate and
Nakayama spans there.  The second is itself a statement about the finite group alone once the ideles
killed by the prime are decomposed place by place, so **the whole local-global content of the second
cohomological obstruction is three vanishing statements about complete cohomology of subgroups of
the Galois group of the level.**

## Main results

* `InverseGalois.CFT.kummerHomRep`: **the homomorphisms of the roots of unity into the kernel of a
  lifting problem, as a representation of the Galois group of the level.**
* `InverseGalois.CFT.kummerHomTensorEquiv_smul`: the tensor product of the units of the level with
  those homomorphisms is the underlying module of the tensor product representation, equivariantly.
* `InverseGalois.CFT.sha1Level_eq_bot_of_spanAt`: **the everywhere locally trivial classes of a
  level all vanish** as soon as the comparison of Tate and Nakayama spans at these coefficients in
  degree minus two and they have no complete cohomology there.
* `InverseGalois.CFT.sha1Level_eq_bot_of_isZero_local`: **the same, from vanishing statements about
  the finite group alone** — at the stabiliser of every place inside a Sylow subgroup, at the whole
  Sylow subgroup, and over the Galois group of the level.

## Tags

number field, Kummer theory, embedding problem, locally trivial, Tate-Nakayama, Sylow subgroup
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain Limits MulAction NumberField Tate

open scoped Pointwise TensorProduct

noncomputable section

/-! ### The homomorphisms into the kernel are killed by the prime -/

section Torsion

variable {M E : Type*} [CommGroup M] [CommGroup E] {p : ℕ}

/-- **The homomorphisms of a group into a group killed by a prime are killed by that prime**, read
additively. -/
theorem nsmul_additive_hom_eq_zero (hEp : ∀ e : E, e ^ p = 1) (w : Additive (M →* E)) :
    p • w = 0 :=
  Additive.toMul.injective (MonoidHom.ext fun m => by
    show (Additive.toMul w ^ p) m = (1 : M →* E) m
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, hEp])

end Torsion

/-! ### The canonical representation on the homomorphisms -/

section HomRep

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]

variable (M E) in
/-- **The Galois group acts on the homomorphisms of the roots of unity into the kernel of a lifting
problem by additive automorphisms of the additive copy**, by transport of structure. -/
def kummerHomAut : Gal(Ω/k) →* AddAut (Additive (M →* E)) where
  toFun σ := MulEquiv.toAdditive (MulDistribMulAction.toMulAut Gal(Ω/k) (M →* E) σ)
  map_one' := AddEquiv.ext fun w => Additive.toMul.injective (one_homSMul w.toMul)
  map_mul' σ τ := AddEquiv.ext fun w =>
    Additive.toMul.injective (homSMul_comp σ τ w.toMul).symm

omit [IsGalois k Ω] in
@[simp]
theorem kummerHomAut_apply (σ : Gal(Ω/k)) (w : Additive (M →* E)) :
    kummerHomAut M E σ w = Additive.ofMul (σ • w.toMul) := rfl

variable {K : IntermediateField k Ω} [Normal k ↥K]
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivEK : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)

omit [IsGalois k Ω] [Normal k ↥K] in
include htriv htrivEK in
/-- The subgroup fixing the level acts trivially on the homomorphisms, so the action descends to the
Galois group of the level. -/
theorem kummerHomAut_eq_one_of_mem_fixingSubgroup {σ : Gal(Ω/k)} (hσ : σ ∈ K.fixingSubgroup) :
    kummerHomAut M E σ = 1 :=
  AddEquiv.ext fun w => Additive.toMul.injective
    (homSMul_eq_self_of_mem_fixingSubgroup htriv htrivEK hσ w.toMul)

variable (M E) in
/-- **The action of the Galois group of the level on the homomorphisms of the roots of unity into
the kernel of a lifting problem.** -/
def kummerHomAutLevel : Gal(↥K/k) →* AddAut (Additive (M →* E)) :=
  (QuotientGroup.lift K.fixingSubgroup (kummerHomAut M E)
      fun _ hn => kummerHomAut_eq_one_of_mem_fixingSubgroup htriv htrivEK hn).comp
    (quotientFixingSubgroupEquiv K).symm.toMonoidHom

/-- The descended action is the original one, read on a restriction. -/
theorem kummerHomAutLevel_restrictNormalHom (σ : Gal(Ω/k)) :
    kummerHomAutLevel M E htriv htrivEK (AlgEquiv.restrictNormalHom ↥K σ)
      = kummerHomAut M E σ := by
  have hσ : (quotientFixingSubgroupEquiv K).symm (AlgEquiv.restrictNormalHom ↥K σ)
      = (QuotientGroup.mk σ : Gal(Ω/k) ⧸ K.fixingSubgroup) :=
    (quotientFixingSubgroupEquiv K).symm_apply_eq.2 (quotientFixingSubgroupEquiv_mk K σ).symm
  simp only [kummerHomAutLevel, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hσ]
  rfl

variable (M E) in
/-- **The homomorphisms of the roots of unity into the kernel of a lifting problem, as a
representation of the Galois group of the level.** -/
def kummerHomRep : Rep ℤ Gal(↥K/k) := repOfAddAut (kummerHomAutLevel M E htriv htrivEK)

@[simp]
theorem kummerHomRep_ρ_apply (σ : Gal(↥K/k)) (w : Additive (M →* E)) :
    (kummerHomRep M E htriv htrivEK).ρ σ w = kummerHomAutLevel M E htriv htrivEK σ w := rfl

/-! ### The tensor product with the units of the level -/

section Tensor

variable [NumberField k] [NumberField ↥K] [IsGalois k ↥K]
variable [ActsTrivially K.fixingSubgroup (M →* E)]

variable (M E) in
/-- The tensor product of the units of the level with the homomorphisms of the roots of unity into
the kernel is the underlying module of the tensor product representation, on the nose. -/
def kummerHomTensorEquiv :
    Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)
      ≃+ ↥(tensorObj (globalUnitsRep k ↥K) (kummerHomRep M E htriv htrivEK)).V :=
  AddEquiv.refl _

omit [NumberField k] [NumberField ↥K] [IsGalois k ↥K] in
/-- **The identification of the tensor product with the underlying module of the tensor product
representation is equivariant** for the Galois group of the level. -/
theorem kummerHomTensorEquiv_smul (g : Gal(Ω/k) ⧸ K.fixingSubgroup)
    (t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    kummerHomTensorEquiv M E htriv htrivEK (g • t)
      = (tensorObj (globalUnitsRep k ↥K) (kummerHomRep M E htriv htrivEK)).ρ
          (quotientFixingSubgroupEquiv K g) (kummerHomTensorEquiv M E htriv htrivEK t) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  refine TensorProduct.induction_on t ?_ (fun a b => ?_) (fun x y hx hy => ?_)
  · simp
  · show Additive.ofMul (σ • a.toMul) ⊗ₜ[ℤ] Additive.ofMul (σ • b.toMul)
        = (tensorObj (globalUnitsRep k ↥K) (kummerHomRep M E htriv htrivEK)).ρ
            (quotientFixingSubgroupEquiv K (QuotientGroup.mk σ)) (a ⊗ₜ[ℤ] b)
    rw [tensorObj_ρ_tmul, quotientFixingSubgroupEquiv_mk, kummerHomRep_ρ_apply,
      kummerHomAutLevel_restrictNormalHom, kummerHomAut_apply]
    rfl
  · rw [smul_add, _root_.map_add, _root_.map_add, _root_.map_add, hx, hy]

omit [NumberField k] [NumberField ↥K] [IsGalois k ↥K]
  [ActsTrivially K.fixingSubgroup (M →* E)] in
/-- The identification of the tensor product with the underlying module of the tensor product
representation moves only the second factor, and moves it by the identity. -/
theorem kummerHomTensorEquiv_eq_map (t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    kummerHomTensorEquiv M E htriv htrivEK t
      = TensorProduct.map LinearMap.id
          (LinearMap.id : Additive (M →* E) →ₗ[ℤ]
            ↥(kummerHomRep M E htriv htrivEK).V) t := by
  rw [TensorProduct.map_id]
  rfl

end Tensor

end HomRep

/-! ### The everywhere locally trivial classes of a level, at the canonical coefficients -/

section Vanish

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω} [NumberField ↥K] [K.fixingSubgroup.Normal] [Normal k ↥K]
variable [IsGalois k ↥K]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/k) M] {ιK : M →* (↥K)ˣ}
variable {p d : ℕ} [Fact p.Prime] [NeZero p] [IsCyclic M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (hK : IsKummerData ↥K Ω M ιK p)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivEK : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable {J : Type} [Fintype J] [DecidableEq J] (α : E ≃* (J → M)) (hEp : ∀ e : E, e ^ p = 1)
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m))
variable [ActsTrivially K.fixingSubgroup (M →* E)] [Finite Gal(↥K/k)]
variable (eM : Additive (M →* E) ≃+ (Fin d → ZMod p))
variable (hroot : ∀ x : Ωˣ, ∃ y : Ωˣ, y ^ p = x)
variable (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))

include hK α hEp hfix eM hroot in
/-- **The everywhere locally trivial classes of a level all vanish**, as soon as the comparison of
Tate and Nakayama spans at the homomorphisms of the roots of unity into the kernel in degree minus
two and those homomorphisms have no complete cohomology there.  This is the vanishing of the second
cohomological obstruction with the auxiliary representation, the identification and its equivariance
all removed: what is left is a condition on the extension and a condition on the finite group. -/
theorem sha1Level_eq_bot_of_spanAt
    (hspan : HasIdeleClassNakayamaSpanAt k ↥K p (kummerHomRep M E htriv htrivEK) (-2))
    (hzero : ∀ y : ↥(tateModule (kummerHomRep M E htriv htrivEK) (-2)), y = 0) :
    sha1Level E K.fixingSubgroup hop (decompositionSubgroups k Ω) = ⊥ :=
  sha1Level_eq_bot_of_span (ρ := LinearMap.id) hK htriv htrivEK α hEp hfix _
    (kummerHomTensorEquiv M E htriv htrivEK) (kummerHomTensorEquiv_smul htriv htrivEK)
    (kummerHomTensorEquiv_eq_map htriv htrivEK) eM hroot hop eM
    (fun _ => nsmul_additive_hom_eq_zero hEp _) hspan hzero

include hK α hEp hfix eM hroot in
/-- **The everywhere locally trivial classes of a level all vanish as soon as three complete
cohomology groups of subgroups of the Galois group of the level do**: over a Sylow subgroup for the
prime, the stabiliser of every place of the level has none with coefficients the roots of unity of
the completion tensored with the homomorphisms into the kernel, in degree two; the whole Sylow
subgroup has none with coefficients the roots of unity of the level tensored with those
homomorphisms, in degree three; and the Galois group of the level has none with coefficients the
homomorphisms themselves, two degrees below zero.  None of the three mentions the lifting problem
beyond its kernel, and each is a vanishing statement about a finite group. -/
theorem sha1Level_eq_bot_of_isZero_local
    (h₁ : ∀ (P : Sylow p Gal(↥K/k)) (w : InfinitePlace ↥K), IsZero
      (tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(↥K/k) w)) (R := w.Completion)).comp
          (stabilizerSubgroupHom (P : Subgroup Gal(↥K/k)) w)) (p : ℤ))
        (resObj (stabilizer ↥(P : Subgroup Gal(↥K/k)) w)
          (resObj (P : Subgroup Gal(↥K/k)) (kummerHomRep M E htriv htrivEK)))) 2))
    (h₂ : ∀ (P : Sylow p Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)), IsZero
      (tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(↥K/k) v)) (R := v.adicCompletion ↥K)).comp
          (stabilizerSubgroupHom (P : Subgroup Gal(↥K/k)) v)) (p : ℤ))
        (resObj (stabilizer ↥(P : Subgroup Gal(↥K/k)) v)
          (resObj (P : Subgroup Gal(↥K/k)) (kummerHomRep M E htriv htrivEK)))) 2))
    (hU : ∀ P : Sylow p Gal(↥K/k), IsZero (tateModule (resObj (P : Subgroup Gal(↥K/k))
      (tensorObj (torsionRep (globalUnitsAut (k := k) (K := ↥K)) (p : ℤ))
        (kummerHomRep M E htriv htrivEK))) 3))
    (hzero : ∀ y : ↥(tateModule (kummerHomRep M E htriv htrivEK) (-2)), y = 0) :
    sha1Level E K.fixingSubgroup hop (decompositionSubgroups k Ω) = ⊥ := by
  have hfour : ((-2 : ℤ) + 1 + 1 + 1 + 1) = 2 := by norm_num
  have hfive : ((-2 : ℤ) + 1 + 1 + 1 + 1 + 1) = 3 := by norm_num
  refine sha1Level_eq_bot_of_spanAt hK htriv htrivEK α hEp hfix eM hroot hop ?_ hzero
  refine hasIdeleClassNakayamaSpanAt_of_isZero_local (kummerHomRep M E htriv htrivEK)
    (fun _ => nsmul_additive_hom_eq_zero hEp _) eM (-2) (fun P w => ?_) (fun P v => ?_)
    (fun P => ?_)
  · rw [hfour]; exact h₁ P w
  · rw [hfour]; exact h₂ P v
  · rw [hfive]; exact hU P

end Vanish

end

end InverseGalois.CFT
