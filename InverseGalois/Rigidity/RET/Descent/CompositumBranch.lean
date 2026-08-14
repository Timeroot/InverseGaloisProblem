/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.SemilinearSub
import InverseGalois.Rigidity.RET.Descent.ModelDescent

/-!
# The branch locus of the geometric compositum

The compositum `Ωbar = Ω · ℚ̄(T)` produced by the arithmetic descent (`Descent.ModelDescent`) is a
bigger cover of the line than the cover `Lsub` it was built from, and the branch cycles of the
descent have to be read off `Ωbar`, not off `Lsub`.  For that one first has to know that the two
covers are branched over the *same* points.

They are, and the reason is arithmetic rather than geometric.  `Ωbar` is normal over the
**arithmetic** base `ℚ(T)`, and it is generated over `ℚ̄(T)` by the `ℚ(T)`-conjugates of a primitive
element of `Lsub` (`GeomCompositum.adjoin_rootSet_eq_top`).  Each `ℚ(T)`-automorphism of `Ωbar`
carries the geometric base `ℚ̄(T)` onto itself — it moves the constants, but it fixes the parameter
`T`, because `T` already lies in `ℚ(T)` — so it is a *semilinear* automorphism of the cover over a
coordinate change of the constants (`RET/Semilinear.lean`).  A coordinate change of the constants
leaves every rational point of the line, and the point at infinity, where it is; so a conjugate of
`Lsub` is branched exactly where `Lsub` is, and the compositum lemma
(`LineCover.IsUnramifiedOutside.of_conjugates`) bounds the branch locus of `Ωbar` by that of `Lsub`.

## Main definitions

* `Rigidity.RET.Descent.GeomCompositum.cover` — the compositum as a cover of the line over `ℚ̄`.
* `Rigidity.RET.Descent.GeomCompositum.baseAut` — the coordinate change of `ℚ̄(T)` induced by a
  `ℚ(T)`-automorphism of the compositum.
* `Rigidity.RET.Descent.GeomCompositum.semiIso` — that automorphism, as a semilinear automorphism
  of the cover.

## Main results

* `Rigidity.RET.Descent.GeomCompositum.iSup_mapField_eq_top` — the conjugates of the sub-cover
  generate the compositum.
* `Rigidity.RET.Descent.GeomCompositum.isUnramifiedOutside`,
  `Rigidity.RET.Descent.GeomCompositum.isUnramifiedAtInfinity` — the compositum is branched where
  the sub-cover is.
* `Rigidity.RET.Descent.geomCompositum_exists_of_cover_unramified` — the descent, with the branch
  locus of the original cover carried over to the compositum.
-/

open Polynomial

noncomputable section


namespace Rigidity.RET.Descent

open Rigidity.RET GeomAKLB LineCover

/-- **A ring endomorphism of an extension of `ℚ̄` sends constants to algebraic elements.**  Every
ring homomorphism fixes the rationals, so the image of a constant satisfies the same `ℚ`-polynomial
the constant does. -/
theorem isAlgebraic_ringHom_const {L : Type*} [Field L] [Algebra k L] (ρ : L →+* L) (a : k) :
    IsAlgebraic k (ρ (algebraMap k L a)) := by
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (A := k) a
  refine ⟨p.map (algebraMap ℚ k), ?_, ?_⟩
  · simpa [Polynomial.map_eq_zero_iff (algebraMap ℚ k).injective] using hp0
  · set f : ℚ →+* L := (algebraMap k L).comp (algebraMap ℚ k) with hf
    have hρf : ρ.comp f = f := by
      refine RingHom.ext fun q => ?_
      show ρ (f q) = f q
      rw [show f q = (q : L) from eq_ratCast f q, map_ratCast]
    have hval : Polynomial.eval₂ f (algebraMap k L a) p = 0 := by
      rw [hf, ← Polynomial.hom_eval₂, show Polynomial.eval₂ (algebraMap ℚ k) a p = 0 from hp,
        map_zero]
    have hcomp : ρ (Polynomial.eval₂ f (algebraMap k L a) p)
        = Polynomial.eval₂ (ρ.comp f) (ρ (algebraMap k L a)) p :=
      Polynomial.hom_eval₂ p f ρ (algebraMap k L a)
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hf, ← hρf, ← hcomp, hval, map_zero]

namespace GeomCompositum

variable {G : Type} [Group G] [Finite G] (c : GeomCompositum G)

/-- **The compositum, as a cover of the line over `ℚ̄`.** -/
@[reducible] noncomputable def cover : LineCover := LineCover.of c.Ωbar

@[simp] theorem cover_M : c.cover.M = c.Ωbar := rfl

/-- The constants, inside the compositum. -/
local instance algConst : Algebra k c.Ωbar :=
  ((algebraMap (RatFunc k) c.Ωbar).comp (algebraMap k (RatFunc k))).toAlgebra

theorem algebraMap_const (a : k) :
    algebraMap k c.Ωbar a = algebraMap (RatFunc k) c.Ωbar (algebraMap k (RatFunc k) a) := rfl

/-- **A `ℚ(T)`-linear ring endomorphism of the compositum carries the geometric base into itself.**
It moves the constants among themselves, because they are the elements algebraic over `ℚ`, and it
fixes the parameter, because the parameter lies in the arithmetic base `ℚ(T)`. -/
theorem mem_base_of_commutes (ρ : c.Ωbar →+* c.Ωbar)
    (hρ : ∀ q : RatFunc ℚ,
      ρ (algebraMap (RatFunc ℚ) c.Ωbar q) = algebraMap (RatFunc ℚ) c.Ωbar q)
    (f : RatFunc k) :
    ∃ g : RatFunc k, ρ (algebraMap (RatFunc k) c.Ωbar f)
      = algebraMap (RatFunc k) c.Ωbar g := by
  have hmem : ρ (algebraMap (RatFunc k) c.Ωbar f)
      ∈ (algebraMap (RatFunc k) c.Ωbar).fieldRange := by
    refine Rigidity.RET.ratFunc_mem_subfield
      (ρ.comp (algebraMap (RatFunc k) c.Ωbar)) _ (fun a => ?_) ?_ f
    · obtain ⟨b, hb⟩ := exists_const_of_isAlgebraic (isAlgebraic_ringHom_const (L := c.Ωbar) ρ a)
      exact ⟨algebraMap k (RatFunc k) b, by rw [← algebraMap_const, hb]; rfl⟩
    · refine ⟨RatFunc.X, ?_⟩
      show algebraMap (RatFunc k) c.Ωbar RatFunc.X
        = ρ (algebraMap (RatFunc k) c.Ωbar RatFunc.X)
      rw [← c.algebraMap_X, hρ, c.algebraMap_X]
  exact (RingHom.mem_fieldRange).1 hmem |>.imp fun _ hg => hg.symm

/-- **The coordinate change of the geometric base induced by a `ℚ(T)`-automorphism of the
compositum.** -/
def baseAut (σ : c.Ωbar ≃ₐ[RatFunc ℚ] c.Ωbar) : RatFunc k ≃+* RatFunc k :=
  SemiIso.baseEquiv (L := c.cover) (L' := c.cover) σ.toRingEquiv
    (c.mem_base_of_commutes (σ : c.Ωbar →+* c.Ωbar) σ.commutes)
    (c.mem_base_of_commutes (σ.symm : c.Ωbar →+* c.Ωbar) σ.symm.commutes)

/-- The coordinate change fixes the parameter: the parameter lies in the arithmetic base. -/
theorem baseAut_X (σ : c.Ωbar ≃ₐ[RatFunc ℚ] c.Ωbar) :
    c.baseAut σ RatFunc.X = RatFunc.X := by
  refine (algebraMap (RatFunc k) c.Ωbar).injective ?_
  show algebraMap (RatFunc k) c.cover.M
      (SemiIso.baseHom (L := c.cover) (L' := c.cover) σ.toRingEquiv
        (c.mem_base_of_commutes (σ : c.Ωbar →+* c.Ωbar) σ.commutes) RatFunc.X) = _
  rw [← SemiIso.baseHom_spec]
  show σ (algebraMap (RatFunc k) c.Ωbar RatFunc.X) = _
  rw [← c.algebraMap_X]
  exact σ.commutes RatFunc.X

/-- **A `ℚ(T)`-automorphism of the compositum, as a semilinear automorphism of the cover** over a
coordinate change of the constants. -/
def semiIso (σ : c.Ωbar ≃ₐ[RatFunc ℚ] c.Ωbar) :
    SemiIso c.cover c.cover (constSubst (constEquiv (c.baseAut σ))) where
  toRingEquiv := σ.toRingEquiv
  map_smul f x := by
    rw [← eq_constSubst _ (c.baseAut_X σ)]
    exact (SemiIso.ofBasePreserving (L := c.cover) (L' := c.cover) σ.toRingEquiv
      (c.mem_base_of_commutes (σ : c.Ωbar →+* c.Ωbar) σ.commutes)
      (c.mem_base_of_commutes (σ.symm : c.Ωbar →+* c.Ωbar) σ.symm.commutes)).map_smul f x

@[simp] theorem semiIso_toRingEquiv (σ : c.Ωbar ≃ₐ[RatFunc ℚ] c.Ωbar) (x : c.Ωbar) :
    (c.semiIso σ).toRingEquiv x = σ x := rfl

/-- The conjugate of the sub-cover under a `ℚ(T)`-automorphism is generated by the image of the
primitive element. -/
theorem mapField_Lsub (σ : c.Ωbar ≃ₐ[RatFunc ℚ] c.Ωbar) :
    (c.semiIso σ).mapField c.Lsub
      = IntermediateField.adjoin (RatFunc k) {σ c.prim} := by
  rw [c.Lsub_eq_adjoin, SemiIso.mapField_adjoin, Set.image_singleton]
  rfl

/-- **The `ℚ(T)`-conjugates of the sub-cover generate the compositum.**  The compositum is
generated over `ℚ̄(T)` by the roots of the `ℚ(T)`-minimal polynomial of the primitive element, and
every such root is a `ℚ(T)`-conjugate of it, because the compositum is normal over `ℚ(T)`. -/
theorem iSup_mapField_eq_top :
    ⨆ σ : c.Ωbar ≃ₐ[RatFunc ℚ] c.Ωbar, (c.semiIso σ).mapField c.Lsub = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← c.adjoin_rootSet_eq_top, IntermediateField.adjoin_le_iff]
  intro x hx
  have hev : (Polynomial.aeval x) (minpoly (RatFunc ℚ) c.prim) = 0 :=
    (Polynomial.mem_rootSet'.1 hx).2
  have halg : IsAlgebraic (RatFunc ℚ) c.prim :=
    Algebra.IsAlgebraic.isAlgebraic (R := RatFunc ℚ) (A := c.Ωbar) c.prim
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (K := RatFunc ℚ) (L := c.Ωbar) halg hev
  refine SetLike.mem_coe.2 (le_iSup (fun σ => (c.semiIso σ).mapField c.Lsub) σ ?_)
  show x ∈ (c.semiIso σ).mapField c.Lsub
  rw [c.mapField_Lsub σ, hσ]
  exact IntermediateField.subset_adjoin _ _ rfl

/-- **The compositum is unramified wherever the sub-cover is**, over a set of rational points. -/
theorem isUnramifiedOutside {S : Set k} (hS : S ⊆ Set.range (algebraMap ℚ k))
    (hE : (c.cover.sub c.Lsub).IsUnramifiedOutside S) : c.cover.IsUnramifiedOutside S :=
  IsUnramifiedOutside.of_conjugates hS c.semiIso c.Lsub c.iSup_mapField_eq_top hE

/-- **The compositum is unramified at infinity if the sub-cover is.** -/
theorem isUnramifiedAtInfinity (hE : (c.cover.sub c.Lsub).IsUnramifiedAtInfinity) :
    c.cover.IsUnramifiedAtInfinity :=
  IsUnramifiedAtInfinity.of_conjugates c.semiIso c.Lsub c.iSup_mapField_eq_top hE

end GeomCompositum

/-- **The arithmetic descent, with the branch locus carried along.**  From a geometric Galois cover
`L/ℚ̄(T)` with deck group `G`, unramified outside a set of rational points and at infinity, the
compositum square exists with a compositum branched over the same points. -/
theorem geomCompositum_exists_of_cover_unramified {G : Type} [Group G] [Finite G] (L : Type)
    [Field L] [Algebra (RatFunc k) L] [FiniteDimensional (RatFunc k) L] [IsGalois (RatFunc k) L]
    (φG : (L ≃ₐ[RatFunc k] L) ≃* G) {S : Set k} (hS : S ⊆ Set.range (algebraMap ℚ k))
    (hL : (LineCover.of L).IsUnramifiedOutside S)
    (hLinf : (LineCover.of L).IsUnramifiedAtInfinity) :
    ∃ (c : GeomCompositum G) (e : L ≃ₐ[RatFunc k] c.Lsub),
      (∀ σ : L ≃ₐ[RatFunc k] L, c.galLsub (AlgEquiv.autCongr e σ) = φG σ) ∧
        c.cover.IsUnramifiedOutside S ∧ c.cover.IsUnramifiedAtInfinity := by
  obtain ⟨c, e, hgal⟩ := geomCompositum_exists_of_cover L φG
  have hsub : (c.cover.sub c.Lsub).IsUnramifiedOutside S :=
    IsUnramifiedOutside.transport (L := LineCover.of L) (L' := c.cover.sub c.Lsub) e hL
  have hsubinf : (c.cover.sub c.Lsub).IsUnramifiedAtInfinity :=
    IsUnramifiedAtInfinity.transport (L := LineCover.of L) (L' := c.cover.sub c.Lsub) e hLinf
  exact ⟨c, e, hgal, c.isUnramifiedOutside hS hsub, c.isUnramifiedAtInfinity hsubinf⟩

end Rigidity.RET.Descent
