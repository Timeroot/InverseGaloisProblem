/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ShaTate
import InverseGalois.CFT.Profinite.DiscreteComap
import InverseGalois.CFT.TateCohomology.CyclicDualNatural
import InverseGalois.CFT.TateCohomology.NakayamaNatural
import InverseGalois.CFT.Units.HasseCoeff

/-!
# The everywhere locally trivial classes in complete cohomology, along a map of the coefficients

The everywhere locally trivial classes of the first cohomology of a Galois group sit inside the
complete cohomology of a finite level in degree one, by inflating them to the level and reading the
smooth cohomology of the finite level as ordinary cohomology.  A map of the coefficients moves both
the classes and the complete cohomology, and the reading commutes with it.

Each of the three steps commutes with a map of the coefficients for its own reason: inflation is
pullback along restriction to the level, and pullback composes a cocycle on the other side from the
map of the coefficients; the comparison between the smooth cohomology of a discrete group and
ordinary cohomology is computed on cocycles, where both operations are again compositions; and the
identification of the representation attached to an action with the representation one started with
is an isomorphism through which the map of representations factors either way.

The coefficients this is wanted for are the maps of a module into a fixed cyclic one, and a map of
the module moves those maps backwards, by composing before it.  So a map of the module carries the
everywhere locally trivial classes of the dual side backwards, and the reading in complete
cohomology carries them backwards too, compatibly.

## Main definitions

* `InverseGalois.CFT.repMulHom`: a map of representations, read on the multiplicative copies of the
  underlying groups.

## Main results

* `InverseGalois.CFT.smoothH1RepHom_coeffH1`: the comparison between smooth and complete cohomology
  in degree one is compatible with a map of the coefficients.
* `InverseGalois.CFT.shaTateLinear_shaCoeffH1`: **reading the everywhere locally trivial classes in
  the complete cohomology of a level is compatible with a map of the coefficients.**

## Tags

Galois cohomology, local-global principle, complete cohomology, duality, naturality
-/

namespace InverseGalois.CFT

open CategoryTheory groupCohomology Tate

noncomputable section

attribute [local instance] repMulDistribMulAction

/-! ### A map of representations, on the multiplicative copies -/

section RepMul

variable {G : Type} [Group G] {X Y : Rep ℤ G} (ψ : X ⟶ Y)

/-- **A map of representations, read on the multiplicative copies of the underlying groups.** -/
def repMulHom : Multiplicative ↥X.V →* Multiplicative ↥Y.V where
  toFun x := Multiplicative.ofAdd (ψ.hom.hom (Multiplicative.toAdd x))
  map_one' := congrArg Multiplicative.ofAdd (_root_.map_zero ψ.hom.hom)
  map_mul' _ _ := congrArg Multiplicative.ofAdd (_root_.map_add ψ.hom.hom _ _)

/-- The reading on the multiplicative copies is equivariant. -/
theorem repMulHom_smul (g : G) (m : Multiplicative ↥X.V) :
    repMulHom ψ (g • m) = g • repMulHom ψ m :=
  congrArg Multiplicative.ofAdd (Rep.hom_comm_apply ψ g (Multiplicative.toAdd m))

/-- The two readings of a map of representations agree: the map of the representations attached to
the actions, followed by the identification of those representations with the ones one started
with, is that identification followed by the map. -/
theorem discreteCoeffRepHom_comp_repIso :
    discreteCoeffRepHom (repMulHom ψ) (repMulHom_smul ψ) ≫ (repIso Y).hom
      = (repIso X).hom ≫ ψ :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

variable [Finite G]

/-- The comparison of the cohomology of an action with the cohomology of the representation is a
map induced by an isomorphism of representations. -/
theorem h1AddEquiv_apply (A : Rep ℤ G)
    (w : ↥(H1 (Rep.ofMulDistribMulAction G (Multiplicative ↥A.V)))) :
    h1AddEquiv A w = tateMap (repIso A).hom 1 w := rfl

/-- **The comparison of the cohomology of an action with the cohomology of the representation is
compatible with a map of the representation.** -/
theorem h1AddEquiv_tateMap (w : ↥(H1 (Rep.ofMulDistribMulAction G (Multiplicative ↥X.V)))) :
    h1AddEquiv Y (tateMap (discreteCoeffRepHom (repMulHom ψ) (repMulHom_smul ψ)) 1 w)
      = tateMap ψ 1 (h1AddEquiv X w) := by
  rw [h1AddEquiv_apply, h1AddEquiv_apply, tateMap_comp_apply, tateMap_comp_apply,
    discreteCoeffRepHom_comp_repIso]

variable [TopologicalSpace G] [DiscreteTopology G]

/-- **The comparison between the smooth cohomology of a discrete group and the complete cohomology
of a representation is compatible with a map of the representation.** -/
theorem smoothH1RepHom_coeffH1 (z : Additive (SmoothH1 G (Multiplicative ↥X.V))) :
    smoothH1RepHom Y (Additive.ofMul
        (coeffH1 (repMulHom ψ) (repMulHom_smul ψ) (Additive.toMul z)))
      = tateMap ψ 1 (smoothH1RepHom X z) := by
  have key : discreteSmoothH1Equiv G (Multiplicative ↥Y.V)
        (coeffH1 (repMulHom ψ) (repMulHom_smul ψ) (Additive.toMul z))
      = Multiplicative.ofAdd (tateMap (discreteCoeffRepHom (repMulHom ψ) (repMulHom_smul ψ)) 1
          (Multiplicative.toAdd
            (discreteSmoothH1Equiv G (Multiplicative ↥X.V) (Additive.toMul z)))) :=
    discreteSmoothH1Hom_coeffH1 _ _ _
  show h1AddEquiv Y (Multiplicative.toAdd (discreteSmoothH1Equiv G (Multiplicative ↥Y.V)
    (coeffH1 (repMulHom ψ) (repMulHom_smul ψ) (Additive.toMul z)))) = _
  rw [key]
  exact h1AddEquiv_tateMap ψ _

end RepMul

/-! ### The everywhere locally trivial classes, along a map of the coefficients -/

section Sha

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  (F : IntermediateField k Ω) [FiniteDimensional k F] [IsGalois k F] [NumberField ↥F]
  (A : Rep ℤ (↥F ≃ₐ[k] ↥F)) [IsAddCyclic ↥A.V] [Finite ↥A.V]
  {B B' : Rep ℤ (↥F ≃ₐ[k] ↥F)} [Finite ↥B.V] [Finite ↥B'.V]
  [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥(linHomObj B A).V)]
  [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥(linHomObj B' A).V)]
  (hπ : ∀ (g : Gal(Ω/k)) (m : Multiplicative ↥(linHomObj B A).V),
    g • m = AlgEquiv.restrictNormalHom F g • m)
  (hπ' : ∀ (g : Gal(Ω/k)) (m : Multiplicative ↥(linHomObj B' A).V),
    g • m = AlgEquiv.restrictNormalHom F g • m)
  (f : B ⟶ B')

omit [IsGalois k Ω] [FiniteDimensional k ↥F] [NumberField ↥F] [IsAddCyclic ↥A.V] [Finite ↥A.V]
  [Finite ↥B.V] [Finite ↥B'.V] in
include hπ hπ' in
/-- Reading a map out of the target on the source is equivariant for the whole Galois group, since
the whole Galois group acts through the level. -/
theorem repMulHom_smul_gal (g : Gal(Ω/k)) (m : Multiplicative ↥(linHomObj B' A).V) :
    repMulHom (linHomPreHom A f) (g • m) = g • repMulHom (linHomPreHom A f) m := by
  rw [hπ' g m, repMulHom_smul, hπ]

omit [IsAddCyclic ↥A.V] [Finite ↥A.V] [Finite ↥B.V] [Finite ↥B'.V] in
include hπ hπ' in
/-- **Reading the everywhere locally trivial classes in the first cohomology of a level is
compatible with a map of the coefficients.** -/
theorem shaTateHom_shaCoeffH1
    (z : ↥(sha1 (Multiplicative ↥(linHomObj B' A).V) (decompositionSubgroups k Ω))) :
    shaTateHom F A B hπ (Additive.ofMul (shaCoeffH1 (repMulHom (linHomPreHom A f))
        (repMulHom_smul_gal F A hπ hπ' f) (decompositionSubgroups k Ω) z))
      = tateMap (linHomPreHom A f) 1 (shaTateHom F A B' hπ' (Additive.ofMul z)) := by
  haveI : IsSmoothAction Gal(Ω/k) (Multiplicative ↥(linHomObj B A).V) :=
    isSmoothAction_of_isOpenNormal_ker _ hπ (isOpenNormal_ker_restrictNormalHom F)
  haveI : IsSmoothAction Gal(Ω/k) (Multiplicative ↥(linHomObj B' A).V) :=
    isSmoothAction_of_isOpenNormal_ker _ hπ' (isOpenNormal_ker_restrictNormalHom F)
  show smoothH1RepHom (linHomObj B A) (Additive.ofMul (shaInflH1 _ F hπ
    (shaCoeffH1 (repMulHom (linHomPreHom A f)) (repMulHom_smul_gal F A hπ hπ' f)
      (decompositionSubgroups k Ω) z))) = _
  rw [shaInflH1_shaCoeffH1 F hπ' hπ (repMulHom (linHomPreHom A f))
    (repMulHom_smul_gal F A hπ hπ' f) (repMulHom_smul (linHomPreHom A f))]
  exact smoothH1RepHom_coeffH1 (linHomPreHom A f)
    (Additive.ofMul (shaInflH1 (Multiplicative ↥(linHomObj B' A).V) F hπ' z))

omit [IsAddCyclic ↥A.V] [Finite ↥A.V] [Finite ↥B.V] [Finite ↥B'.V] in
include hπ hπ' in
/-- **Reading the everywhere locally trivial classes in the complete cohomology of a level is
compatible with a map of the coefficients.**  A class carried backwards along the map of the
coefficients and then read at the level is the class read at the level and then carried backwards
in complete cohomology. -/
theorem shaTateLinear_shaCoeffH1
    (z : ↥(sha1 (Multiplicative ↥(linHomObj B' A).V) (decompositionSubgroups k Ω))) :
    shaTateLinear F A B hπ (Additive.ofMul (shaCoeffH1 (repMulHom (linHomPreHom A f))
        (repMulHom_smul_gal F A hπ hπ' f) (decompositionSubgroups k Ω) z))
      = tateMap (linHomPreHom A f) 1 (shaTateLinear F A B' hπ' (Additive.ofMul z)) :=
  shaTateHom_shaCoeffH1 F A hπ hπ' f z

end Sha

end

end InverseGalois.CFT
