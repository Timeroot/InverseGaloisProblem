import InverseGalois.Rigidity.RET.Pi1.Etale.Category
import InverseGalois.Rigidity.RET.Pi1.Etale.Closure
import InverseGalois.Rigidity.RET.Pi1.Etale.Limits
import InverseGalois.Rigidity.RET.Pi1.Etale.Subalgebra
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

/-!
# Equalizers, finite limits, and quotients by finite groups

The equalizer of two `K`-algebra maps `f, g : A ⟶ B` is the subalgebra on which they agree; when
`A` is finite étale so is this subalgebra (`etale_of_injective`, via the injective inclusion).  This
closes `FiniteEtaleAlgCat K` under equalizers, hence under all finite limits, and dually makes the
Galois category `(FiniteEtaleAlgCat K)ᵒᵖ` have finite colimits and quotients by finite groups.
-/

open CategoryTheory Limits

namespace Rigidity.RET.Etale

universe u

variable {K : Type u} [Field K]

section Equalizer
variable (A B : CommAlgCat.{u} K) (f g : A ⟶ B)

/-- Equalizer fork in `CommAlgCat K` for a parallel pair `f, g : A ⟶ B`, with point the subalgebra
`{ a | f a = g a }` of `A` and leg its inclusion. -/
noncomputable def equalizerFork : Fork f g :=
  Fork.ofι (CommAlgCat.ofHom (AlgHom.equalizer f.hom g.hom).val)
    (by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      exact (AlgHom.mem_equalizer f.hom g.hom (x : A)).mp x.2)

/-- The `equalizerFork` is a limit: the subalgebra where `f` and `g` agree is their equalizer. -/
noncomputable def equalizerForkIsLimit : IsLimit (equalizerFork A B f g) :=
  Fork.IsLimit.mk _
    (fun s => CommAlgCat.ofHom
      (AlgHom.codRestrict s.ι.hom (AlgHom.equalizer f.hom g.hom) (fun y => by
        rw [AlgHom.mem_equalizer]
        have h := congrArg CommAlgCat.Hom.hom s.condition
        rw [CommAlgCat.hom_comp, CommAlgCat.hom_comp] at h
        exact DFunLike.congr_fun h y)))
    (fun s => by
      apply CommAlgCat.hom_ext
      exact AlgHom.val_comp_codRestrict s.ι.hom _ _)
    (fun s m hm => by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro y
      apply Subtype.ext
      have h := congrArg CommAlgCat.Hom.hom hm
      rw [CommAlgCat.hom_comp] at h
      have hy := DFunLike.congr_fun h y
      simp only [equalizerFork, Fork.ofι_pt, Fork.ι_ofι, CommAlgCat.hom_ofHom,
        AlgHom.coe_codRestrict, AlgHom.coe_comp, Function.comp_apply] at hy ⊢
      exact hy)

end Equalizer

/-- **Finite étale algebras are closed under equalizers.**  The limit of a parallel pair
`f, g : A ⟶ B` of finite étale `K`-algebras is the subalgebra of `A` on which `f` and `g` agree
(`equalizerForkIsLimit`); it is finite étale because it injects into the finite étale algebra `A`
(`etale_of_injective`). -/
instance : (isFiniteEtale K).IsClosedUnderLimitsOfShape WalkingParallelPair := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  haveI : Algebra.Etale K (F.obj WalkingParallelPair.zero : Type u) := hF WalkingParallelPair.zero
  -- the equalizer subalgebra injects into the (finite étale) source, hence is finite étale
  haveI : Algebra.Etale K
      (AlgHom.equalizer (F.map WalkingParallelPairHom.left).hom
        (F.map WalkingParallelPairHom.right).hom) :=
    etale_of_injective
      (AlgHom.equalizer (F.map WalkingParallelPairHom.left).hom
        (F.map WalkingParallelPairHom.right).hom).val Subtype.val_injective
  -- identify `limit F` with the equalizer fork point via `diagramIsoParallelPair`
  have hlc : IsLimit (equalizerFork (F.obj WalkingParallelPair.zero)
      (F.obj WalkingParallelPair.one) (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)) :=
    equalizerForkIsLimit _ _ _ _
  have hcF : IsLimit ((Cones.postcompose (diagramIsoParallelPair F).inv).obj
      (equalizerFork (F.obj WalkingParallelPair.zero) (F.obj WalkingParallelPair.one)
        (F.map WalkingParallelPairHom.left) (F.map WalkingParallelPairHom.right))) :=
    (IsLimit.postcomposeInvEquiv (diagramIsoParallelPair F) _).symm hlc
  have iso : limit F ≅ (equalizerFork (F.obj WalkingParallelPair.zero)
      (F.obj WalkingParallelPair.one) (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)).pt :=
    (limit.isLimit F).conePointUniqueUpToIso hcF
  exact ObjectProperty.prop_of_iso (isFiniteEtale K) iso.symm ‹_›

/-- **`FiniteEtaleAlgCat K` has equalizers.** -/
instance : HasEqualizers (FiniteEtaleAlgCat K) :=
  hasLimitsOfShape_of_closedUnderLimits _ _

/-- **`FiniteEtaleAlgCat K` has all finite limits**, assembled from finite products and equalizers. -/
instance : HasFiniteLimits (FiniteEtaleAlgCat K) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- **The Galois category `(FiniteEtaleAlgCat K)ᵒᵖ` has finite colimits**, dual to the finite limits
of `FiniteEtaleAlgCat K`. -/
instance : HasFiniteColimits (FiniteEtaleAlgCat K)ᵒᵖ :=
  hasFiniteColimits_opposite

/-- **The Galois category has quotients by finite groups** (`PreGaloisCategory` field): colimits
over `SingleObj G` for a finite group `G`.  For a finite group already living in the object
universe this is a finite colimit; the general case transports along a group isomorphism to such a
model (mirroring the same reduction in `CategoryTheory.Galois`). -/
instance {G : Type*} [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlgCat.{u} K)ᵒᵖ := by
  obtain ⟨G', _, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

end Rigidity.RET.Etale
