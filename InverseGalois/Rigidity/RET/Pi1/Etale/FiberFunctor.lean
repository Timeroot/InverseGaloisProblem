import InverseGalois.Rigidity.RET.Pi1.Etale.Category
import InverseGalois.Rigidity.RET.Pi1.Etale.Fiber
import InverseGalois.Rigidity.RET.Pi1.Etale.Closure
import InverseGalois.Rigidity.RET.Pi1.Etale.Limits
import InverseGalois.Rigidity.RET.Pi1.Etale.Subalgebra
import InverseGalois.Rigidity.RET.Pi1.Etale.Pushout
import InverseGalois.Rigidity.RET.Pi1.Etale.Equalizer
import InverseGalois.Rigidity.RET.Pi1.Etale.DirectSummand
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.CategoryTheory.Galois.Basic

/-!
# The fibre functor of the étale Galois category

For a field `K`, an algebraically closed extension `Ω`, and the fibre functor
`fibreFunctor K Ω : (FiniteEtaleAlgCat K)ᵒᵖ ⥤ FintypeCat`, `A ↦ (A.obj →ₐ[K] Ω)`, this file
establishes the exactness properties that make it a fibre functor for the Galois category
`(FiniteEtaleAlgCat K)ᵒᵖ`: it preserves the terminal object, pullbacks, and finite coproducts,
carries epimorphisms to epimorphisms, and reflects isomorphisms.

* Terminal: the fibre of the base object `K` is a singleton.
* Pullbacks: the fibre functor is representable (`fibreNatIso`), so it preserves all limits.
* Finite coproducts: the fibre of a finite product of algebras is the disjoint union of the
  fibres (`reassemble`).
* Epimorphisms: a mono of finite étale algebras is an injection, and every geometric point of the
  source extends to one of the target (base change to `Ω` plus a point of a nonzero finite étale
  `Ω`-algebra).
* Reflects isos: a bijection on fibres forces equal dimension, hence an algebra isomorphism.
-/

open CategoryTheory Limits Functor
open scoped TensorProduct

namespace Rigidity.RET.Etale.FiniteEtaleAlgCat

universe u
variable {K : Type u} [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω]

-- ===========================================================================
-- Field 1: preserves the terminal object
-- ===========================================================================

/-- The value of the fibre functor at the terminal object `op K` is terminal: its fibre `K →ₐ[K] Ω`
is a singleton. -/
noncomputable def fibreFunctorObjBaseIsTerminal :
    IsTerminal ((fibreFunctor K Ω).obj (Opposite.op (base K))) := by
  haveI hs : Subsingleton ((fibreFunctor K Ω).obj (Opposite.op (base K))) := by
    show Subsingleton ((base K).obj →ₐ[K] Ω); infer_instance
  have pt : ((fibreFunctor K Ω).obj (Opposite.op (base K)) : Type u) :=
    (Algebra.ofId K Ω : (base K).obj →ₐ[K] Ω)
  refine IsTerminal.ofUniqueHom (fun Y => FintypeCat.homMk (fun _ => pt)) ?_
  intro Y m
  apply FintypeCat.hom_ext
  intro x
  exact Subsingleton.elim _ _

noncomputable instance preservesTerminal :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (fibreFunctor K Ω) := by
  haveI : PreservesLimit (Functor.empty.{0} _) (fibreFunctor K Ω) :=
    preservesLimit_of_preserves_limit_cone (opBaseIsTerminal K)
      ((isLimitMapConeEmptyConeEquiv _ _).symm (fibreFunctorObjBaseIsTerminal Ω))
  exact preservesLimitsOfShape_pempty_of_preservesTerminal _

-- ===========================================================================
-- Field 2: preserves pullbacks (via representability)
-- ===========================================================================

/-- The fibre functor into `Type`, `A ↦ (A →ₐ[K] Ω)`, is naturally isomorphic to the representable
functor `Hom(-, Ω)` on `(CommAlgCat K)ᵒᵖ` restricted along the full-subcategory inclusion. -/
noncomputable def fibreNatIso :
    (isFiniteEtale K).ι.op ⋙ yoneda.obj (CommAlgCat.of K Ω)
      ≅ fibreFunctor K Ω ⋙ FintypeCat.incl :=
  NatIso.ofComponents
    (fun X => Equiv.toIso
      { toFun := fun h => h.hom
        invFun := fun f => CommAlgCat.ofHom f
        left_inv := by intro h; simp
        right_inv := by intro f; simp })
    (by
      intro X Y f
      funext h
      rfl)

noncomputable instance preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (fibreFunctor K Ω) := by
  haveI : PreservesColimitsOfShape WalkingCospanᵒᵖ (isFiniteEtale K).ι :=
    preservesColimitsOfShape_of_equiv walkingCospanOpEquiv.symm _
  haveI : PreservesLimitsOfShape WalkingCospan (isFiniteEtale K).ι.op :=
    preservesLimitsOfShape_op (J := WalkingCospan) (isFiniteEtale K).ι
  haveI : PreservesLimitsOfShape WalkingCospan
      ((isFiniteEtale K).ι.op ⋙ yoneda.obj (CommAlgCat.of K Ω)) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan (fibreFunctor K Ω ⋙ FintypeCat.incl) :=
    preservesLimitsOfShape_of_natIso (fibreNatIso Ω)
  exact preservesLimitsOfShape_of_reflects_of_preserves (fibreFunctor K Ω) FintypeCat.incl

-- ===========================================================================
-- Field 3: preserves finite coproducts (via `reassemble`)
-- ===========================================================================

section Coprod
variable {n : ℕ}

/-- Étale-ness of the concrete product `∀ j : Fin n, Z j` (universe transport via `ULift`). -/
private theorem etale_pi_fin (Z : Fin n → FiniteEtaleAlgCat K) :
    Algebra.Etale K (∀ j : Fin n, ((Z j).obj : Type u)) := by
  haveI : ∀ j : Fin n, Algebra.Etale K ((Z j).obj : Type u) := fun j => (Z j).property
  haveI : Algebra.Etale K (∀ j : ULift.{u} (Fin n), ((Z (Equiv.ulift j)).obj : Type u)) :=
    Algebra.Etale.pi _
  exact Algebra.Etale.of_equiv
    (AlgEquiv.piCongrLeft K (fun j : Fin n => ((Z j).obj : Type u)) Equiv.ulift)

/-- The concrete product object (the `Pi`-algebra) in `FiniteEtaleAlgCat K`. -/
def piPoint (Z : Fin n → FiniteEtaleAlgCat K) : FiniteEtaleAlgCat K :=
  ⟨CommAlgCat.of K (∀ j : Fin n, ((Z j).obj : Type u)), etale_pi_fin Z⟩

/-- The product fan with concrete `Pi`-algebra apex and evaluation projections. -/
def piFan (Z : Fin n → FiniteEtaleAlgCat K) : Fan Z :=
  Fan.mk (piPoint Z)
    (fun j => ObjectProperty.homMk
      (CommAlgCat.ofHom (Pi.evalAlgHom K (fun j : Fin n => ((Z j).obj : Type u)) j)))

/-- The `Pi`-algebra fan is a product. -/
def piFanIsLimit (Z : Fin n → FiniteEtaleAlgCat K) : IsLimit (piFan Z) := by
  refine mkFanLimit _
    (fun s => ObjectProperty.homMk
      (CommAlgCat.ofHom (Pi.algHom K (fun j : Fin n => ((Z j).obj : Type u))
        (fun j => homAlg K (s.proj j))))) ?_ ?_
  · intro s j
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext x
    rfl
  · intro s m hm
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    funext j
    have h := congrArg (fun t : s.pt ⟶ Z j => (homAlg K t) x) (hm j)
    exact h

/-- Bijectivity of `reassemble` re-derived from public API (injectivity + card count). -/
private theorem reassemble_bij (Z : Fin n → FiniteEtaleAlgCat K) :
    Function.Bijective
      (reassemble (K := K) (L := fun j : Fin n => ((Z j).obj : Type u)) (Ω := Ω)) := by
  haveI : ∀ j : Fin n, Algebra.Etale K ((Z j).obj : Type u) := fun j => (Z j).property
  haveI hfin : ∀ j : Fin n, Finite (((Z j).obj : Type u) →ₐ[K] Ω) :=
    fun j => finite_algHom_of_etale
  haveI : Finite ((∀ j : Fin n, ((Z j).obj : Type u)) →ₐ[K] Ω) := by
    haveI := etale_pi_fin Z
    exact finite_algHom_of_etale
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · rintro ⟨i, gi⟩ ⟨i', gi'⟩ h
    have hidx : i = i' := by
      by_contra hne
      have h1 := congrArg (fun φ => φ (Pi.single i 1)) h
      simp only [reassemble, AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same,
        map_one, Pi.single_eq_of_ne (Ne.symm hne), map_zero] at h1
      exact one_ne_zero h1
    subst hidx
    have hg : gi = gi' := by
      ext y
      have h2 := congrArg (fun φ => φ (Pi.single i y)) h
      simpa only [reassemble, AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same] using h2
    rw [hg]
  · rw [Nat.card_sigma, natCard_algHom_pi]

/-- The fibre functor preserves the coproduct of a single finite family. -/
noncomputable def preservesColimitDiscrete (g : Fin n → (FiniteEtaleAlgCat K)ᵒᵖ) :
    PreservesColimit (Discrete.functor g) (fibreFunctor K Ω) := by
  set Z : Fin n → FiniteEtaleAlgCat K := fun j => (g j).unop with hZ
  have hcolim : IsColimit ((piFan Z).op) := Fan.IsLimit.op (piFanIsLimit Z)
  refine preservesColimit_of_preserves_colimit_cocone hcolim ?_
  rw [show (piFan Z).op = Cofan.mk (Opposite.op (piPoint Z))
        (fun j => ((piFan Z).proj j).op) from rfl]
  refine (isColimitMapCoconeCofanMkEquiv (fibreFunctor K Ω) _
    (fun j => ((piFan Z).proj j).op)).symm ?_
  refine isColimitOfReflects FintypeCat.incl ?_
  refine (isColimitMapCoconeCofanMkEquiv FintypeCat.incl _
    (fun j => (fibreFunctor K Ω).map ((piFan Z).proj j).op)).symm ?_
  refine ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mpr ?_).some
  exact reassemble_bij Ω Z

end Coprod

/-- **The fibre functor preserves finite coproducts.**  A finite coproduct in the Galois category
`(FiniteEtaleAlgCat K)ᵒᵖ` is a finite product of `K`-algebras, and the fibre of a finite product is
the disjoint union of the factors' fibres (`reassemble`); hence `F(⨿ Aⱼ) ≅ ⨿ F(Aⱼ)`. -/
noncomputable instance fibreFunctorPreservesFiniteCoproducts :
    PreservesFiniteCoproducts (fibreFunctor K Ω) := by
  refine ⟨fun n => ?_⟩
  haveI : ∀ (g : Fin n → (FiniteEtaleAlgCat K)ᵒᵖ),
      PreservesColimit (Discrete.functor g) (fibreFunctor K Ω) :=
    fun g => preservesColimitDiscrete Ω g
  exact preservesColimitsOfShape_of_discrete _

-- ===========================================================================
-- Fields 4 & 6 need an algebraically closed fibre field.
-- ===========================================================================

section AlgClosed
variable [IsAlgClosed Ω]

/-- A nonzero finite étale algebra over an algebraically closed field has an algebra map back to
that field: it is a nonempty product of separable field factors, each of which (being algebraic over
the algebraically closed base) embeds. -/
theorem exists_algHom_of_etale_nontrivial {R : Type u} [CommRing R] [Algebra Ω R]
    [Algebra.Etale Ω R] [Nontrivial R] : Nonempty (R →ₐ[Ω] Ω) := by
  obtain ⟨I, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod Ω R).mp inferInstance
  haveI : Nonempty I := by
    by_contra hI
    rw [not_nonempty_iff] at hI
    haveI : Subsingleton (∀ i, L i) := ⟨fun a b => funext (fun i => (hI.false i).elim)⟩
    exact (not_subsingleton R) (e.injective.subsingleton)
  let i₀ : I := Classical.arbitrary I
  haveI : Module.Finite Ω (L i₀) := (hL i₀).1
  haveI : Algebra.IsAlgebraic Ω (L i₀) := Algebra.IsAlgebraic.of_finite Ω (L i₀)
  obtain ⟨φ⟩ := fibre_nonempty (K := Ω) (E := L i₀) (Ω := Ω)
  exact ⟨φ.comp ((Pi.evalAlgHom Ω L i₀).comp e.toAlgHom)⟩

/-- **The extension lemma.**  An injective `K`-algebra map `ψ : B →ₐ[K] A` between finite étale
`K`-algebras exhibits `A` as finite étale over `B`; a `K`-embedding `h : B →ₐ[K] Ω` into an
algebraically closed field therefore extends to a `K`-embedding of `A`.  Concretely `Ω ⊗[B] A` is a
nonzero finite étale `Ω`-algebra (nonzero since `A` is faithfully flat over `B`, by lying-over for the
integral injection `ψ`), and any of its `Ω`-points restricts to the required extension. -/
theorem exists_extension {B A : Type u} [CommRing B] [Algebra K B] [CommRing A] [Algebra K A]
    [Algebra.Etale K B] [Algebra.Etale K A]
    (ψ : B →ₐ[K] A) (hψ : Function.Injective ψ) (h : B →ₐ[K] Ω) :
    ∃ g : A →ₐ[K] Ω, g.comp ψ = h := by
  classical
  letI : Algebra B A := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq (fun x => (ψ.commutes x).symm)
  letI : Algebra B Ω := h.toRingHom.toAlgebra
  haveI : IsScalarTower K B Ω := IsScalarTower.of_algebraMap_eq (fun x => (h.commutes x).symm)
  haveI : Module.Finite K A := etale_moduleFinite A
  haveI : Module.Finite B A := Module.Finite.of_restrictScalars_finite K B A
  haveI : Algebra.Etale B A := etale_of_isScalarTower (K := K) B A
  haveI : Module.Flat B A := inferInstance
  haveI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hψ
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have hint : (algebraMap B A).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  have hcs : Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) :=
    hint.comap_surjective (FaithfulSMul.algebraMap_injective B A)
  haveI : Module.FaithfullyFlat B A := Module.FaithfullyFlat.of_comap_surjective hcs
  haveI : Nontrivial (Ω ⊗[B] A) := inferInstance
  haveI : Algebra.Etale Ω (Ω ⊗[B] A) := Algebra.Etale.baseChange B A Ω
  obtain ⟨p⟩ := exists_algHom_of_etale_nontrivial Ω (R := Ω ⊗[B] A)
  refine ⟨(p.restrictScalars K).comp
    ((Algebra.TensorProduct.includeRight : A →ₐ[B] Ω ⊗[B] A).restrictScalars K), ?_⟩
  apply AlgHom.ext
  intro b
  show p (1 ⊗ₜ[B] (ψ b)) = h b
  have h1 : (1 : Ω) ⊗ₜ[B] (ψ b) = (h b) ⊗ₜ[B] (1 : A) := by
    show (1 : Ω) ⊗ₜ[B] (algebraMap B A b) = (algebraMap B Ω b) ⊗ₜ[B] (1 : A)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  rw [h1]
  have h2 : (h b) ⊗ₜ[B] (1 : A) = algebraMap Ω (Ω ⊗[B] A) (h b) := by
    rw [Algebra.TensorProduct.algebraMap_apply]; simp
  rw [h2, AlgHom.commutes]; simp

/-- A monomorphism of finite étale `K`-algebras is injective on carriers.  This is extracted
concretely from its kernel pair: the subalgebra `{(a, a') | ψ a = ψ a'}` of `A.obj × A.obj` is
finite étale, and its two projections agree after post-composition with `φ`, so `Mono φ` forces them
equal — which is exactly injectivity of `ψ = homAlg K φ`. -/
theorem homAlg_injective_of_mono {A B : FiniteEtaleAlgCat K} (φ : A ⟶ B) [Mono φ] :
    Function.Injective (homAlg K φ) := by
  set ψ := homAlg K φ with hψdef
  haveI : Algebra.Etale K (A.obj × A.obj) := Algebra.Etale.prod
  let P : Subalgebra K (A.obj × A.obj) :=
    AlgHom.equalizer (ψ.comp (AlgHom.fst K A.obj A.obj)) (ψ.comp (AlgHom.snd K A.obj A.obj))
  haveI hPe : Algebra.Etale K P := etale_of_injective P.val Subtype.val_injective
  let Pcat : FiniteEtaleAlgCat K := ⟨CommAlgCat.of K P, hPe⟩
  let q₁ : Pcat.obj ⟶ A.obj := CommAlgCat.ofHom ((AlgHom.fst K A.obj A.obj).comp P.val)
  let q₂ : Pcat.obj ⟶ A.obj := CommAlgCat.ofHom ((AlgHom.snd K A.obj A.obj).comp P.val)
  let m₁ : Pcat ⟶ A := ObjectProperty.homMk q₁
  let m₂ : Pcat ⟶ A := ObjectProperty.homMk q₂
  have e1 : homAlg K m₁ = (AlgHom.fst K A.obj A.obj).comp P.val := by simp [m₁, q₁, homAlg]
  have e2 : homAlg K m₂ = (AlgHom.snd K A.obj A.obj).comp P.val := by simp [m₂, q₂, homAlg]
  have key : ψ.comp ((AlgHom.fst K A.obj A.obj).comp P.val)
           = ψ.comp ((AlgHom.snd K A.obj A.obj).comp P.val) := by
    apply AlgHom.ext
    intro p
    exact (AlgHom.mem_equalizer _ _ p.val).mp p.2
  have hcomp : m₁ ≫ φ = m₂ ≫ φ := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    show homAlg K (m₁ ≫ φ) = homAlg K (m₂ ≫ φ)
    rw [homAlg_comp, homAlg_comp, e1, e2]
    exact key
  have hm : m₁ = m₂ := (cancel_mono φ).mp hcomp
  intro a₁ a₂ ha
  have hp : (a₁, a₂) ∈ P := (AlgHom.mem_equalizer _ _ (a₁, a₂)).mpr (by simpa using ha)
  have hcong := congrArg (fun m => (homAlg K m) (⟨(a₁, a₂), hp⟩ : P)) hm
  simp only [e1, e2, AlgHom.comp_apply] at hcong
  simpa using hcong

/-- **The fibre functor preserves epimorphisms.**  An epimorphism in the Galois category
`(FiniteEtaleAlgCat K)ᵒᵖ` is a monomorphism `ψ` of finite étale `K`-algebras, hence an injective
algebra map; the induced map on fibres is precomposition by `ψ`, which is surjective by the extension
lemma (every geometric point of the source cover extends to one of the target).  A surjection of
finite sets is an epimorphism, so `F.map f` is epi. -/
noncomputable instance fibreFunctor_preservesEpi :
    Functor.PreservesEpimorphisms (fibreFunctor K Ω) where
  preserves {X Y} f _ := by
    haveI : Mono f.unop := inferInstance
    have hψ : Function.Injective (homAlg K f.unop) := homAlg_injective_of_mono f.unop
    apply ConcreteCategory.epi_of_surjective
    intro h
    obtain ⟨g, hg⟩ := exists_extension Ω (homAlg K f.unop) hψ h
    exact ⟨g, hg⟩

/-- **The fibre functor reflects isomorphisms.**  If the induced map on fibres is bijective, the
underlying algebra map is injective (fibres separate points, `separating_of_etale`) and, by equality
of fibre counts with `K`-dimension, surjective; hence an algebra isomorphism, so the original
morphism is an isomorphism. -/
noncomputable instance fibreFunctorReflectsIso :
    (fibreFunctor K Ω).ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    haveI := hf
    have hbij : Function.Bijective
        (fun g : X.unop.obj →ₐ[K] Ω => g.comp (homAlg K f.unop)) :=
      ConcreteCategory.bijective_of_isIso ((fibreFunctor K Ω).map f)
    have hψinj : Function.Injective (homAlg K f.unop) := by
      intro a b hab
      by_contra hne
      have ht : (a - b) ≠ 0 := sub_ne_zero.mpr hne
      obtain ⟨h, hh⟩ := separating_of_etale (K := K) (Ω := Ω) ht
      obtain ⟨g, hg⟩ := hbij.surjective h
      refine hh ?_
      rw [← hg, AlgHom.comp_apply, _root_.map_sub, hab, sub_self, map_zero]
    have hcard : Nat.card (X.unop.obj →ₐ[K] Ω) = Nat.card (Y.unop.obj →ₐ[K] Ω) :=
      Nat.card_congr (Equiv.ofBijective _ hbij)
    have hfr : Module.finrank K Y.unop.obj = Module.finrank K X.unop.obj := by
      rw [← natCard_algHom_eq_finrank_of_etale (K := K) (A := Y.unop.obj) (Ω := Ω),
          ← natCard_algHom_eq_finrank_of_etale (K := K) (A := X.unop.obj) (Ω := Ω), hcard]
    haveI : Module.Finite K X.unop.obj := etale_moduleFinite X.unop.obj
    haveI : Module.Finite K Y.unop.obj := etale_moduleFinite Y.unop.obj
    have hψsurj : Function.Surjective (homAlg K f.unop) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (homAlg K f.unop).toLinearMap) hfr).mp hψinj
    have hψbij : Function.Bijective (homAlg K f.unop) := ⟨hψinj, hψsurj⟩
    haveI : IsIso ((isFiniteEtale K).ι.map f.unop) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact hψbij
    haveI : IsIso f.unop := isIso_of_reflects_iso f.unop (isFiniteEtale K).ι
    exact (isIso_unop_iff f).mp inferInstance

end AlgClosed

end Rigidity.RET.Etale.FiniteEtaleAlgCat
