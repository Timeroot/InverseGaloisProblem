/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LinHomTensor
import InverseGalois.Solvable.Shafarevich.HomologyIntegral
import InverseGalois.Solvable.Shafarevich.LayerCohomology
import InverseGalois.CFT.PoitouTate.ShaCover

/-!
# A single class of complete cohomology governs every shrinking of a level

The ladder that builds a solvable extension asks, at each rung, that an obstruction class of the
second cohomology with coefficients in a layer of the level be killed by some shrinking of the
level.  Global duality supplies exactly such a governing device, but in a different language: it
reads an everywhere locally trivial class of the second cohomology as a character of the everywhere
locally trivial classes of the first cohomology of the Cartier dual, and cuts that character out
with one class of complete cohomology of the level in degree minus two.  A shrinking under which
that one class dies kills the obstruction.

The two languages are joined here.  The coefficients global duality carries are the maps of a fixed
module into the layer; the coefficients the ladder carries are the layer tensored with the dual of
that module.  Those are the same coefficients, and the identification is compatible with every
homomorphism of levels commuting with the operators, so the class produced once and for all by
duality is carried across to the class the ladder consumes: one class for every shrinking at once.

Reading the class the other way round costs nothing, because a homomorphism of levels commuting
with the operators is a map of representations of the operator group, and the Galois group acts on
every layer through the level.  What global duality itself contributes - the character at the
level, and for each shrinking an injective character downstairs compatible with it - is named as a
hypothesis.

## Main definitions

* `InverseGalois.Shafarevich.operatorLayerRep`: a homomorphism of levels commuting with the
  operators, read as a map of representations of layers.
* `InverseGalois.Shafarevich.layerLinHomIso`: **a layer tensored with the dual of a module is the
  maps of that module into the layer.**
* `InverseGalois.Shafarevich.HasTateShaCover`: one class of complete cohomology of the level in
  degree minus two governs every everywhere locally trivial class of the layer.
* `InverseGalois.Shafarevich.HasShrinkShaDualInjection`: global duality reads the everywhere
  locally trivial classes of a layer as characters, compatibly with every shrinking.

## Main results

* `InverseGalois.Shafarevich.layerLinHomIso_naturality`: **the identification of the coefficients
  is compatible with a homomorphism commuting with the operators.**
* `InverseGalois.Shafarevich.hasIntegralShaTateCover_of_hasTateShaCover`: **the governing class of
  complete cohomology is the governing class of first homology the ladder consumes.**
* `InverseGalois.Shafarevich.hasTateShaCover_of_hasShrinkShaDualInjection`: **global duality
  produces the governing class of complete cohomology.**
* `InverseGalois.Shafarevich.hasShrinkableSha_of_hasShrinkShaDualInjection`: **global duality makes
  every everywhere locally trivial class of a layer shrinkable.**

## Tags

Shafarevich's theorem, embedding problem, global duality, Poitou-Tate, complete cohomology, layer
-/

namespace InverseGalois.Shafarevich

open CategoryTheory InverseGalois.CFT InverseGalois.CFT.Tate

attribute [local instance] repMulDistribMulAction

/-! ### A finite cyclic module stays finite cyclic over the integers -/

/-- Reading a representation over the integers does not change its underlying group. -/
instance instFiniteIntRep {ℓ : ℕ} {G : Type} [Group G] (A : Rep (ZMod ℓ) G) [Finite ↥A.V] :
    Finite ↥(intRep A).V := ‹Finite ↥A.V›

/-- Reading a representation over the integers does not change its underlying group. -/
instance instIsAddCyclicIntRep {ℓ : ℕ} {G : Type} [Group G] (A : Rep (ZMod ℓ) G)
    [IsAddCyclic ↥A.V] : IsAddCyclic ↥(intRep A).V := ‹IsAddCyclic ↥A.V›

noncomputable section

/-! ### A shrinking of the level, as a map of representations -/

section OperatorLayer

variable {U : Type} [Group U] {S : Type} [Group S] {m n : ℕ}
  {α : Generic U m S →* Generic U n S}

/-- **A homomorphism of levels commuting with the operators, read as a map of representations of
layers.**  The induced map of layers is linear, and commuting with the operators is exactly the
equivariance the map of representations asks for. -/
def operatorLayerRep (hα : IsOperatorHom α) (ℓ j : ℕ) :
    genericLayer U m S ℓ j ⟶ genericLayer U n S ℓ j where
  hom := ModuleCat.ofHom (layerLinear ℓ α j)
  comm u := ModuleCat.hom_ext (LinearMap.ext fun v => layerMap_isOperatorHom hα u v)

@[simp]
theorem operatorLayerRep_hom (hα : IsOperatorHom α) (ℓ j : ℕ) :
    (operatorLayerRep hα ℓ j).hom = ModuleCat.ofHom (layerLinear ℓ α j) := rfl

end OperatorLayer

/-! ### The two readings of the coefficients -/

section Bridge

variable {U : Type} [Group U] {S : Type} [Group S] {ℓ : ℕ} [Fact ℓ.Prime]
  (M : Rep (ZMod ℓ) U) [FiniteDimensional (ZMod ℓ) ↥M.V] (n j : ℕ)

/-- **A layer tensored with the dual of a module is the maps of that module into the layer**, over
the integers. -/
def layerLinHomIso :
    intRep (genericLayerTensor U n S ℓ j (dualRep M)) ≅
      linHomObj (intRep M) (intRep (genericLayer U n S ℓ j)) :=
  intRepIso (linHomTensorIso M (genericLayer U n S ℓ j)) ≪≫
    (intLinHomIso M (genericLayer U n S ℓ j)).symm

theorem layerLinHomIso_hom :
    (layerLinHomIso M (S := S) n j).hom =
      intRepMap (linHomTensorIso M (genericLayer U n S ℓ j)).hom ≫
        (intLinHomIso M (genericLayer U n S ℓ j)).inv := rfl

variable {n}

/-- **The identification of the coefficients is compatible with a homomorphism commuting with the
operators.**  Following the induced map of layers after a linear map out of the module is, on the
tensor product, that map applied to the layer alone. -/
theorem layerLinHomIso_naturality {m : ℕ} {α : Generic U m S →* Generic U n S}
    (hα : IsOperatorHom α) :
    (layerLinHomIso M (S := S) m j).hom ≫
        linHomPostHom (intRep M) (intRepMap (operatorLayerRep hα ℓ j))
      = intRepMap (operatorTensorRep hα ℓ j (dualRep M)) ≫
        (layerLinHomIso M (S := S) n j).hom := by
  have hb : intRepMap (linHomTensorIso M (genericLayer U m S ℓ j)).hom ≫
      intRepMap (linHomPostHom M (operatorLayerRep hα ℓ j))
        = intRepMap (operatorTensorRep hα ℓ j (dualRep M)) ≫
          intRepMap (linHomTensorIso M (genericLayer U n S ℓ j)).hom := by
    rw [← intRepMap_comp, ← intRepMap_comp,
      linHomTensorIso_naturality M (operatorLayerRep hα ℓ j)
        (operatorTensorRep hα ℓ j (dualRep M)) fun _ => rfl]
  have hinv : (intLinHomIso M (genericLayer U m S ℓ j)).inv ≫
      linHomPostHom (intRep M) (intRepMap (operatorLayerRep hα ℓ j))
        = intRepMap (linHomPostHom M (operatorLayerRep hα ℓ j)) ≫
          (intLinHomIso M (genericLayer U n S ℓ j)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact intLinHomIso_naturality M (operatorLayerRep hα ℓ j)
  rw [layerLinHomIso_hom, layerLinHomIso_hom, Category.assoc, hinv, ← Category.assoc, hb,
    Category.assoc]

end Bridge

/-! ### The governing class, in the language of complete cohomology -/

section Feed

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {ℓ : ℕ} [Fact ℓ.Prime]
  {U : Type} [Group U] [Finite U] [TopologicalSpace U] (N : ℕ) (S : Type) [Group S] [Finite S]
  (j : ℕ) (φ : Gal(Ω/k) →* U) (T : Set (Subgroup Gal(Ω/k)))
  (M : Rep (ZMod ℓ) U) [FiniteDimensional (ZMod ℓ) ↥M.V]

/-- **One class of complete cohomology of the level in degree minus two governs every everywhere
locally trivial class of the layer.**  The class is produced before any shrinking is chosen, and
its death under a shrinking kills the locally trivial class. -/
def HasTateShaCover : Prop :=
  letI := galLayerAction ℓ U N S j φ
  ∀ ε ∈ sha2 ↥(layerSub ℓ (Generic U N S) j) T,
    ∃ x : ↥(tateModule (linHomObj (intRep M) (intRep (genericLayer U N S ℓ j))) (-2)),
      ∀ (n : ℕ) (α : Generic U N S →* Generic U n S) (hα : IsOperatorHom α),
        tateMap (linHomPostHom (intRep M) (intRepMap (operatorLayerRep hα ℓ j))) (-2) x = 0 →
          letI := galLayerAction ℓ U n S j φ
          coeffH2 (layerSubMap ℓ α j)
            (layerSubMap_smul_comm φ (fun _ _ => rfl) (fun _ _ => rfl) hα) ε = 1

/-- **The governing class of complete cohomology is the governing class of first homology the
ladder consumes.**  Complete cohomology in degree minus two is first homology, and the two readings
of the coefficients are identified compatibly with every shrinking, so the class is carried across
and its death is carried with it. -/
theorem hasIntegralShaTateCover_of_hasTateShaCover (h : HasTateShaCover N S j φ T M) :
    HasIntegralShaTateCover ℓ U N S j φ T (dualRep M) := by
  intro ε hε
  obtain ⟨x, hx⟩ := h ε hε
  refine ⟨groupHomology.map (MonoidHom.id U) (layerLinHomIso M (S := S) N j).inv 1 x,
    fun n α hα hkill => ?_⟩
  refine hx n α hα ?_
  exact map_eq_zero_of_isoSquare (layerLinHomIso M (S := S) N j) (layerLinHomIso M (S := S) n j)
    _ _ (layerLinHomIso_naturality M j hα) x hkill

end Feed

/-! ### The governing class, from global duality -/

section Duality

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  (F : IntermediateField k Ω) [FiniteDimensional k ↥F] [IsGalois k ↥F] [NumberField ↥F]
  {ℓ : ℕ} [Fact ℓ.Prime] (S : Type) [Group S] [Finite S] (j : ℕ)
  (M : Rep (ZMod ℓ) (↥F ≃ₐ[k] ↥F)) [FiniteDimensional (ZMod ℓ) ↥M.V] [Finite ↥M.V]
  [IsAddCyclic ↥M.V]

/-- The Galois group acts on a layer, read as a representation over the integers, through the
level. -/
def galIntLayerAction (n : ℕ) : MulDistribMulAction Gal(Ω/k)
    (Multiplicative ↥(intRep (genericLayer (↥F ≃ₐ[k] ↥F) n S ℓ j)).V) :=
  galLayerAction ℓ (↥F ≃ₐ[k] ↥F) n S j (AlgEquiv.restrictNormalHom F)

/-- The Galois group acts on the maps of a module into a layer through the level. -/
def galLinHomAction (n : ℕ) : MulDistribMulAction Gal(Ω/k)
    (Multiplicative ↥(linHomObj (intRep (genericLayer (↥F ≃ₐ[k] ↥F) n S ℓ j)) (intRep M)).V) :=
  MulDistribMulAction.compHom _ (AlgEquiv.restrictNormalHom (K₁ := Ω) F)

omit [FiniteDimensional k ↥F] [Finite S] [IsGalois k Ω] [IsGalois k ↥F] [NumberField ↥F]
  [FiniteDimensional (ZMod ℓ) ↥M.V] [Finite ↥M.V] [IsAddCyclic ↥M.V] in
/-- The order of the module kills every layer, because the residue characteristic divides it. -/
theorem nsmul_layer_eq_zero (hcard : ℓ ∣ Nat.card ↥M.V) (n : ℕ)
    (b : Layer ℓ (Generic (↥F ≃ₐ[k] ↥F) n S) j) : Nat.card ↥M.V • b = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ _).2 hcard, zero_smul]

variable {S j M}

omit [IsGalois k Ω] [Fact ℓ.Prime] [NumberField ↥F] [FiniteDimensional (ZMod ℓ) ↥M.V]
  [Finite ↥M.V] [IsAddCyclic ↥M.V] in
/-- A shrinking of the level, read on the multiplicative copies of the layers, is equivariant for
the action of the Galois group through the level. -/
theorem repMulHom_operatorLayerRep_smul {N n : ℕ}
    {α : Generic (↥F ≃ₐ[k] ↥F) N S →* Generic (↥F ≃ₐ[k] ↥F) n S} (hα : IsOperatorHom α) :
    letI := galIntLayerAction (ℓ := ℓ) F S j N
    letI := galIntLayerAction (ℓ := ℓ) F S j n
    ∀ (g : Gal(Ω/k)) (m : Multiplicative ↥(intRep (genericLayer (↥F ≃ₐ[k] ↥F) N S ℓ j)).V),
      repMulHom (intRepMap (operatorLayerRep hα ℓ j)) (g • m)
        = g • repMulHom (intRepMap (operatorLayerRep hα ℓ j)) m := by
  letI := galLayerAction ℓ (↥F ≃ₐ[k] ↥F) N S j (AlgEquiv.restrictNormalHom (K₁ := Ω) F)
  letI := galLayerAction ℓ (↥F ≃ₐ[k] ↥F) n S j (AlgEquiv.restrictNormalHom (K₁ := Ω) F)
  exact layerSubMap_smul_comm (AlgEquiv.restrictNormalHom F) (fun _ _ => rfl) (fun _ _ => rfl) hα

variable (S j M)

/-- **Global duality reads the everywhere locally trivial classes of a layer as characters,
compatibly with every shrinking of the level.**  One character is asked for at the level itself,
and for each shrinking an injective character downstairs compatible with it: it is the injectivity
downstairs that turns the death of a character into the death of a class. -/
def HasShrinkShaDualInjection (N : ℕ) : Prop :=
  letI := galIntLayerAction (ℓ := ℓ) F S j N
  letI := galLinHomAction (ℓ := ℓ) F S j M N
  ∃ α : Additive ↥(sha2 (Multiplicative ↥(intRep (genericLayer (↥F ≃ₐ[k] ↥F) N S ℓ j)).V)
        (decompositionSubgroups k Ω)) →+
      (Additive ↥(sha1 (Multiplicative ↥(linHomObj (intRep (genericLayer (↥F ≃ₐ[k] ↥F) N S ℓ j))
        (intRep M)).V) (decompositionSubgroups k Ω)) →ₗ[ℤ] AddCircle (1 : ℚ)),
    ∀ (n : ℕ) (α₀ : Generic (↥F ≃ₐ[k] ↥F) N S →* Generic (↥F ≃ₐ[k] ↥F) n S)
      (hα₀ : IsOperatorHom α₀),
      letI := galIntLayerAction (ℓ := ℓ) F S j n
      letI := galLinHomAction (ℓ := ℓ) F S j M n
      ∃ α' : Additive ↥(sha2 (Multiplicative ↥(intRep (genericLayer (↥F ≃ₐ[k] ↥F) n S ℓ j)).V)
            (decompositionSubgroups k Ω)) →+
          (Additive ↥(sha1 (Multiplicative ↥(linHomObj (intRep (genericLayer (↥F ≃ₐ[k] ↥F) n S ℓ j))
            (intRep M)).V) (decompositionSubgroups k Ω)) →ₗ[ℤ] AddCircle (1 : ℚ)),
        Function.Injective α' ∧
          IsShaDualNatural F (intRep M) (fun _ _ => rfl) (fun _ _ => rfl)
            (intRepMap (operatorLayerRep hα₀ ℓ j))
            (repMulHom_operatorLayerRep_smul F hα₀) α α'

omit [FiniteDimensional (ZMod ℓ) ↥M.V] in
set_option maxHeartbeats 1000000 in
/-- **Global duality produces the governing class of complete cohomology.**  The character the
locally trivial class cuts out is fixed before any shrinking is chosen, and the class of complete
cohomology is cut out from that character alone; a shrinking under which it dies makes the
character of the class carried along the shrinking identically zero, so the injective reading
downstairs makes that class trivial. -/
theorem hasTateShaCover_of_hasShrinkShaDualInjection (hcard : ℓ ∣ Nat.card ↥M.V) (N : ℕ)
    (h : HasShrinkShaDualInjection F S j M N) :
    HasTateShaCover N S j (AlgEquiv.restrictNormalHom (K₁ := Ω) F)
      (decompositionSubgroups k Ω) M := by
  letI := galIntLayerAction (ℓ := ℓ) F S j N
  letI := galLinHomAction (ℓ := ℓ) F S j M N
  obtain ⟨α, hα⟩ := h
  intro ε hε
  obtain ⟨x, hx⟩ := exists_cartierPairing_sha_eq F (intRep M)
    (intRep (genericLayer (↥F ≃ₐ[k] ↥F) N S ℓ j)) (fun _ _ => rfl)
    (nsmul_layer_eq_zero F S j M hcard N) (α (Additive.ofMul ⟨ε, hε⟩))
  refine ⟨x, ?_⟩
  intro n α₀ hα₀ hkill
  letI := galIntLayerAction (ℓ := ℓ) F S j n
  letI := galLinHomAction (ℓ := ℓ) F S j M n
  obtain ⟨α', hinj, hnat⟩ := hα n α₀ hα₀
  exact coeffH2_eq_one_of_cartierPairing_eq F (intRep M) (fun _ _ => rfl) (fun _ _ => rfl)
    (intRepMap (operatorLayerRep hα₀ ℓ j)) (repMulHom_operatorLayerRep_smul F hα₀)
    (nsmul_layer_eq_zero F S j M hcard N) (nsmul_layer_eq_zero F S j M hcard n) hinj hnat
    ⟨ε, hε⟩ x hx hkill

/-- **Global duality makes every everywhere locally trivial class of a layer shrinkable.**  The
governing class of complete cohomology is the governing class of first homology, a covering by
integral homology classes is a covering, a covering by the homology of the level is a covering by
the homology of the semidirect product, and a covered class is a shrinkable class. -/
theorem hasShrinkableSha_of_hasShrinkShaDualInjection (hS : IsPGroup ℓ S)
    (hcard : ℓ ∣ Nat.card ↥M.V) (h : ∀ N : ℕ, HasShrinkShaDualInjection F S j M N) (n : ℕ) :
    HasShrinkableSha ℓ (↥F ≃ₐ[k] ↥F) n S j (AlgEquiv.restrictNormalHom (K₁ := Ω) F)
      (decompositionSubgroups k Ω) :=
  hasShrinkableSha_of_hasShaTateCover ℓ (↥F ≃ₐ[k] ↥F) n S hS j
      (AlgEquiv.restrictNormalHom F) (decompositionSubgroups k Ω) (dualRep M) fun N =>
    hasShaTateCover_of_hasOperatorShaTateCover ℓ (↥F ≃ₐ[k] ↥F) N S j
        (AlgEquiv.restrictNormalHom F) (decompositionSubgroups k Ω) (dualRep M) <|
      hasOperatorShaTateCover_of_hasIntegralShaTateCover ℓ (↥F ≃ₐ[k] ↥F) N S j
          (AlgEquiv.restrictNormalHom F) (decompositionSubgroups k Ω) (dualRep M) <|
        hasIntegralShaTateCover_of_hasTateShaCover N S j (AlgEquiv.restrictNormalHom F)
          (decompositionSubgroups k Ω) M
          (hasTateShaCover_of_hasShrinkShaDualInjection F S j M hcard N (h N))

end Duality

end

end InverseGalois.Shafarevich
