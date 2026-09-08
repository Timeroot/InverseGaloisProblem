/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.ComapIso
import InverseGalois.CFT.Profinite.ExtensionCoeff
import InverseGalois.Solvable.Shafarevich.LevelObstruction

/-!
# An everywhere locally trivial obstruction killed by a second shrinking

The obstruction to carrying a solution one step up the descending `ℓ`-central series is everywhere
locally trivial once the count has made the class of the layer die along the finite family and the
step is locally solvable elsewhere.  Asking such a class to vanish outright is more than the
arithmetic of a number field supplies; what it supplies is that an everywhere locally trivial class
is inflated from the finite quotient the base realization cuts out.

That is enough, because the shrinking count is insensitive to everything but the order of the group
carrying the class, and the operator group has an order fixed in advance.  So the count can be run
a second time, on the single class upstairs the first run leaves behind.  The rank the second run
asks for is settled by the operator group, the intended number of letters and the layer alone, so it
can be fixed before any solution is chosen; a solution with that many times as many letters is then
produced, its obstruction written as an inflated class, and the class killed.  Pushing the solution
down to the intended number of letters carries its obstruction to the image of the class that was
killed, so the pushed down solution lifts.

## Main definitions

* `InverseGalois.Shafarevich.galLayerAction` — the Galois group acts on a layer of a generic
  operator group through the base realization.
* `InverseGalois.Shafarevich.HasInflatedSha` — every everywhere locally trivial class with
  coefficients in a layer is inflated from the operator group along the base realization.

## Main results

* `InverseGalois.Shafarevich.coeffH2_liftObstructionClass_layerSemidirect` — **the obstruction of a
  solution pushed down along a homomorphism of generic operator groups is the obstruction upstairs,
  read through the induced map of the layers.**
* `InverseGalois.Shafarevich.exists_lift_of_levelSolution_of_hasInflatedSha` — **a solution at one
  level lifts to the next as soon as every everywhere locally trivial class of the layer is
  inflated from the operator group.**

## Tags

Shafarevich's theorem, embedding problem, obstruction, p-central series, inflation, Shafarevich
group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

attribute [local instance] genericQuotAction

/-! ### The action on a layer through the base realization -/

/-- **The Galois group acts on a layer of a generic operator group through the base realization.**
The operator group acts on every layer, and the base realization is a homomorphism onto it. -/
def galLayerAction (ℓ : ℕ) (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S] [Finite S]
    (j : ℕ) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (φ : Gal(Ω/k) →* U) :
    MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j) :=
  MulDistribMulAction.compHom _ φ

/-! ### Everywhere locally trivial classes are inflated -/

/-- **Every everywhere locally trivial class of the second cohomology with coefficients in a layer
is inflated from the operator group along the base realization.**

The layer is a module over the operator group, and the Galois group acts on it through the base
realization, so a class of the finite group has a pullback to the Galois group; the condition asks
that the classes trivial on every member of the family are among those pullbacks.  It is what
global duality provides: an everywhere locally trivial class of the second cohomology is dual to a
class of the first cohomology of the dual module, which is detected on the finite level, and
dualizing back writes the class as an inflated one. -/
def HasInflatedSha (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] [TopologicalSpace U]
    (n : ℕ) (S : Type) [Group S] [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [Field Ω]
    [Algebra k Ω] (φ : Gal(Ω/k) →* U) (T : Set (Subgroup Gal(Ω/k))) : Prop :=
  ∀ hsm : IsSmoothHom φ,
    @sha2 Gal(Ω/k) _ _ ↥(layerSub ℓ (Generic U n S) j) _ (galLayerAction ℓ U n S j φ) T ≤
      (@comapH2 Gal(Ω/k) U ↥(layerSub ℓ (Generic U n S) j) _ _ _ _ _
        (galLayerAction ℓ U n S j φ) _ φ (fun _ _ => rfl) hsm).range

/-! ### Pushing an obstruction down -/

/-- **The obstruction of a solution pushed down along a homomorphism of generic operator groups is
the obstruction upstairs, read through the induced map of the layers.**

Both obstructions are the class of the extension one layer gives, pulled back: upstairs along the
solution, downstairs along the solution composed with the homomorphism the map of the groups induces
at the level.  The class upstairs, read through the map of the layers, is the class downstairs
pulled back along that homomorphism, so the two pullbacks in succession are the one pullback
below. -/
theorem coeffH2_liftObstructionClass_layerSemidirect (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U]
    [Finite U] {m n : ℕ} (S : Type) [Group S] [Finite S] (j : ℕ)
    {α : Generic U m S →* Generic U n S} (hα : IsOperatorHom α) {Γ : Type*} [Group Γ]
    [TopologicalSpace Γ] (Φ : Γ →* GenericQuot ℓ U m S j)
    [MulDistribMulAction Γ ↥(layerSub ℓ (Generic U m S) j)]
    [MulDistribMulAction Γ ↥(layerSub ℓ (Generic U n S) j)]
    (hcomm : ∀ (x : Γ) (v : ↥(layerSub ℓ (Generic U m S) j)),
      layerSubMap ℓ α j (x • v) = x • layerSubMap ℓ α j v)
    (hactm : ∀ (x : Γ) (v : ↥(layerSub ℓ (Generic U m S) j)),
      x • v = (layerExtension ℓ (genericAut U m S) j).conjActHom (Φ x) v)
    (hactn : ∀ (x : Γ) (v : ↥(layerSub ℓ (Generic U n S) j)),
      x • v = (layerExtension ℓ (genericAut U n S) j).conjActHom
        (((layerSemidirectMap ℓ hα j).comp Φ) x) v)
    (hkerm : IsOpenNormal Φ.ker)
    (hkern : IsOpenNormal ((layerSemidirectMap ℓ hα j).comp Φ).ker)
    (σm : (layerExtension ℓ (genericAut U m S) j).Section)
    (σn : (layerExtension ℓ (genericAut U n S) j).Section) :
    coeffH2 (layerSubMap ℓ α j) hcomm
        (liftObstructionClass (layerExtension ℓ (genericAut U m S) j) Φ hactm hkerm σm)
      = liftObstructionClass (layerExtension ℓ (genericAut U n S) j)
          ((layerSemidirectMap ℓ hα j).comp Φ) hactn hkern σn := by
  have hsmΦ : IsSmoothHom Φ := isSmoothHom_of_isOpenNormal_ker hkerm
  have hsmψ : IsSmoothHom (layerSemidirectMap ℓ hα j) :=
    isSmoothHom_of_continuous continuous_of_discreteTopology
  -- the action of the group is the action of the level, read through the solution
  have hΦm : ∀ (x : Γ) (v : ↥(layerSub ℓ (Generic U m S) j)), x • v = Φ x • v :=
    smul_eq_smul_map (layerExtension ℓ (genericAut U m S) j) Φ
      (smul_eq_conjActHom_genericLayer ℓ U m S j) hactm
  have hΦn : ∀ (x : Γ) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = Φ x • v := fun x v =>
    (hactn x v).trans
      (smul_eq_conjActHom_genericLayer ℓ U n S j (layerSemidirectMap ℓ hα j (Φ x)) v).symm
  -- the map of the layers is equivariant for the level above
  have hequiv := map_smul_of_extensionMap
    (S₁ := layerExtension ℓ (genericAut U m S) j) (S₂ := layerExtension ℓ (genericAut U n S) j)
    (α := layerSubMap ℓ α j) (ψ := layerSemidirectMap ℓ hα (j + 1))
    (φ := layerSemidirectMap ℓ hα j) (smul_eq_conjActHom_genericLayer ℓ U m S j)
    (smul_eq_conjActHom_genericLayer ℓ U n S j) (fun _ _ => rfl) (inl_layerSemidirectMap ℓ j hα)
    (rightHom_layerSemidirectMap ℓ j hα)
  -- the class above, read through the map of the layers, is the class below pulled back
  have hcmp := coeffH2_extensionClass_eq_comapH2
    (S₁ := layerExtension ℓ (genericAut U m S) j) (S₂ := layerExtension ℓ (genericAut U n S) j)
    (α := layerSubMap ℓ α j) (ψ := layerSemidirectMap ℓ hα (j + 1))
    (φ := layerSemidirectMap ℓ hα j) (smul_eq_conjActHom_genericLayer ℓ U m S j)
    (smul_eq_conjActHom_genericLayer ℓ U n S j) (fun _ _ => rfl) (inl_layerSemidirectMap ℓ j hα)
    (rightHom_layerSemidirectMap ℓ j hα) hsmψ σm σn
  refine Eq.trans ?_ (comapH2_extensionClass (layerExtension ℓ (genericAut U n S) j)
    ((layerSemidirectMap ℓ hα j).comp Φ) (smul_eq_conjActHom_genericLayer ℓ U n S j) hactn hkern
    σn)
  refine Eq.trans (congrArg (fun z => coeffH2 (layerSubMap ℓ α j) hcomm z)
    (comapH2_extensionClass (layerExtension ℓ (genericAut U m S) j) Φ
      (smul_eq_conjActHom_genericLayer ℓ U m S j) hactm hkerm σm).symm) ?_
  refine Eq.trans (coeffH2_comapH2 hΦm hΦn hsmΦ hcomm hequiv _) ?_
  refine Eq.trans (congrArg (fun z => comapH2 Φ hΦn hsmΦ z) hcmp) ?_
  exact comapH2_comapH2 hΦn (fun _ _ => rfl) hsmΦ hsmψ _

/-! ### The lift, once the locally trivial classes are inflated -/

/-- **A solution at one level of the filtration lifts to the next as soon as every everywhere
locally trivial class with coefficients in the layer is inflated from the operator group.**

The rank the second shrinking asks for depends on the operator group, the intended number of
letters and the layer alone, so it is fixed before a solution is chosen.  A solution with that many
times as many letters is produced whose obstruction is everywhere locally trivial, hence inflated
from a single class of the operator group; the second shrinking kills that class, and the solution
pushed down to the intended number of letters has for obstruction the image of the class that was
killed.  The lift is a homomorphism to the group one layer up over the pushed down solution, and
nothing more: whether it is onto, and whether it is again trivial along the family, is left
open. -/
theorem exists_lift_of_levelSolution_of_hasInflatedSha (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U]
    [Finite U] [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type) [Group S] [Finite S]
    (hS : IsPGroup ℓ S) (j : ℕ) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) (hsmφ : IsSmoothHom φ) {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k))
    (T : Set (Subgroup Gal(Ω/k))) (hvan : ∀ m : ℕ, HasLocalLift ℓ U m S j φ D T)
    (hinfl : ∀ m : ℕ, HasInflatedSha ℓ U m S j φ T)
    (h : ∀ m : ℕ, LevelSolution ℓ U S φ (Set.range D) m j) :
    ∃ (Φ : Gal(Ω/k) →* GenericQuot ℓ U n S j) (f : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1)),
      Function.Surjective Φ ∧ IsSmoothHom Φ ∧ (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) ∧
        (∀ A ∈ Set.range D, ∀ x ∈ A, φ x = 1 → Φ x = 1) ∧ IsSmoothHom f ∧
          ∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom (f x) = Φ x := by
  -- the rank the second shrinking needs, fixed before anything about the solution is known
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (j + 1) * (1 * Nat.card U ^ 2 *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r := ⟨_, Nat.lt_succ_self _⟩
  letI := galLayerAction ℓ U (r * n) S j φ
  letI := galLayerAction ℓ U n S j φ
  -- a set theoretic section of each of the two extensions
  have hsurjN := (layerExtension ℓ (genericAut U (r * n) S) j).rightHom_surjective
  let σN : (layerExtension ℓ (genericAut U (r * n) S) j).Section :=
    ⟨Function.surjInv hsurjN, Function.rightInverse_surjInv hsurjN⟩
  have hsurjn := (layerExtension ℓ (genericAut U n S) j).rightHom_surjective
  let σn : (layerExtension ℓ (genericAut U n S) j).Section :=
    ⟨Function.surjInv hsurjn, Function.rightInverse_surjInv hsurjn⟩
  -- a solution at the larger number of letters whose obstruction is everywhere locally trivial
  obtain ⟨ΦN, hNsurj, hNsm, hNright, hNloc, hNsha⟩ :=
    exists_levelSolution_liftObstructionClass_mem_sha2 ℓ U (r * n) S hS j φ D T (hvan (r * n)) σN h
  have hactN : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U (r * n) S) j)),
      x • v = (layerExtension ℓ (genericAut U (r * n) S) j).conjActHom (ΦN x) v := by
    intro x v
    rw [show x • v = φ x • v from rfl, ← hNright x]
    exact (genericQuotAction_smul ℓ U (r * n) (r * n) S j (ΦN x) v).symm.trans
      (smul_eq_conjActHom_genericLayer ℓ U (r * n) S j (ΦN x) v)
  have hkerN : IsOpenNormal ΦN.ker := isOpenNormal_ker_of_isSmoothHom hNsm
  -- the obstruction is inflated from a single class of the operator group
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 (hinfl (r * n) hsmφ (hNsha hactN hkerN))
  -- the second shrinking kills that class
  obtain ⟨a, hasurj, ha⟩ := exists_genericShrink_forall_coeffH2_eq_one U r n S hS
    (MonoidHom.id U) (fun _ _ => rfl) (fun _ _ => rfl) hr fun _ : Fin 1 => y
  have hα : IsOperatorHom (genericShrink U r n S a) := isOperatorHom_genericShrink U r n S a
  have hcomm : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U (r * n) S) j)),
      layerSubMap ℓ (genericShrink U r n S a) j (x • v)
        = x • layerSubMap ℓ (genericShrink U r n S a) j v :=
    layerSubMap_smul_comm φ (fun _ _ => rfl) (fun _ _ => rfl) hα
  have hy1 : coeffH2 (layerSubMap ℓ (genericShrink U r n S a) j) (layerSubMap_smul hα) y = 1 :=
    ha 0
  -- the pushed down solution
  have hΦsm : IsSmoothHom ((layerSemidirectMap ℓ hα j).comp ΦN) :=
    isSmoothHom_comp hNsm (isSmoothHom_of_continuous continuous_of_discreteTopology)
  have hΦright : ∀ x, SemidirectProduct.rightHom (((layerSemidirectMap ℓ hα j).comp ΦN) x) = φ x :=
    fun x => hNright x
  have hΦloc : ∀ A ∈ Set.range D, ∀ x ∈ A, φ x = 1 →
      ((layerSemidirectMap ℓ hα j).comp ΦN) x = 1 := by
    rintro _ ⟨ν, rfl⟩ x hx hx1
    show layerSemidirectMap ℓ hα j (ΦN x) = 1
    rw [hNloc (D ν) ⟨ν, rfl⟩ x hx hx1, _root_.map_one]
  have hactΦ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)),
      x • v = (layerExtension ℓ (genericAut U n S) j).conjActHom
        (((layerSemidirectMap ℓ hα j).comp ΦN) x) v := by
    intro x v
    rw [show x • v = φ x • v from rfl, ← hΦright x]
    exact (genericQuotAction_smul ℓ U n n S j
        (((layerSemidirectMap ℓ hα j).comp ΦN) x) v).symm.trans
      (smul_eq_conjActHom_genericLayer ℓ U n S j (((layerSemidirectMap ℓ hα j).comp ΦN) x) v)
  have hkerΦ : IsOpenNormal ((layerSemidirectMap ℓ hα j).comp ΦN).ker :=
    isOpenNormal_ker_of_isSmoothHom hΦsm
  -- the obstruction of the pushed down solution is the image of the class that was killed
  have hzero : coeffH2 (layerSubMap ℓ (genericShrink U r n S a) j) hcomm
      (liftObstructionClass (layerExtension ℓ (genericAut U (r * n) S) j) ΦN hactN hkerN σN)
        = 1 := by
    rw [← hy]
    refine Eq.trans (coeffH2_comapH2 (fun _ _ => rfl) (fun _ _ => rfl) hsmφ hcomm
      (layerSubMap_smul hα) y) ?_
    rw [hy1, _root_.map_one]
  obtain ⟨f, hfsm, hf⟩ :=
    (liftObstructionClass_eq_one_iff (layerExtension ℓ (genericAut U n S) j)
      ((layerSemidirectMap ℓ hα j).comp ΦN) hactΦ hkerΦ σn).1
      (((coeffH2_liftObstructionClass_layerSemidirect ℓ U S j hα ΦN hcomm hactN hactΦ hkerN hkerΦ
        σN σn).symm.trans hzero))
  exact ⟨(layerSemidirectMap ℓ hα j).comp ΦN, f,
    (layerSemidirectMap_surjective ℓ hα j hasurj).comp hNsurj, hΦsm, hΦright, hΦloc,
    isSmoothHom_of_isSmooth₁ hfsm, hf⟩

end InverseGalois.Shafarevich
