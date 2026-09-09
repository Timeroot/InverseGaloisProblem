/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ShaKummerShrink
import InverseGalois.Solvable.Shafarevich.LayerPi
import InverseGalois.Solvable.Shafarevich.LayerTensorOne
import InverseGalois.Solvable.Shafarevich.LevelShrink

/-!
# Shrinking away the everywhere locally trivial classes of a layer

The ladder which climbs a generic operator group one layer at a time has to know that an
obstruction which is trivial at every place disappears once the number of letters is enlarged and
then shrunk back.  Twisted Kummer theory turns that into two counting problems.  Over a finite
Galois subextension carrying enough roots of unity, a class of the second cohomology with
coefficients in a layer is measured by the units of that subextension: the failure of the class to
come from the finite level is one class of the first cohomology, with coefficients the units
tensored against the homomorphisms of the roots of unity into the layer, and what remains after the
descent is one class of the second cohomology of a finite group.

Two enlargements of the alphabet answer the two problems in turn.  The second counting fixes how
many letters are needed to kill a class of the finite level, the first counting fixes how many are
needed on top of that to kill the obstruction to descending, and the composite of the two
shrinkings is a single shrinking that annihilates the class one started from.  The order matters
only in that each bound is chosen before anything about the class is known, which is what lets the
same shrinking serve every class at once.

What arithmetic still has to supply is the local dictionary: at every number of letters, the
reading of a class in the units of the subextension has to be an order at each place outside the
finite set being avoided.  That is named here as a condition on the data and quantified over all
numbers of letters, since the ladder picks the number of letters only after the condition has been
fixed.

## Main definitions

* `InverseGalois.Shafarevich.HasLayerLocalOrdHom`: the local dictionary twisted Kummer theory asks
  of a layer, at every number of letters at once.

## Main results

* `InverseGalois.Shafarevich.fixingSubgroup_le_ker`: a base realization factoring through a finite
  Galois subextension kills the subgroup fixing that subextension.
* `InverseGalois.Shafarevich.actsTrivially_hom_layerSub`: the homomorphisms of the roots of unity
  into a layer are fixed by that subgroup.
* `InverseGalois.Shafarevich.hasShrinkableSha_of_hasLayerLocalOrdHom`: **every everywhere locally
  trivial class with coefficients in a layer dies under a shrinking**, once the local dictionary is
  available at every number of letters.

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, group cohomology, locally trivial class
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace InverseGalois.Shafarevich

open CategoryTheory InverseGalois.CFT IntermediateField groupCohomology TensorProduct

/-! ### The layer as coefficients over a finite Galois level -/

section Data

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (S : Type) [Group S] [Finite S]
  (j : ℕ)
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable (K : IntermediateField k Ω)
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/k) M] {ι : M →* (↥K)ˣ}
variable (φ : Gal(Ω/k) →* U)

omit [Fact ℓ.Prime] [IsGalois k Ω] in
/-- The layer, acted on through the base realization, is fixed by the subgroup fixing a
subextension through which the base realization factors. -/
theorem layerSub_smul_eq_self (m : ℕ) (hker : K.fixingSubgroup ≤ φ.ker)
    (x : ↥K.fixingSubgroup) (e : ↥(layerSub ℓ (Generic U m S) j)) :
    letI := galLayerAction ℓ U m S j φ
    (x : Gal(Ω/k)) • e = e := by
  letI := galLayerAction ℓ U m S j φ
  show φ (x : Gal(Ω/k)) • e = e
  rw [MonoidHom.mem_ker.1 (hker x.2), one_smul]

omit [Fact ℓ.Prime] [IsGalois k Ω] [MulDistribMulAction Gal(Ω/↥K) M] in
/-- **The homomorphisms of the roots of unity into a layer are fixed by the subgroup fixing a
subextension through which the base realization factors.** -/
theorem actsTrivially_hom_layerSub (m : ℕ) (hker : K.fixingSubgroup ≤ φ.ker)
    (htriv : ∀ (σ : Gal(Ω/k)) (n : M), σ • n = n) :
    letI := galLayerAction ℓ U m S j φ
    ActsTrivially K.fixingSubgroup (M →* ↥(layerSub ℓ (Generic U m S) j)) := by
  letI := galLayerAction ℓ U m S j φ
  refine ⟨fun x hx w => MonoidHom.ext fun n => ?_⟩
  show x • w (x⁻¹ • n) = w n
  rw [htriv, layerSub_smul_eq_self ℓ U S j K φ m hker ⟨x, hx⟩]

variable [IsGalois k ↥K] [IsCyclic M]

/-- The local dictionary twisted Kummer theory asks of a layer, at every number of letters at
once. -/
def HasLayerLocalOrdHom (hker : K.fixingSubgroup ≤ φ.ker) (h : IsKummerData ↥K Ω M ι ℓ)
    (htriv : ∀ (σ : Gal(Ω/k)) (n : M), σ • n = n) (hM : Nat.card M = ℓ) {X : Type}
    [MulAction (Gal(Ω/k) ⧸ K.fixingSubgroup) X] [DecidableEq X]
    (g : Additive (↥K)ˣ →+ (X →₀ ℤ)) (T : Set (Subgroup Gal(Ω/k))) : Prop :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  ∀ m : ℕ,
    letI := galLayerAction ℓ U m S j φ
    letI := actsTrivially_hom_layerSub ℓ U S j K φ m hker htriv
    ∀ x : X, HasLocalOrdHom h htriv
      (fun x e => layerSub_smul_eq_self ℓ U S j K φ m hker x e)
      (layerPiMulEquiv ℓ (Generic U m S) j M hM)
      (layerSub_pow_eq_one ℓ (Generic U m S) j) g T x

end Data

/-! ### The two countings, composed -/

section Assembly

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] [TopologicalSpace U] (n : ℕ)
  (S : Type) [Group S] [Finite S] (j : ℕ)
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
  [IsAlgClosure ↥K Ω]
variable {M : Type} [CommGroup M] [Finite M] [IsCyclic M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/k) M] {ι : M →* (↥K)ˣ}
variable (f : Gal(↥K/k) →* U) {φ : Gal(Ω/k) →* U}
variable {X : Type} [MulAction (Gal(Ω/k) ⧸ K.fixingSubgroup) X] [DecidableEq X]
variable (g : Additive (↥K)ˣ →+ (X →₀ ℤ)) (B : Subgroup (↥K)ˣ)
  [IsStableSubgroup (Gal(Ω/k) ⧸ K.fixingSubgroup) B] [Finite (Gal(Ω/k) ⧸ K.fixingSubgroup)]

omit [Finite U] [TopologicalSpace U] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
  [FiniteDimensional k ↥K] [NumberField ↥K] [IsAlgClosure ↥K Ω]
  [Finite (Gal(Ω/k) ⧸ K.fixingSubgroup)] in
include f in
/-- **A base realization factoring through a finite Galois subextension kills the subgroup fixing
that subextension.** -/
theorem fixingSubgroup_le_ker
    (hφ : ∀ x : Gal(Ω/k), φ x = f (AlgEquiv.restrictNormalHom ↥K x)) :
    K.fixingSubgroup ≤ φ.ker := by
  intro x hx
  have hx1 : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K x = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
    exact hx
  rw [MonoidHom.mem_ker, hφ, hx1, _root_.map_one]

/-- **Every everywhere locally trivial class with coefficients in a layer dies under a shrinking,**
once the local dictionary is available at every number of letters. -/
theorem hasShrinkableSha_of_hasLayerLocalOrdHom (hS : IsPGroup ℓ S)
    (hφ : ∀ x : Gal(Ω/k), φ x = f (AlgEquiv.restrictNormalHom ↥K x))
    (h : IsKummerData ↥K Ω M ι ℓ) (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
    (hM : Nat.card M = ℓ)
    (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
      σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
        = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
    (hg : Function.Surjective g)
    (hB : ∀ a : (↥K)ˣ, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Gal(Ω/k) ⧸ K.fixingSubgroup) (a : (↥K)ˣ) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    {d : ℕ} (b : Fin d → Additive ↥B) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (hlocal : HasLayerLocalOrdHom ℓ U S j K φ (fixingSubgroup_le_ker U K f hφ) h htriv hM g
      (decompositionSubgroups k Ω)) :
    HasShrinkableSha ℓ U n S j φ (decompositionSubgroups k Ω) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hker := fixingSubgroup_le_ker U K f hφ
  -- the rank of the second counting, fixed before anything about the class is known
  obtain ⟨r₂, hr₂⟩ : ∃ r₂ : ℕ, (j + 1) * (1 * Nat.card Gal(↥K/k) ^ 2 *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r₂ := ⟨_, Nat.lt_succ_self _⟩
  -- and the rank of the first counting, likewise
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ℕ, (j + 1) *
      (Nat.card ((Gal(Ω/k) ⧸ K.fixingSubgroup) × Fin d × M) *
        Module.finrank (ZMod ℓ) (Layer ℓ (Generic U (r₂ * n) S) j)) < r₁ := ⟨_, Nat.lt_succ_self _⟩
  letI := galLayerAction ℓ U n S j φ
  letI := galLayerAction ℓ U (r₂ * n) S j φ
  letI := galLayerAction ℓ U (r₁ * (r₂ * n)) S j φ
  letI := galLayerAction ℓ U n S j (k := k) (Ω := ↥K) f
  letI := galLayerAction ℓ U (r₂ * n) S j (k := k) (Ω := ↥K) f
  letI := galLayerAction ℓ U (r₁ * (r₂ * n)) S j (k := k) (Ω := ↥K) f
  letI := galLayerAction ℓ U (r₁ * (r₂ * n)) S j (k := ↥K) (Ω := Ω)
    (φ.comp (galRestrictScalarsHom k ↥K Ω))
  letI := actsTrivially_hom_layerSub ℓ U S j K φ (r₁ * (r₂ * n)) hker htriv
  letI := actsTrivially_hom_layerSub ℓ U S j K φ (r₂ * n) hker htriv
  refine ⟨r₁ * (r₂ * n), fun ε hε => ?_⟩
  -- the three actions of the Galois group factor through the finite Galois level
  have hπtop : ∀ (x : Gal(Ω/k)) (e : ↥(layerSub ℓ (Generic U (r₁ * (r₂ * n)) S) j)),
      x • e = AlgEquiv.restrictNormalHom ↥K x • e := by
    intro x e
    show φ x • e = f (AlgEquiv.restrictNormalHom ↥K x) • e
    rw [hφ]
  have hπmid : ∀ (x : Gal(Ω/k)) (e : ↥(layerSub ℓ (Generic U (r₂ * n) S) j)),
      x • e = AlgEquiv.restrictNormalHom ↥K x • e := by
    intro x e
    show φ x • e = f (AlgEquiv.restrictNormalHom ↥K x) • e
    rw [hφ]
  have hπbot : ∀ (x : Gal(Ω/k)) (e : ↥(layerSub ℓ (Generic U n S) j)),
      x • e = AlgEquiv.restrictNormalHom ↥K x • e := by
    intro x e
    show φ x • e = f (AlgEquiv.restrictNormalHom ↥K x) • e
    rw [hφ]
  have hπK : ∀ (x : Gal(Ω/↥K)) (e : ↥(layerSub ℓ (Generic U (r₁ * (r₂ * n)) S) j)),
      x • e = galRestrictScalarsHom k ↥K Ω x • e := fun _ _ => rfl
  -- the obstruction to descending, as one class of the first cohomology
  obtain ⟨w, hw⟩ := exists_forall_coeffH2_of_hasLocalOrdHom K hπtop hπK hπmid h htriv
    (layerSub_smul_eq_self ℓ U S j K φ (r₁ * (r₂ * n)) hker)
    (layerSub_smul_eq_self ℓ U S j K φ (r₂ * n) hker)
    (layerPiMulEquiv ℓ (Generic U (r₁ * (r₂ * n)) S) j M hM)
    (layerPiMulEquiv ℓ (Generic U (r₂ * n) S) j M hM)
    (layerSub_pow_eq_one ℓ (Generic U (r₁ * (r₂ * n)) S) j)
    (layerSub_pow_eq_one ℓ (Generic U (r₂ * n) S) j) hfix g B hg hB hgeq
    (hlocal (r₁ * (r₂ * n))) ε hε
  -- the first counting kills it
  have hψ : ∀ (a : Fin r₁ → ℕ) (u : Gal(Ω/k))
      (e : ↥(layerSub ℓ (Generic U (r₁ * (r₂ * n)) S) j)),
      layerSubMap ℓ (genericShrink U r₁ (r₂ * n) S a) j (u • e)
        = u • layerSubMap ℓ (genericShrink U r₁ (r₂ * n) S a) j e :=
    fun a => layerSubMap_smul_comm φ (fun _ _ => rfl) (fun _ _ => rfl)
      (isOperatorHom_genericShrink U r₁ (r₂ * n) S a)
  obtain ⟨a₁, ha₁surj, ha₁⟩ := exists_genericShrink_map_h1_eq_zero U r₁ (r₂ * n) S hS b hb
    (fun (v : M →* ↥(layerSub ℓ (Generic U (r₁ * (r₂ * n)) S) j)) (t : M) => v t)
    (fun a => MonoidHom.compHom (layerSubMap ℓ (genericShrink U r₁ (r₂ * n) S a) j))
    (fun a => compHom_quotient_smul (M := M) _ (hψ a))
    (fun _ _ hv => MonoidHom.ext fun t => hv t) hr₁ w
  obtain ⟨v, hv⟩ := hw (layerSubMap ℓ (genericShrink U r₁ (r₂ * n) S a₁) j) (hψ a₁) ha₁
  -- and the second counting kills the class it is inflated from
  obtain ⟨a₂, ha₂surj, ha₂⟩ := exists_genericShrink_forall_coeffH2_eq_one U r₂ n S hS f
    (fun _ _ => rfl) (fun _ _ => rfl) hr₂ (fun _ : Fin 1 => v)
  have hχ : ∀ (u : Gal(Ω/k)) (e : ↥(layerSub ℓ (Generic U (r₂ * n) S) j)),
      layerSubMap ℓ (genericShrink U r₂ n S a₂) j (u • e)
        = u • layerSubMap ℓ (genericShrink U r₂ n S a₂) j e :=
    layerSubMap_smul_comm φ (fun _ _ => rfl) (fun _ _ => rfl)
      (isOperatorHom_genericShrink U r₂ n S a₂)
  have hχK : ∀ (u : Gal(↥K/k)) (e : ↥(layerSub ℓ (Generic U (r₂ * n) S) j)),
      layerSubMap ℓ (genericShrink U r₂ n S a₂) j (u • e)
        = u • layerSubMap ℓ (genericShrink U r₂ n S a₂) j e :=
    layerSubMap_smul_comm f (fun _ _ => rfl) (fun _ _ => rfl)
      (isOperatorHom_genericShrink U r₂ n S a₂)
  have hop : IsOperatorHom ((genericShrink U r₂ n S a₂).comp (genericShrink U r₁ (r₂ * n) S a₁)) :=
    (isOperatorHom_genericShrink U r₂ n S a₂).comp
      (isOperatorHom_genericShrink U r₁ (r₂ * n) S a₁)
  refine ⟨(genericShrink U r₂ n S a₂).comp (genericShrink U r₁ (r₂ * n) S a₁), hop,
    ha₂surj.comp ha₁surj, ?_⟩
  have hcompos : ∀ (x : Gal(Ω/k)) (e : ↥(layerSub ℓ (Generic U (r₁ * (r₂ * n)) S) j)),
      ((layerSubMap ℓ (genericShrink U r₂ n S a₂) j).comp
          (layerSubMap ℓ (genericShrink U r₁ (r₂ * n) S a₁) j)) (x • e)
        = x • ((layerSubMap ℓ (genericShrink U r₂ n S a₂) j).comp
          (layerSubMap ℓ (genericShrink U r₁ (r₂ * n) S a₁) j)) e := by
    intro x e
    show layerSubMap ℓ (genericShrink U r₂ n S a₂) j
        (layerSubMap ℓ (genericShrink U r₁ (r₂ * n) S a₁) j (x • e)) = _
    rw [hψ a₁ x e, hχ]
    rfl
  refine Eq.trans (coeffH2_congr (G := Gal(Ω/k))
    (layerSubMap_comp (genericShrink U r₂ n S a₂) (genericShrink U r₁ (r₂ * n) S a₁))
    _ hcompos ε) ?_
  refine Eq.trans (coeffH2_comp (layerSubMap ℓ (genericShrink U r₁ (r₂ * n) S a₁) j) (hψ a₁)
    (layerSubMap ℓ (genericShrink U r₂ n S a₂) j) hχ hcompos ε).symm ?_
  rw [← hv]
  refine Eq.trans (coeffH2_comapH2 hπmid hπbot (isSmoothHom_restrictNormalHom K) hχ hχK v) ?_
  rw [ha₂ 0, _root_.map_one]

end Assembly

end InverseGalois.Shafarevich
