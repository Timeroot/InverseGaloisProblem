/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.Monodromy

/-!
# The fundamental group of a quotient by a free, properly discontinuous action

Let a group `G` act on a topological space `E` so that the quotient map `f : E → X` is a covering
map with `G` acting simply transitively on each fibre (`IsQuotientCoveringMap f G`).  If `E` is
simply connected and path connected, then `G` *is* the fundamental group of the base:

* `IsQuotientCoveringMap.fundamentalGroupMulEquiv : FundamentalGroup X (f e₀) ≃* G`.

This is the topological heart of link **C** of `GAGA_DREAM.md` in its cleanest form: for a universal
cover `E → X` presented as a quotient by the deck group `G`, one has `π₁(X) ≅ G`.  The isomorphism
sends a loop class to the deck transformation carrying `e₀` to the endpoint of the loop's lift.

The construction assembles two bijections and one equivariance fact:

* `actionEquiv : G ≃ f ⁻¹' {f e₀}` — the orbit map `g ↦ g • e₀` identifies `G` with the fibre
  (free + transitive);
* `IsCoveringMap.orbitEquiv : FundamentalGroup X (f e₀) ≃ f ⁻¹' {f e₀}` — the monodromy orbit map
  (from `Monodromy.lean`, using simple connectivity);
* `IsCoveringMap.monodromy_comp_deck` — monodromy is `G`-equivariant, which upgrades the composite
  set bijection to a group isomorphism.
-/

open CategoryTheory Topology unitInterval

namespace IsQuotientCoveringMap

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [Group G] [MulAction G E] {f : E → X} (hf : IsQuotientCoveringMap f G)

/-- The fibre of a quotient covering over `f e₀` is the `G`-orbit of `e₀`; the orbit map
`g ↦ g • e₀` identifies the deck group `G` with the fibre, because the action is free
(injective) and transitive on fibres (surjective). -/
noncomputable def actionEquiv (e₀ : E) : G ≃ f ⁻¹' {f e₀} :=
  Equiv.ofBijective
    (fun g => (⟨g • e₀, hf.apply_eq_iff_mem_orbit.mpr ⟨g, rfl⟩⟩ : f ⁻¹' {f e₀}))
    ⟨fun g₁ g₂ h => hf.isCancelSMul.right_cancel' g₁ g₂ e₀ (Subtype.ext_iff.mp h),
     fun e => by
       obtain ⟨g, hg⟩ := hf.apply_eq_iff_mem_orbit.mp e.2
       exact ⟨g, Subtype.ext hg⟩⟩

@[simp] theorem actionEquiv_apply_val (e₀ : E) (g : G) :
    ((hf.actionEquiv e₀ g : f ⁻¹' {f e₀}) : E) = g • e₀ := rfl

/-- The deck-group map underlying the fundamental-group isomorphism: a loop class `γ` is sent to
the unique deck transformation `g` with `g • e₀ = ` (endpoint of the lift of `γ` from `e₀`). -/
noncomputable def deckMap [SimplyConnectedSpace E] (e₀ : E) :
    FundamentalGroup X (f e₀) → G :=
  fun γ => (hf.actionEquiv e₀).symm (hf.isCoveringMap.orbitEquiv (f e₀) ⟨e₀, rfl⟩ γ)

/-- The defining property of `deckMap`: `deckMap γ` moves `e₀` to the endpoint of the lift of a
representative loop of `γ` starting at `e₀`. -/
theorem deckMap_smul [SimplyConnectedSpace E] (e₀ : E) (γ : FundamentalGroup X (f e₀)) :
    hf.deckMap e₀ γ • e₀ = (hf.isCoveringMap.monodromy γ.toPath ⟨e₀, rfl⟩ : E) := by
  have h := (hf.actionEquiv e₀).apply_symm_apply
    (hf.isCoveringMap.orbitEquiv (f e₀) ⟨e₀, rfl⟩ γ)
  exact Subtype.ext_iff.mp h

theorem deckMap_one [SimplyConnectedSpace E] (e₀ : E) : hf.deckMap e₀ 1 = 1 := by
  refine hf.isCancelSMul.right_cancel' _ _ e₀ ?_
  rw [deckMap_smul, one_smul,
    show ((1 : FundamentalGroup X (f e₀)).toPath) = Path.Homotopic.Quotient.refl (f e₀) from rfl,
    hf.isCoveringMap.monodromy_refl]
  rfl

theorem deckMap_mul [SimplyConnectedSpace E] (e₀ : E) (a b : FundamentalGroup X (f e₀)) :
    hf.deckMap e₀ (a * b) = hf.deckMap e₀ b * hf.deckMap e₀ a := by
  have hcc := hf.toContinuousConstSMul
  refine hf.isCancelSMul.right_cancel' _ _ e₀ ?_
  rw [deckMap_smul, mul_smul, deckMap_smul,
    show ((a * b).toPath) = b.toPath.trans a.toPath from rfl,
    hf.isCoveringMap.monodromy_trans_apply]
  have hfb : hf.isCoveringMap.monodromy b.toPath ⟨e₀, rfl⟩
      = ⟨hf.deckMap e₀ b • e₀, hf.apply_eq_iff_mem_orbit.mpr ⟨hf.deckMap e₀ b, rfl⟩⟩ :=
    Subtype.ext (hf.deckMap_smul e₀ b).symm
  rw [hfb]
  exact hf.isCoveringMap.monodromy_comp_deck (g := fun e => hf.deckMap e₀ b • e)
    (continuous_const_smul (hf.deckMap e₀ b))
    (fun e => hf.apply_eq_iff_mem_orbit.mpr ⟨hf.deckMap e₀ b, rfl⟩) a.toPath ⟨e₀, rfl⟩

theorem deckMap_bijective [SimplyConnectedSpace E] (e₀ : E) :
    Function.Bijective (hf.deckMap e₀) :=
  ((hf.isCoveringMap.orbitEquiv (f e₀) ⟨e₀, rfl⟩).trans (hf.actionEquiv e₀).symm).bijective

/-- The deck-group homomorphism `π₁(X, f e₀) →* G`.  Because the monodromy convention makes
`deckMap` an *anti*-homomorphism, the honest homomorphism is `γ ↦ (deckMap γ)⁻¹`. -/
noncomputable def deckHom [SimplyConnectedSpace E] (e₀ : E) :
    FundamentalGroup X (f e₀) →* G where
  toFun γ := (hf.deckMap e₀ γ)⁻¹
  map_one' := by rw [hf.deckMap_one, inv_one]
  map_mul' a b := by rw [hf.deckMap_mul, mul_inv_rev]

theorem deckHom_bijective [SimplyConnectedSpace E] (e₀ : E) :
    Function.Bijective (hf.deckHom e₀) :=
  (inv_involutive (G := G)).bijective.comp (hf.deckMap_bijective e₀)

/-- **The fundamental group of a free, properly discontinuous quotient is the deck group.**
For a quotient covering `f : E → X` by a group `G` with `E` simply connected and path connected,
the fundamental group of `X` at `f e₀` is isomorphic to `G`. -/
noncomputable def fundamentalGroupMulEquiv [SimplyConnectedSpace E] (e₀ : E) :
    FundamentalGroup X (f e₀) ≃* G :=
  MulEquiv.ofBijective (hf.deckHom e₀) (hf.deckHom_bijective e₀)

@[simp] theorem fundamentalGroupMulEquiv_apply [SimplyConnectedSpace E] (e₀ : E)
    (γ : FundamentalGroup X (f e₀)) :
    hf.fundamentalGroupMulEquiv e₀ γ = (hf.deckMap e₀ γ)⁻¹ := rfl

end IsQuotientCoveringMap

namespace IsAddQuotientCoveringMap

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [AddGroup A] [AddAction A E] {f : E → X}

/-- An additive quotient covering by a group `A` is a multiplicative quotient covering by the
`Multiplicative` deck group.  (`Multiplicative A` acts on `E` via `AddAction A E`.) -/
theorem toMultiplicative (h : IsAddQuotientCoveringMap f A) :
    IsQuotientCoveringMap f (Multiplicative A) where
  toIsQuotientMap := h.toIsQuotientMap
  toContinuousConstSMul :=
    { continuous_const_smul := fun g => by
        have := h.toContinuousConstVAdd; exact continuous_const_vadd (Multiplicative.toAdd g) }
  apply_eq_iff_mem_orbit := h.apply_eq_iff_mem_orbit
  disjoint := h.disjoint

/-- **The additive form.**  For a free, properly discontinuous additive quotient covering
`f : E → X` by an additive group `A` with `E` simply connected and path connected, `π₁(X, f e₀)` is
isomorphic to the multiplicative group `Multiplicative A`. -/
noncomputable def fundamentalGroupMulEquiv [SimplyConnectedSpace E]
    (h : IsAddQuotientCoveringMap f A) (e₀ : E) :
    FundamentalGroup X (f e₀) ≃* Multiplicative A :=
  h.toMultiplicative.fundamentalGroupMulEquiv e₀

end IsAddQuotientCoveringMap
