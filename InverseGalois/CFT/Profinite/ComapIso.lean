/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.ExtensionCoeff

/-!
# Pulling back cohomology along a composite, and along an isomorphism

Pulling a smooth class back along a homomorphism is functorial: two pullbacks in succession are the
pullback along the composite, and the pullback along the identity is the identity.  It also
commutes with a map of the coefficients, both operations being composition of the same cocycle with
something.

The reading these are for is transport.  A homomorphism which happens to be an isomorphism has a
pullback with a two sided inverse, so pulling back along it is injective, and a class which becomes
trivial after transport was already trivial.  That is what identifies the cohomology of a
decomposition subgroup of a covering group with the cohomology of the decomposition subgroup below
it, at a place which is completely decomposed: the projection is then an isomorphism of the two, and
an obstruction killed on one is killed on the other.

## Main results

* `InverseGalois.CFT.comapH2_comapH2`: two pullbacks in succession are the pullback along the
  composite.
* `InverseGalois.CFT.coeffH2_comapH2`: **a pullback commutes with a map of the coefficients.**
* `InverseGalois.CFT.comapH2_injective_of_mulEquiv`: **pulling back along an isomorphism is
  injective.**
* `InverseGalois.CFT.eq_one_of_comapH2_eq_one`: a class trivial after transport along an
  isomorphism is trivial.
* `InverseGalois.CFT.resH2_range_eq_one_of_comapH2_eq_one`: **a class whose pullback along an
  injective homomorphism is trivial is trivial on the image of that homomorphism.**

## Tags

profinite group, Galois cohomology, smooth cochain, functoriality, inflation, transport
-/

namespace InverseGalois.CFT

/-! ### Two pullbacks in succession -/

section Comp

variable {G Q R M : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [Group R] [TopologicalSpace R] [CommGroup M] [MulDistribMulAction G M]
  [MulDistribMulAction Q M] [MulDistribMulAction R M] {π : G →* Q} {ρ : Q →* R}

omit [TopologicalSpace G] [TopologicalSpace Q] [TopologicalSpace R] in
/-- The compatibility of the actions with a composite of two homomorphisms. -/
theorem smul_eq_comp_smul (hπ : ∀ (g : G) (m : M), g • m = π g • m)
    (hρ : ∀ (q : Q) (m : M), q • m = ρ q • m) (g : G) (m : M) : g • m = (ρ.comp π) g • m := by
  rw [hπ, hρ]
  rfl

omit [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M]
  [MulDistribMulAction R M] in
/-- A composite of two smooth homomorphisms is smooth. -/
theorem isSmoothHom_comp (hsmπ : IsSmoothHom π) (hsmρ : IsSmoothHom ρ) :
    IsSmoothHom (ρ.comp π) := fun N hN => by
  obtain ⟨N', hN', hle⟩ := hsmρ N hN
  obtain ⟨N'', hN'', hle'⟩ := hsmπ N' hN'
  exact ⟨N'', hN'', fun x hx => Subgroup.mem_comap.2 (hle (Subgroup.mem_comap.1 (hle' hx)))⟩

/-- Two pullbacks of a class of the first cohomology in succession are the pullback along the
composite. -/
theorem comapH1_comapH1 (hπ : ∀ (g : G) (m : M), g • m = π g • m)
    (hρ : ∀ (q : Q) (m : M), q • m = ρ q • m) (hsmπ : IsSmoothHom π) (hsmρ : IsSmoothHom ρ)
    (x : SmoothH1 R M) :
    comapH1 π hπ hsmπ (comapH1 ρ hρ hsmρ x)
      = comapH1 (ρ.comp π) (smul_eq_comp_smul hπ hρ) (isSmoothHom_comp hsmπ hsmρ) x := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rfl

/-- **Two pullbacks of a class of the second cohomology in succession are the pullback along the
composite.** -/
theorem comapH2_comapH2 (hπ : ∀ (g : G) (m : M), g • m = π g • m)
    (hρ : ∀ (q : Q) (m : M), q • m = ρ q • m) (hsmπ : IsSmoothHom π) (hsmρ : IsSmoothHom ρ)
    (x : SmoothH2 R M) :
    comapH2 π hπ hsmπ (comapH2 ρ hρ hsmρ x)
      = comapH2 (ρ.comp π) (smul_eq_comp_smul hπ hρ) (isSmoothHom_comp hsmπ hsmρ) x := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  rfl

end Comp

/-! ### Two homomorphisms which agree -/

section Congr

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M] {π π' : G →* Q}

/-- Equal homomorphisms pull a class of the second cohomology back to the same class. -/
theorem comapH2_congr (h : π = π') (hπ : ∀ (g : G) (m : M), g • m = π g • m)
    (hπ' : ∀ (g : G) (m : M), g • m = π' g • m) (hsm : IsSmoothHom π) (hsm' : IsSmoothHom π')
    (x : SmoothH2 Q M) : comapH2 π hπ hsm x = comapH2 π' hπ' hsm' x := by
  subst h
  rfl

end Congr

/-! ### A pullback and a map of the coefficients -/

section Coeff

variable {G Q M N : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [CommGroup M] [CommGroup N] [MulDistribMulAction G M] [MulDistribMulAction Q M]
  [MulDistribMulAction G N] [MulDistribMulAction Q N] {π : G →* Q} {φ : M →* N}

/-- **Pulling back along a homomorphism commutes with a map of the coefficients**, in the first
cohomology. -/
theorem coeffH1_comapH1 (hπM : ∀ (g : G) (m : M), g • m = π g • m)
    (hπN : ∀ (g : G) (n : N), g • n = π g • n) (hsm : IsSmoothHom π)
    (hφG : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    (hφQ : ∀ (q : Q) (m : M), φ (q • m) = q • φ m) (x : SmoothH1 Q M) :
    coeffH1 φ hφG (comapH1 π hπM hsm x) = comapH1 π hπN hsm (coeffH1 φ hφQ x) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rfl

/-- **Pulling back along a homomorphism commutes with a map of the coefficients**, in the second
cohomology. -/
theorem coeffH2_comapH2 (hπM : ∀ (g : G) (m : M), g • m = π g • m)
    (hπN : ∀ (g : G) (n : N), g • n = π g • n) (hsm : IsSmoothHom π)
    (hφG : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    (hφQ : ∀ (q : Q) (m : M), φ (q • m) = q • φ m) (x : SmoothH2 Q M) :
    coeffH2 φ hφG (comapH2 π hπM hsm x) = comapH2 π hπN hsm (coeffH2 φ hφQ x) := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  rfl

end Coeff

/-! ### Pulling back along an isomorphism -/

section Iso

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M] (e : G ≃* Q)
  (hact : ∀ (g : G) (m : M), g • m = e g • m)

omit [TopologicalSpace G] [TopologicalSpace Q] in
include hact in
/-- The compatibility of the actions with the inverse of an isomorphism. -/
theorem smul_eq_symm_smul (q : Q) (m : M) : q • m = e.symm q • m := by
  rw [hact (e.symm q) m, MulEquiv.apply_symm_apply]

include hact in
/-- Pulling back along an isomorphism and then along its inverse changes nothing. -/
theorem comapH2_comapH2_symm (hsm : IsSmoothHom (e : G →* Q))
    (hsm' : IsSmoothHom (e.symm : Q →* G)) (x : SmoothH2 Q M) :
    comapH2 (e.symm : Q →* G) (smul_eq_symm_smul e hact) hsm'
        (comapH2 (e : G →* Q) hact hsm x) = x := by
  rw [comapH2_comapH2]
  refine Eq.trans (comapH2_congr (π' := MonoidHom.id Q) ?_ _ (fun _ _ => rfl) _
    (isSmoothHom_of_continuous continuous_id) x) (comapH2_id _ x)
  ext q
  exact e.apply_symm_apply q

include hact in
/-- **Pulling a class of the second cohomology back along an isomorphism is injective.** -/
theorem comapH2_injective_of_mulEquiv (hsm : IsSmoothHom (e : G →* Q))
    (hsm' : IsSmoothHom (e.symm : Q →* G)) :
    Function.Injective (comapH2 (e : G →* Q) hact hsm) :=
  Function.LeftInverse.injective
    (g := comapH2 (e.symm : Q →* G) (smul_eq_symm_smul e hact) hsm')
    (comapH2_comapH2_symm e hact hsm hsm')

include hact in
/-- **A class which becomes trivial after transport along an isomorphism was already trivial.** -/
theorem eq_one_of_comapH2_eq_one (hsm : IsSmoothHom (e : G →* Q))
    (hsm' : IsSmoothHom (e.symm : Q →* G)) {x : SmoothH2 Q M}
    (h : comapH2 (e : G →* Q) hact hsm x = 1) : x = 1 :=
  comapH2_injective_of_mulEquiv e hact hsm hsm' (by rw [h, _root_.map_one])

end Iso

/-! ### The image of an injective homomorphism -/

section Range

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [Group Q]
  [TopologicalSpace Q] [DiscreteTopology Q] [CommGroup M] [MulDistribMulAction G M]
  [MulDistribMulAction Q M] {f : G →* Q} (hinj : Function.Injective f)
  (hact : ∀ (g : G) (m : M), g • m = f g • m)

include hinj hact in
/-- **A class of the second cohomology whose pullback along an injective homomorphism is trivial is
trivial on the image of that homomorphism.**  An injective homomorphism is an isomorphism onto its
image, and pulling back along it is pulling back along that isomorphism after restricting. -/
theorem resH2_range_eq_one_of_comapH2_eq_one (hsm : IsSmoothHom f) {x : SmoothH2 Q M}
    (h : comapH2 f hact hsm x = 1) : resH2 f.range x = 1 := by
  have hacte : ∀ (g : G) (m : M), g • m = MonoidHom.ofInjective hinj g • m := hact
  refine eq_one_of_comapH2_eq_one (MonoidHom.ofInjective hinj) hacte
    (isSmoothHom_of_continuous continuous_of_discreteTopology)
    (isSmoothHom_of_continuous continuous_of_discreteTopology) ?_
  refine Eq.trans (comapH2_comapH2 (π := (MonoidHom.ofInjective hinj : G →* ↥f.range))
    (ρ := f.range.subtype) hacte (fun _ _ => rfl)
    (isSmoothHom_of_continuous continuous_of_discreteTopology)
    (isSmoothHom_subtype f.range) x) ?_
  exact Eq.trans (comapH2_congr (π' := f) (MonoidHom.ext fun _ => rfl) _ hact _ hsm x) h

end Range

end InverseGalois.CFT
