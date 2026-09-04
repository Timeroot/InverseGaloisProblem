/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Restrict
import InverseGalois.CFT.TateCohomology.ShiftNatural

/-!
# Restriction and corestriction are natural in the representation

Restriction to a subgroup and corestriction from it are defined in the two middle degrees by hand
and carried to every other degree by dimension shifting.  Both halves of that construction are
natural in the representation: in the two middle degrees because the transfer commutes with any
equivariant map, and in the shifted degrees because the two identifications used are connecting
maps, and a connecting map commutes with a map of short exact sequences.

The induction is therefore the same one that defines the two maps.  A map of representations is read
on the subgroup, a map of short exact sequences with it, and the sequences defining the shift and
the coshift are functorial, so each step of the recursion is a square built out of squares that are
already known to commute.

## Main definitions

* `InverseGalois.CFT.Tate.resHom`: a map of representations read as a map of representations of a
  subgroup.
* `InverseGalois.CFT.Tate.resSeqHom`: a map of short exact sequences read on a subgroup.

## Main results

* `InverseGalois.CFT.Tate.resShiftEquiv_naturality`,
  `InverseGalois.CFT.Tate.resCoshiftEquiv_naturality`: the two identifications used to move a degree
  after restriction commute with a map of representations.
* `InverseGalois.CFT.Tate.tateRes_naturality`, `InverseGalois.CFT.Tate.tateRes_comp_tateMap`:
  **restriction to a subgroup commutes with a map of representations**, in every integer degree.
* `InverseGalois.CFT.Tate.tateCor_naturality`, `InverseGalois.CFT.Tate.tateCor_comp_tateMap`:
  **corestriction from a subgroup commutes with a map of representations**, in every integer degree.

## Tags

Tate cohomology, restriction, corestriction, naturality, transfer, dimension shifting
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### Maps read on a subgroup -/

/-- **A map of representations read as a map of representations of a subgroup.** -/
def resHom (H : Subgroup G) {A B : Rep k G} (φ : A ⟶ B) : resObj H A ⟶ resObj H B :=
  (Action.res _ H.subtype).map φ

omit [Finite G] in
@[simp]
theorem resHom_hom (H : Subgroup G) {A B : Rep k G} (φ : A ⟶ B) (v : ↥A.V) :
    (resHom H φ).hom.hom v = φ.hom.hom v := rfl

/-- **A map of short exact sequences read on a subgroup.** -/
def resSeqHom (H : Subgroup G) {X Y : ShortComplex (Rep k G)} (ψ : X ⟶ Y) :
    resSeq H X ⟶ resSeq H Y where
  τ₁ := resHom H ψ.τ₁
  τ₂ := resHom H ψ.τ₂
  τ₃ := resHom H ψ.τ₃
  comm₁₂ := by
    show (Action.res _ H.subtype).map ψ.τ₁ ≫ (Action.res _ H.subtype).map Y.f
      = (Action.res _ H.subtype).map X.f ≫ (Action.res _ H.subtype).map ψ.τ₂
    rw [← Functor.map_comp, ← Functor.map_comp, ψ.comm₁₂]
  comm₂₃ := by
    show (Action.res _ H.subtype).map ψ.τ₂ ≫ (Action.res _ H.subtype).map Y.g
      = (Action.res _ H.subtype).map X.g ≫ (Action.res _ H.subtype).map ψ.τ₃
    rw [← Functor.map_comp, ← Functor.map_comp, ψ.comm₂₃]

/-! ### The two transfers commute with a map of representations -/

/-- **The transfer to a subgroup commutes with a map of representations.** -/
theorem hom_transferLeft (H : Subgroup G) {A B : Rep k G} (φ : A ⟶ B) (v : ↥A.V) :
    transferLeft H B.ρ (φ.hom.hom v) = φ.hom.hom (transferLeft H A.ρ v) := by
  letI := Fintype.ofFinite (G ⧸ H)
  rw [transferLeft_apply, transferLeft_apply, map_sum]
  exact Finset.sum_congr rfl fun c _ => (LinearMap.congr_fun (hom_equivariant φ c.out) v).symm

/-- **The opposite transfer to a subgroup commutes with a map of representations.** -/
theorem hom_transferRight (H : Subgroup G) {A B : Rep k G} (φ : A ⟶ B) (v : ↥A.V) :
    transferRight H B.ρ (φ.hom.hom v) = φ.hom.hom (transferRight H A.ρ v) := by
  letI := Fintype.ofFinite (G ⧸ H)
  rw [transferRight_apply, transferRight_apply, map_sum]
  exact Finset.sum_congr rfl fun c _ => (LinearMap.congr_fun (hom_equivariant φ c.out⁻¹) v).symm

/-! ### The two identifications after restriction -/

/-- **The complete cohomology of the shift, read on a subgroup, is the complete cohomology of the
representation, read on the subgroup, one degree higher, naturally in the representation.** -/
theorem resShiftEquiv_naturality (H : Subgroup G) {A B : Rep k G} (φ : A ⟶ B) (n : ℤ)
    (x : ↥(tateModule (resObj H (shiftObj A)) n)) :
    tateMap (resHom H φ) (n + 1) (resShiftEquiv H A n x)
      = resShiftEquiv H B n (tateMap (resHom H (shiftHom φ)) n x) :=
  tateδ_naturality_apply (resSeq_shortExact (shiftSeq_shortExact A) H)
    (resSeq_shortExact (shiftSeq_shortExact B) H) (resSeqHom H (shiftSeqHom φ)) n x

/-- **The complete cohomology of a representation, read on a subgroup, is the complete cohomology of
its coshift, read on the subgroup, one degree higher, naturally in the representation.** -/
theorem resCoshiftEquiv_naturality (H : Subgroup G) {A B : Rep k G} (φ : A ⟶ B) (n : ℤ)
    (x : ↥(tateModule (resObj H A) n)) :
    tateMap (resHom H (coshiftHom φ)) (n + 1) (resCoshiftEquiv H A n x)
      = resCoshiftEquiv H B n (tateMap (resHom H φ) n x) :=
  tateδ_naturality_apply (resSeq_shortExact (coshiftSeq_shortExact A) H)
    (resSeq_shortExact (coshiftSeq_shortExact B) H) (resSeqHom H (coshiftSeqHom φ)) n x

/-! ### Restriction -/

theorem tateResNat_naturality (H : Subgroup G) :
    ∀ (m : ℕ) {A B : Rep k G} (φ : A ⟶ B) (x : ↥(tateModule A (Int.ofNat m))),
      tateResNat H m B (tateMap φ (Int.ofNat m) x)
        = tateMap (resHom H φ) (Int.ofNat m) (tateResNat H m A x) := by
  intro m
  induction m with
  | zero =>
    intro A B φ x
    obtain ⟨v, rfl⟩ := H0mk_surjective A.ρ x
    rfl
  | succ m ih =>
    intro A B φ x
    have h := tateShiftEquiv_naturality φ (Int.ofNat m) ((tateShiftEquiv A (Int.ofNat m)).symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    show (resShiftEquiv H B (Int.ofNat m)) (tateResNat H m (shiftObj B)
        ((tateShiftEquiv B (Int.ofNat m)).symm (tateMap φ (Int.ofNat m + 1) x)))
      = tateMap (resHom H φ) (Int.ofNat m + 1) ((resShiftEquiv H A (Int.ofNat m))
        (tateResNat H m (shiftObj A) ((tateShiftEquiv A (Int.ofNat m)).symm x)))
    rw [h, LinearEquiv.symm_apply_apply, ih (shiftHom φ), resShiftEquiv_naturality]

theorem tateResNegSucc_naturality (H : Subgroup G) :
    ∀ (m : ℕ) {A B : Rep k G} (φ : A ⟶ B) (x : ↥(tateModule A (Int.negSucc m))),
      tateResNegSucc H m B (tateMap φ (Int.negSucc m) x)
        = tateMap (resHom H φ) (Int.negSucc m) (tateResNegSucc H m A x) := by
  intro m
  induction m with
  | zero =>
    intro A B φ x
    refine Subtype.ext ?_
    obtain ⟨v, hv⟩ := Coinvariants.mk_surjective A.ρ x.1
    show resCoinvariants H B.ρ (Coinvariants.map A.ρ B.ρ φ.hom.hom (hom_equivariant φ) x.1)
      = Coinvariants.map (restrictRep H A.ρ) (restrictRep H B.ρ) φ.hom.hom
        (hom_equivariant (resHom H φ)) (resCoinvariants H A.ρ x.1)
    rw [← hv]
    exact congrArg (Coinvariants.mk (restrictRep H B.ρ)) (hom_transferRight H φ v)
  | succ m ih =>
    intro A B φ x
    have h1 : (tateCoshiftEquiv B (Int.negSucc (m + 1))) (tateMap φ (Int.negSucc (m + 1)) x)
        = tateMap (coshiftHom φ) (Int.negSucc m)
          ((tateCoshiftEquiv A (Int.negSucc (m + 1))) x) :=
      (tateCoshiftEquiv_naturality φ (Int.negSucc (m + 1)) x).symm
    have h2 : tateMap (resHom H (coshiftHom φ)) (Int.negSucc m)
          (tateResNegSucc H m (coshiftObj A) ((tateCoshiftEquiv A (Int.negSucc (m + 1))) x))
        = resCoshiftEquiv H B (Int.negSucc (m + 1)) (tateMap (resHom H φ) (Int.negSucc (m + 1))
          ((resCoshiftEquiv H A (Int.negSucc (m + 1))).symm
            (tateResNegSucc H m (coshiftObj A)
              ((tateCoshiftEquiv A (Int.negSucc (m + 1))) x)))) := by
      have h := resCoshiftEquiv_naturality H φ (Int.negSucc (m + 1))
        ((resCoshiftEquiv H A (Int.negSucc (m + 1))).symm
          (tateResNegSucc H m (coshiftObj A) ((tateCoshiftEquiv A (Int.negSucc (m + 1))) x)))
      rw [LinearEquiv.apply_symm_apply] at h
      exact h
    show (resCoshiftEquiv H B (Int.negSucc (m + 1))).symm (tateResNegSucc H m (coshiftObj B)
        ((tateCoshiftEquiv B (Int.negSucc (m + 1))) (tateMap φ (Int.negSucc (m + 1)) x)))
      = tateMap (resHom H φ) (Int.negSucc (m + 1))
        ((resCoshiftEquiv H A (Int.negSucc (m + 1))).symm
          (tateResNegSucc H m (coshiftObj A) ((tateCoshiftEquiv A (Int.negSucc (m + 1))) x)))
    rw [h1, ih (coshiftHom φ), h2, LinearEquiv.symm_apply_apply]

/-- **Restriction to a subgroup commutes with a map of representations**, in every integer
degree. -/
theorem tateRes_naturality (H : Subgroup G) {A B : Rep k G} (φ : A ⟶ B) (n : ℤ)
    (x : ↥(tateModule A n)) :
    tateRes H B n (tateMap φ n x) = tateMap (resHom H φ) n (tateRes H A n x) := by
  match n with
  | .ofNat m => exact tateResNat_naturality H m φ x
  | .negSucc m => exact tateResNegSucc_naturality H m φ x

/-- **The square of restriction and a map of representations commutes**, in every integer degree. -/
theorem tateRes_comp_tateMap (H : Subgroup G) {A B : Rep k G} (φ : A ⟶ B) (n : ℤ) :
    tateRes H B n ∘ₗ (tateMap φ n).hom
      = (tateMap (resHom H φ) n).hom ∘ₗ tateRes H A n :=
  LinearMap.ext fun x => tateRes_naturality H φ n x

/-! ### Corestriction -/

theorem tateCorNat_naturality (H : Subgroup G) :
    ∀ (m : ℕ) {A B : Rep k G} (φ : A ⟶ B) (x : ↥(tateModule (resObj H A) (Int.ofNat m))),
      tateCorNat H m B (tateMap (resHom H φ) (Int.ofNat m) x)
        = tateMap φ (Int.ofNat m) (tateCorNat H m A x) := by
  intro m
  induction m with
  | zero =>
    intro A B φ x
    obtain ⟨v, rfl⟩ := H0mk_surjective (restrictRep H A.ρ) x
    exact congrArg (H0mk B.ρ) (Subtype.ext (hom_transferLeft H φ (v : ↥A.V)))
  | succ m ih =>
    intro A B φ x
    have h1 : (resShiftEquiv H B (Int.ofNat m)).symm
          (tateMap (resHom H φ) (Int.ofNat m + 1) x)
        = tateMap (resHom H (shiftHom φ)) (Int.ofNat m)
          ((resShiftEquiv H A (Int.ofNat m)).symm x) := by
      have h := resShiftEquiv_naturality H φ (Int.ofNat m)
        ((resShiftEquiv H A (Int.ofNat m)).symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      rw [h, LinearEquiv.symm_apply_apply]
    show (tateShiftEquiv B (Int.ofNat m)) (tateCorNat H m (shiftObj B)
        ((resShiftEquiv H B (Int.ofNat m)).symm (tateMap (resHom H φ) (Int.ofNat m + 1) x)))
      = tateMap φ (Int.ofNat m + 1) ((tateShiftEquiv A (Int.ofNat m))
        (tateCorNat H m (shiftObj A) ((resShiftEquiv H A (Int.ofNat m)).symm x)))
    rw [h1, ih (shiftHom φ), tateShiftEquiv_naturality]

theorem tateCorNegSucc_naturality (H : Subgroup G) :
    ∀ (m : ℕ) {A B : Rep k G} (φ : A ⟶ B) (x : ↥(tateModule (resObj H A) (Int.negSucc m))),
      tateCorNegSucc H m B (tateMap (resHom H φ) (Int.negSucc m) x)
        = tateMap φ (Int.negSucc m) (tateCorNegSucc H m A x) := by
  intro m
  induction m with
  | zero =>
    intro A B φ x
    refine Subtype.ext ?_
    obtain ⟨v, hv⟩ := Coinvariants.mk_surjective (restrictRep H A.ρ) x.1
    show corCoinvariants H B.ρ (Coinvariants.map (restrictRep H A.ρ) (restrictRep H B.ρ) φ.hom.hom
        (hom_equivariant (resHom H φ)) x.1)
      = Coinvariants.map A.ρ B.ρ φ.hom.hom (hom_equivariant φ) (corCoinvariants H A.ρ x.1)
    rw [← hv]
    simp only [Coinvariants.map_mk, corCoinvariants_mk]
  | succ m ih =>
    intro A B φ x
    have h1 : (resCoshiftEquiv H B (Int.negSucc (m + 1)))
          (tateMap (resHom H φ) (Int.negSucc (m + 1)) x)
        = tateMap (resHom H (coshiftHom φ)) (Int.negSucc m)
          ((resCoshiftEquiv H A (Int.negSucc (m + 1))) x) :=
      (resCoshiftEquiv_naturality H φ (Int.negSucc (m + 1)) x).symm
    have h2 : tateMap (coshiftHom φ) (Int.negSucc m)
          (tateCorNegSucc H m (coshiftObj A) ((resCoshiftEquiv H A (Int.negSucc (m + 1))) x))
        = tateCoshiftEquiv B (Int.negSucc (m + 1)) (tateMap φ (Int.negSucc (m + 1))
          ((tateCoshiftEquiv A (Int.negSucc (m + 1))).symm
            (tateCorNegSucc H m (coshiftObj A)
              ((resCoshiftEquiv H A (Int.negSucc (m + 1))) x)))) := by
      have h := tateCoshiftEquiv_naturality φ (Int.negSucc (m + 1))
        ((tateCoshiftEquiv A (Int.negSucc (m + 1))).symm
          (tateCorNegSucc H m (coshiftObj A) ((resCoshiftEquiv H A (Int.negSucc (m + 1))) x)))
      rw [LinearEquiv.apply_symm_apply] at h
      exact h
    show (tateCoshiftEquiv B (Int.negSucc (m + 1))).symm (tateCorNegSucc H m (coshiftObj B)
        ((resCoshiftEquiv H B (Int.negSucc (m + 1)))
          (tateMap (resHom H φ) (Int.negSucc (m + 1)) x)))
      = tateMap φ (Int.negSucc (m + 1)) ((tateCoshiftEquiv A (Int.negSucc (m + 1))).symm
        (tateCorNegSucc H m (coshiftObj A) ((resCoshiftEquiv H A (Int.negSucc (m + 1))) x)))
    rw [h1, ih (coshiftHom φ), h2, LinearEquiv.symm_apply_apply]

/-- **Corestriction from a subgroup commutes with a map of representations**, in every integer
degree. -/
theorem tateCor_naturality (H : Subgroup G) {A B : Rep k G} (φ : A ⟶ B) (n : ℤ)
    (x : ↥(tateModule (resObj H A) n)) :
    tateCor H B n (tateMap (resHom H φ) n x) = tateMap φ n (tateCor H A n x) := by
  match n with
  | .ofNat m => exact tateCorNat_naturality H m φ x
  | .negSucc m => exact tateCorNegSucc_naturality H m φ x

/-- **The square of corestriction and a map of representations commutes**, in every integer
degree. -/
theorem tateCor_comp_tateMap (H : Subgroup G) {A B : Rep k G} (φ : A ⟶ B) (n : ℤ) :
    tateCor H B n ∘ₗ (tateMap (resHom H φ) n).hom
      = (tateMap φ n).hom ∘ₗ tateCor H A n :=
  LinearMap.ext fun x => tateCor_naturality H φ n x

end

end InverseGalois.CFT.Tate
