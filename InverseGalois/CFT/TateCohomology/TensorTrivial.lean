/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TensorFunctor
import InverseGalois.CFT.TateCohomology.TateNakayama

/-!
# Cohomological triviality of a tensor product

Multiplication by a natural number commutes with tensoring, because it may be carried out on either
factor.  So the sequence relating a representation to its reduction modulo a prime stays short
exact after tensoring with a flat representation, and multiplication by that prime is injective on
the complete cohomology of the tensor product as soon as the tensored reduction has none.  For a
`p`-group the order of the group annihilates every degree, and that order is a power of `p`, so the
tensor product has no complete cohomology at all.

The reduction modulo `p` of a representation with no complete cohomology is killed by `p` and has
no first cohomology, hence is the representation on the functions on the group; and the functions
on the group tensored with anything are the functions on the group again, which is acyclic.  The
hypothesis of no torsion at `p` is removed by covering the representation with a free induced one:
the kernel of the covering has no torsion and no complete cohomology, and the long exact sequence
of the covering, tensored with the flat representation, carries the vanishing back to the
representation one started with.

Restriction to a subgroup commutes with tensoring, so the whole argument only has to be run on the
Sylow subgroups.  Feeding the outcome into the connecting map of the tensored extension gives the
theorem of Tate and Nakayama for coefficients which are flat over the integers, with no hypothesis
left over.

## Main results

* `InverseGalois.CFT.Tate.tensorHomLeft_nsmulHom`: **multiplication by a natural number commutes
  with tensoring.**
* `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj_of_isPGroup`: **a representation of a
  `p`-group with no complete cohomology has none after tensoring with a flat representation.**
* `InverseGalois.CFT.Tate.resObj_tensorObj`: **restriction to a subgroup commutes with tensoring.**
* `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj`: **a representation whose restriction to a
  Sylow subgroup for every prime has no complete cohomology in two consecutive degrees has none
  after tensoring with a flat representation.**
* `InverseGalois.CFT.Tate.tateNakayamaFlatEquiv`: **the theorem of Tate and Nakayama** for
  coefficients flat over the integers.

## Tags

Tate cohomology, cohomologically trivial, tensor product, flat module, Tate-Nakayama
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### Multiplication by a natural number after tensoring -/

section Nsmul

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

omit [Finite G] in
/-- **Multiplication by a natural number commutes with tensoring.** -/
theorem tensorHomLeft_nsmulHom (A M : Rep k G) (m : ℕ) :
    tensorHomLeft M (nsmulHom A m) = nsmulHom (tensorObj A M) m := by
  refine tensorHomLeft_ext M fun a v => ?_
  show (m • a) ⊗ₜ[k] v = m • (a ⊗ₜ[k] v)
  rw [← Nat.cast_smul_eq_nsmul k m a, ← Nat.cast_smul_eq_nsmul k m (a ⊗ₜ[k] v),
    TensorProduct.smul_tmul']

end Nsmul

/-! ### Restriction to a subgroup -/

section Restrict

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

omit [Finite G] in
/-- **Restriction to a subgroup commutes with tensoring.** -/
theorem resObj_tensorObj (H : Subgroup G) (A M : Rep k G) :
    resObj H (tensorObj A M) = tensorObj (resObj H A) (resObj H M) := rfl

end Restrict

/-! ### The case of a `p`-group -/

section PGroup

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

/-- **A representation of a `p`-group over the integers killed by `p` with no first cohomology has
no complete cohomology after tensoring with any representation.** -/
theorem isZero_tateModule_tensorObj_of_isZero_H1_int (hG : IsPGroup p G) (A : Rep ℤ G)
    (hp : ∀ v : ↥A.V, p • v = 0) (h1 : Limits.IsZero (groupCohomology A 1)) (M : Rep ℤ G)
    (n : ℤ) : Limits.IsZero (tateModule (tensorObj A M) n) := by
  letI : Module ℤ ↥(A.ρ.invariants) := A.ρ.invariants.module
  letI : Module (ZMod p) ↥A.V := AddCommGroup.zmodModule (n := p) hp
  letI : Module (ZMod p) ↥(A.ρ.invariants) :=
    AddCommGroup.zmodModule (n := p) (nsmul_invariants_eq_zero A hp)
  refine isZero_tateModule_of_iso (tensorIsoLeft M (inducedIsoOfIsZeroH1 hG A hp
    (@intLinear ↥A.V ↥(A.ρ.invariants) _ _ _ A.ρ.invariants.module
      (A.ρ.invariants.subtype.toAddMonoidHom.toZModLinearMap p).leftInverse.toAddMonoidHom)
    (fun v => LinearMap.leftInverse_apply_of_inj
      (f := A.ρ.invariants.subtype.toAddMonoidHom.toZModLinearMap p)
      (LinearMap.ker_eq_bot.2 fun _ _ h => Subtype.ext h) v) h1)) n ?_
  exact isZero_tateModule_tensorObj_inducedRep _ M n

/-- **A representation of a `p`-group over the integers without torsion at `p` and with no complete
cohomology has none after tensoring with a flat representation.** -/
theorem isZero_tateModule_tensorObj_of_torsionFree (hG : IsPGroup p G) (E M : Rep ℤ G)
    (hM : Module.Flat ℤ ↥M.V) (htf : ∀ v : ↥E.V, p • v = 0 → v = 0)
    (hE : ∀ m : ℤ, Limits.IsZero (tateModule E m)) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj E M) n) := by
  haveI := hM
  have hX : (nsmulSeq E p).ShortExact := nsmulSeq_shortExact E p htf
  have hq : Limits.IsZero (tateModule (modNsmul E p) 1) :=
    isZero_tateModule_X₃ hX 1 (hE 1) (hE (1 + 1))
  have hind : ∀ m : ℤ, Limits.IsZero (tateModule (tensorObj (modNsmul E p) M) m) :=
    isZero_tateModule_tensorObj_of_isZero_H1_int hG (modNsmul E p)
      (nsmul_modNsmul_eq_zero E p) hq M
  refine isZero_tateModule_of_injective_nsmul hG (tensorObj E M) (fun m => ?_) n
  have h : Function.Injective (tateMap (tensorHomLeft M (nsmulHom E p)) (m + 1)) :=
    injective_tateMap_f (tensorSeq_shortExact M hX) m (hind m)
  rwa [tensorHomLeft_nsmulHom E M p] at h

/-- **A representation of a `p`-group over the integers with no complete cohomology has none after
tensoring with a flat representation.** -/
theorem isZero_tateModule_tensorObj_of_isPGroup (hG : IsPGroup p G) (E M : Rep ℤ G)
    (hM : Module.Flat ℤ ↥M.V) (hE : ∀ m : ℤ, Limits.IsZero (tateModule E m)) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj E M) n) := by
  haveI := hM
  have hp : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  have hK : (kerSeq (freeHom E)).ShortExact := kerSeq_shortExact _ (freeHom_surjective E)
  have hbij : ∀ m : ℤ, Function.Bijective (tateδ hK m) := fun m =>
    bijective_tateδ hK m (isZero_tateModule_freeObj E m) (isZero_tateModule_freeObj E (m + 1))
  have hker1 : ∀ m : ℤ, Limits.IsZero (tateModule (kerObj (freeHom E)) (m + 1)) := by
    intro m
    refine isZero_of_forall_eq_zero fun y => ?_
    obtain ⟨x, rfl⟩ := (hbij m).2 y
    rw [eq_zero_of_isZero (hE m) x, map_zero]
  have hker : ∀ m : ℤ, Limits.IsZero (tateModule (kerObj (freeHom E)) m) := fun m =>
    isZero_tateModule_congr (by omega) (hker1 (m - 1))
  have htf : ∀ v : ↥(kerObj (freeHom E)).V, p • v = 0 → v = 0 :=
    nsmul_eq_zero_kerObj _ (nsmul_eq_zero_freeObj E hp)
  have hfree : ∀ m : ℤ, Limits.IsZero (tateModule (tensorObj (freeObj E) M) m) := fun m =>
    isZero_tateModule_tensorObj_inducedRep _ M m
  exact isZero_tateModule_X₃ (tensorSeq_shortExact M hK) n (hfree n)
    (isZero_tateModule_tensorObj_of_torsionFree hG (kerObj (freeHom E)) M hM htf hker (n + 1))

end PGroup

/-! ### Reduction to the Sylow subgroups -/

section Sylow

variable {G : Type} [Group G] [Finite G]

/-- **A representation over the integers whose restriction to a Sylow subgroup for every prime has
no complete cohomology in two consecutive degrees has none in any degree after tensoring with a
flat representation.** -/
theorem isZero_tateModule_tensorObj (E M : Rep ℤ G) (hM : Module.Flat ℤ ↥M.V)
    (h : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, ∃ i : ℤ,
      Limits.IsZero (tateModule (resObj (P : Subgroup G) E) i) ∧
        Limits.IsZero (tateModule (resObj (P : Subgroup G) E) (i + 1))) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj E M) n) := by
  have key : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, ∀ m : ℤ,
      Limits.IsZero (tateModule (resObj (P : Subgroup G) (tensorObj E M)) m) := by
    intro q hq P m
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨i, hi, hi1⟩ := h q hq P
    rw [resObj_tensorObj]
    exact isZero_tateModule_tensorObj_of_isPGroup P.isPGroup' (resObj (P : Subgroup G) E)
      (resObj (P : Subgroup G) M) hM
      (isZero_tateModule_of_isZero_two P.isPGroup' (resObj (P : Subgroup G) E) hi hi1) m
  exact isZero_tateModule_of_sylow (tensorObj E M)
    (fun q hq P => ⟨0, key q hq P 0, key q hq P 1⟩) n

/-- **The theorem of Tate and Nakayama**: for coefficients flat over the integers, the complete
cohomology of a representation in a degree is the complete cohomology of its tensor product with a
representation carrying a class which satisfies the classical hypotheses on a Sylow subgroup for
every prime, two degrees higher. -/
def tateNakayamaFlatEquiv (A : Rep ℤ G) (α : tateModule A 2)
    (h : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, IsTateClassTwo (P : Subgroup G) A α) (M : Rep ℤ G)
    (hM : Module.Flat ℤ ↥M.V) (n : ℤ) :
    tateModule M n ≃ₗ[ℤ] tateModule (tensorObj A M) (n + 1 + 1) :=
  tateNakayamaTwoEquiv A α M
    (fun m => isZero_tateModule_tensorObj (cocycleObj (shiftObj A) (tateTwoCocycle A α)) M hM
      (fun q hq P => by
        have hT : IsTateClass (P : Subgroup G) (shiftObj A) (tateTwoCocycle A α) :=
          isTateClass_shiftObj (by
            rw [tateTwoCocycle_spec]
            exact h q hq P)
        refine ⟨0, ?_, ?_⟩
        · rw [resObj_cocycleObj]
          exact isZero_tateModule_cocycleObj_res_zero hT
        · rw [resObj_cocycleObj]
          exact isZero_tateModule_cocycleObj_res_one hT) m) n

end Sylow

end

end InverseGalois.CFT.Tate
