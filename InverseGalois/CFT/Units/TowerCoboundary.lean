/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.CompletionUnits
import InverseGalois.CFT.Units.LocalEmbedding
import InverseGalois.CFT.Units.PlaceRestrict

/-!
# Local coboundaries along a tower

Let `k ⊆ F ⊆ K` be a tower of number fields with `F` normal over `k`, and let `a` be a family of
units of `k` indexed by pairs of automorphisms of `F` over `k`.  Composing with the restriction map
turns `a` into a family indexed by pairs of automorphisms of `K` over `k`, and this file transports
the local hypothesis of the Albert-Brauer-Hasse-Noether theorem from `F` to `K`: if `a` is a
coboundary in the local units at a place of `F`, then the inflated family is a coboundary in the
local units at every place of `K` above it.

The transport is the inclusion of the completion of `F` at the place below into the completion of
`K` at the place above.  That inclusion intertwines the two decomposition-group actions, because an
automorphism of `K` fixing a place restricts to an automorphism of `F` fixing the place below, and
the two induced automorphisms of the completions agree on the smaller one; both sides are
continuous and agree on the dense image of the middle field, where the statement is the defining
property of the restriction.  A local cochain below therefore pushes forward to a local cochain
above with the same coboundary.

The point of the transport is that a place of `K` ramified over `k` may well lie above a place of
`F` which is not, so the hypothesis can be free below and is then supplied above at no cost.

## Main results

* `InverseGalois.CFT.adicCompletionAut_adicCompletionComap_restrict`: **the automorphisms of the
  completions attached to an automorphism fixing a place and to its restriction to the middle field
  agree on the completion of the middle field.**
* `InverseGalois.CFT.stabilizerRestrictPlace`: the decomposition group at a place of the top field
  maps to the decomposition group at the place below.
* `InverseGalois.CFT.smulUnitsAut_adicUnitsComap_restrict`: the same compatibility for the local
  units.
* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_restrict`: **a family of units of the base which
  is a local coboundary at a place of the middle field inflates to a local coboundary at every
  place of the top field above it.**

## Tags

number field, tower, completion, decomposition group, two-cocycle, coboundary, inflation
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### The automorphism of a completion on the image of the field -/

section AdicCoe

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]

/-- **The automorphism of the completion attached to an automorphism fixing the place carries the
section determined by an element of the field to the section determined by its image.** -/
@[simp]
theorem adicCompletionAut_adicCoe (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k)) (hσ : σ • v = v)
    (y : K) : adicCompletionAut v σ hσ (adicCoe y v) = adicCoe (σ y) v := by
  rw [adicCoe, adicCompletionAut_coe]
  rfl

end AdicCoe

section TowerCoboundary

variable {k F K : Type*} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
  [IsGalois k F]

/-! ### The decomposition group along the tower -/

variable (F) in
omit [NumberField k] [NumberField F] in
/-- **An automorphism of the top field fixing a place fixes the place of the middle field below
it.** -/
theorem restrictNormalHom_smul_primeUnder {σ : Gal(K/k)} {w : HeightOneSpectrum (𝓞 K)}
    (hσ : σ • w = w) :
    AlgEquiv.restrictNormalHom F σ • primeUnder (𝓞 F) w = primeUnder (𝓞 F) w := by
  rw [← primeUnder_smul F σ w, hσ]

variable (F) in
/-- **The decomposition group at a place of the top field maps to the decomposition group at the
place of the middle field below it**, by restriction of automorphisms. -/
noncomputable def stabilizerRestrictPlace (w : HeightOneSpectrum (𝓞 K)) :
    ↥(stabilizer Gal(K/k) w) →* ↥(stabilizer Gal(F/k) (primeUnder (𝓞 F) w)) where
  toFun σ := ⟨AlgEquiv.restrictNormalHom F σ.1,
    mem_stabilizer_iff.mpr (restrictNormalHom_smul_primeUnder F (mem_stabilizer_iff.mp σ.2))⟩
  map_one' := Subtype.ext (map_one (AlgEquiv.restrictNormalHom F))
  map_mul' σ τ := Subtype.ext (map_mul (AlgEquiv.restrictNormalHom F) σ.1 τ.1)

variable (F) in
omit [NumberField k] [NumberField F] in
@[simp]
theorem coe_stabilizerRestrict (w : HeightOneSpectrum (𝓞 K)) (σ : ↥(stabilizer Gal(K/k) w)) :
    (stabilizerRestrictPlace F w σ : Gal(F/k)) = AlgEquiv.restrictNormalHom F σ.1 := rfl

/-! ### The completions along the tower -/

variable (F) in
omit [NumberField k] in
/-- **The automorphisms of the completions attached to an automorphism fixing a place and to its
restriction to the middle field agree on the completion of the middle field**: both sides are
continuous and agree on the dense image of the middle field. -/
theorem adicCompletionAut_adicCompletionComap_restrict (w : HeightOneSpectrum (𝓞 K))
    (σ : Gal(K/k)) (hσ : σ • w = w) (c : (primeUnder (𝓞 F) w).adicCompletion F) :
    adicCompletionAut w σ hσ (adicCompletionComap (𝓞 F) (k := F) (K := K) w c)
      = adicCompletionComap (𝓞 F) (k := F) (K := K) w
          (adicCompletionAut (primeUnder (𝓞 F) w) (AlgEquiv.restrictNormalHom F σ)
            (restrictNormalHom_smul_primeUnder F hσ) c) := by
  refine UniformSpace.Completion.induction_on c ?_ ?_
  · exact isClosed_eq
      ((continuous_adicCompletionAut w σ hσ).comp
        (continuous_adicCompletionComap (𝓞 F) (k := F) (K := K) w))
      ((continuous_adicCompletionComap (𝓞 F) (k := F) (K := K) w).comp
        (continuous_adicCompletionAut (primeUnder (𝓞 F) w) (AlgEquiv.restrictNormalHom F σ)
          (restrictNormalHom_smul_primeUnder F hσ)))
  · intro x
    set y : F := WithVal.equiv ((primeUnder (𝓞 F) w).valuation F) x with hy
    have h1 : adicCompletionComap (𝓞 F) (k := F) (K := K) w (adicCoe y (primeUnder (𝓞 F) w))
        = adicCoe (algebraMap F K y) w := adicCompletionComap_coe (𝓞 F) w y
    have h2 : adicCompletionComap (𝓞 F) (k := F) (K := K) w
          (adicCoe (AlgEquiv.restrictNormalHom F σ y) (primeUnder (𝓞 F) w))
        = adicCoe (algebraMap F K (AlgEquiv.restrictNormalHom F σ y)) w :=
      adicCompletionComap_coe (𝓞 F) w _
    show adicCompletionAut w σ hσ
        (adicCompletionComap (𝓞 F) (k := F) (K := K) w (adicCoe y (primeUnder (𝓞 F) w)))
      = adicCompletionComap (𝓞 F) (k := F) (K := K) w
          (adicCompletionAut (primeUnder (𝓞 F) w) (AlgEquiv.restrictNormalHom F σ)
            (restrictNormalHom_smul_primeUnder F hσ) (adicCoe y (primeUnder (𝓞 F) w)))
    rw [h1, adicCompletionAut_adicCoe, adicCompletionAut_adicCoe, h2,
      algebraMap_restrictNormalHom F]

variable (F) in
omit [NumberField k] in
/-- **The actions of the two decomposition groups on the local units agree on the local units of
the middle field.** -/
theorem smulUnitsAut_adicUnitsComap_restrict (w : HeightOneSpectrum (𝓞 K))
    (σ : ↥(stabilizer Gal(K/k) w)) (c : Additive ((primeUnder (𝓞 F) w).adicCompletion F)ˣ) :
    smulUnitsAut σ (adicUnitsComap F w c)
      = adicUnitsComap F w (smulUnitsAut (stabilizerRestrictPlace F w σ) c) := by
  refine Additive.toMul.injective (Units.ext ?_)
  simp only [coe_smulUnitsAut_apply, coe_adicUnitsComap, stabilizer_smul_adicCompletion_def,
    algebraMap_adicCompletion F w]
  exact adicCompletionAut_adicCompletionComap_restrict F w σ.1 (mem_stabilizer_iff.mp σ.2) _

variable (F) in
/-- **A unit of the middle field, read in the local units of the top field, is the image of its
reading in the local units of the middle field.** -/
theorem adicUnitsComap_adicUnitHom (w : HeightOneSpectrum (𝓞 K)) (y : Fˣ) :
    adicUnitsComap F w (Additive.ofMul (adicUnitHom (primeUnder (𝓞 F) w) y))
      = Additive.ofMul (adicUnitHom w (Units.map (algebraMap F K : F →* K) y)) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [coe_adicUnitsComap, toMul_ofMul, coe_adicUnitHom, toMul_ofMul, coe_adicUnitHom,
    algebraMap_adicCompletion F w]
  exact adicCompletionComap_coe (𝓞 F) w (y : F)

omit [NumberField k] [NumberField F] [NumberField K] [IsGalois k F] in
/-- A unit of the base field reaches the top field through the middle field. -/
theorem units_map_algebraMap_tower (q : kˣ) :
    Units.map (algebraMap F K : F →* K) (Units.map (algebraMap k F : k →* F) q)
      = Units.map (algebraMap k K : k →* K) q :=
  Units.ext (IsScalarTower.algebraMap_apply k F K (q : k)).symm

/-! ### The transport of the local hypothesis -/

variable (F) in
omit [NumberField k] in
/-- **A family of units of the base field which is a local coboundary at a place of the middle
field inflates to a local coboundary at every place of the top field above it.**  The transport is
the inclusion of the completion below into the completion above, which intertwines the two
decomposition-group actions. -/
theorem exists_sub_add_eq_adicUnits_restrict {a : Gal(F/k) → Gal(F/k) → kˣ}
    (w : HeightOneSpectrum (𝓞 K))
    (h : ∃ c : ↥(stabilizer Gal(F/k) (primeUnder (𝓞 F) w)) →
          Additive ((primeUnder (𝓞 F) w).adicCompletion F)ˣ,
        ∀ s t : ↥(stabilizer Gal(F/k) (primeUnder (𝓞 F) w)),
          Additive.ofMul (adicUnitHom (primeUnder (𝓞 F) w)
              (Units.map (algebraMap k F : k →* F) (a s.1 t.1)))
            = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ c : ↥(stabilizer Gal(K/k) w) → Additive (w.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) w),
        Additive.ofMul (adicUnitHom w (Units.map (algebraMap k K : k →* K)
            (a (AlgEquiv.restrictNormalHom F s.1) (AlgEquiv.restrictNormalHom F t.1))))
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun s => adicUnitsComap F w (c (stabilizerRestrictPlace F w s)), fun s t => ?_⟩
  show Additive.ofMul (adicUnitHom w (Units.map (algebraMap k K : k →* K)
      (a (AlgEquiv.restrictNormalHom F s.1) (AlgEquiv.restrictNormalHom F t.1))))
    = smulUnitsAut s (adicUnitsComap F w (c (stabilizerRestrictPlace F w t)))
      - adicUnitsComap F w (c (stabilizerRestrictPlace F w (s * t)))
      + adicUnitsComap F w (c (stabilizerRestrictPlace F w s))
  rw [smulUnitsAut_adicUnitsComap_restrict F w s, map_mul (stabilizerRestrictPlace F w),
    ← map_sub, ← map_add, ← hc (stabilizerRestrictPlace F w s) (stabilizerRestrictPlace F w t),
    adicUnitsComap_adicUnitHom F w, units_map_algebraMap_tower]
  rfl

end TowerCoboundary

end InverseGalois.CFT
