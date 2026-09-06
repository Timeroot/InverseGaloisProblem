/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DeltaCoshift
import InverseGalois.CFT.TateCohomology.DeltaRetract
import InverseGalois.CFT.TateCohomology.RestrictDelta
import InverseGalois.CFT.TateCohomology.RestrictNatural
import InverseGalois.CFT.TateCohomology.RestrictShift
import InverseGalois.CFT.TateCohomology.ShiftSplit

/-!
# Restriction against the connecting map of a split extension

An extension which is split as a sequence of modules compares in two ways with the sequences that
define the shift and the coshift, and each comparison survives passage to a subgroup, because
reading a sequence on a subgroup is a functor and carries the identity on the sub to the identity.
The connecting map of the restricted extension is therefore the restricted comparison followed by
the identification of the shift for the subgroup, and dually.

Both descriptions are available in every degree, while the two identifications commute with
restriction only in the range of degrees in which they are the definition.  Playing the two against
each other, together with the degree in which the two recursions meet, gives **the square of
restriction and the connecting map, in every integer degree**, for an extension split as a sequence
of modules; and likewise for corestriction.  Applied to the two defining sequences, which are split,
this removes the restriction on the degree from the two identifications themselves.

## Main results

* `InverseGalois.CFT.Tate.tateRes_tateδ`: **restriction commutes with the connecting map of an
  extension split as a sequence of modules**, in every integer degree.
* `InverseGalois.CFT.Tate.tateCor_tateδ`: **corestriction commutes with the connecting map of an
  extension split as a sequence of modules**, in every integer degree.
* `InverseGalois.CFT.Tate.tateRes_tateShiftEquiv_int` and
  `InverseGalois.CFT.Tate.tateRes_tateCoshiftEquiv_int`: **restriction commutes with the two
  identifications of degree**, in every integer degree.
* `InverseGalois.CFT.Tate.tateCor_tateShiftEquiv_int` and
  `InverseGalois.CFT.Tate.tateCor_tateCoshiftEquiv_int`: **corestriction commutes with the two
  identifications of degree**, in every integer degree.

## Tags

Tate cohomology, restriction, corestriction, connecting homomorphism, dimension shifting
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### The identity read on a subgroup -/

omit [Finite G] in
/-- **The identity read on a subgroup is the identity.** -/
theorem resHom_id (H : Subgroup G) (A : Rep k G) : resHom H (𝟙 A) = 𝟙 (resObj H A) :=
  (Action.res _ H.subtype).map_id A

/-! ### The two comparisons, read on a subgroup -/

section Theta

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (H : Subgroup G)

/-- **The connecting map of a restricted extension comparing with the sequence defining the shift is
the identification of the shift for the subgroup composed with the restricted induced map.** -/
theorem tateδ_res_eq_resShiftEquiv (φ : X ⟶ shiftSeq X.X₁) (hφ : φ.τ₁ = 𝟙 X.X₁) (n : ℤ)
    (z : ↥(tateModule (resSeq H X).X₃ n)) :
    tateδ (resSeq_shortExact hX H) n z
      = resShiftEquiv H X.X₁ n (tateMap (resHom H φ.τ₃) n z) := by
  have h : tateMap (resHom H φ.τ₁) (n + 1) (tateδ (resSeq_shortExact hX H) n z)
      = tateδ (resSeq_shortExact (shiftSeq_shortExact X.X₁) H) n
        (tateMap (resHom H φ.τ₃) n z) :=
    tateδ_naturality_apply (resSeq_shortExact hX H)
      (resSeq_shortExact (shiftSeq_shortExact X.X₁) H) (resSeqHom H φ) n z
  have h1 : tateMap (resHom H φ.τ₁) (n + 1) (tateδ (resSeq_shortExact hX H) n z)
      = tateδ (resSeq_shortExact hX H) n z := by
    rw [hφ]
    exact tateMap_id_apply (resObj H X.X₁) (n + 1) _
  exact h1.symm.trans h

/-- **The connecting map of a restricted extension compared with by the sequence defining the
coshift is the identification of the coshift for the subgroup followed by the restricted induced
map.** -/
theorem tateδ_res_eq_resCoshiftEquiv (ψ : coshiftSeq X.X₃ ⟶ X) (hψ : ψ.τ₃ = 𝟙 X.X₃) (n : ℤ)
    (z : ↥(tateModule (resSeq H X).X₃ n)) :
    tateδ (resSeq_shortExact hX H) n z
      = tateMap (resHom H ψ.τ₁) (n + 1) (resCoshiftEquiv H X.X₃ n z) := by
  have h : tateMap (resHom H ψ.τ₁) (n + 1)
        (tateδ (resSeq_shortExact (coshiftSeq_shortExact X.X₃) H) n z)
      = tateδ (resSeq_shortExact hX H) n (tateMap (resHom H ψ.τ₃) n z) :=
    tateδ_naturality_apply (resSeq_shortExact (coshiftSeq_shortExact X.X₃) H)
      (resSeq_shortExact hX H) (resSeqHom H ψ) n z
  have h3 : tateMap (resHom H ψ.τ₃) n z = z := by
    rw [hψ]
    exact tateMap_id_apply (resObj H X.X₃) n z
  exact (h.trans (congrArg (fun y => tateδ (resSeq_shortExact hX H) n y) h3)).symm

end Theta

/-! ### The two squares for a split extension -/

section Split

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
  (r : ↥X.X₂.V →ₗ[k] ↥X.X₁.V) (hr : ∀ a : ↥X.X₁.V, r (X.f.hom.hom a) = a)
  (s : ↥X.X₃.V →ₗ[k] ↥X.X₂.V) (hs : ∀ v : ↥X.X₃.V, X.g.hom.hom (s v) = v)
  (H : Subgroup G)

/-- The connecting map of a restricted extension whose sub is a direct summand of its middle term is
the restricted map on the quotients followed by the identification of the shift. -/
theorem tateδ_res_eq_retractQuot (n : ℤ) (z : ↥(tateModule (resSeq H X).X₃ n)) :
    tateδ (resSeq_shortExact hX H) n z
      = resShiftEquiv H X.X₁ n
        (tateMap (resHom H (retractQuotHom hX r hr s hs)) n z) :=
  tateδ_res_eq_resShiftEquiv hX H (retractSeqHom hX r hr s hs) rfl n z

/-- The connecting map of a restricted extension whose quotient is a direct summand of its middle
term is the identification of the coshift followed by the restricted trace. -/
theorem tateδ_res_eq_traceSub (n : ℤ) (z : ↥(tateModule (resSeq H X).X₃ n)) :
    tateδ (resSeq_shortExact hX H) n z
      = tateMap (resHom H (traceSubHom hX s hs)) (n + 1) (resCoshiftEquiv H X.X₃ n z) :=
  tateδ_res_eq_resCoshiftEquiv hX H (traceSeqHom hX s hs) rfl n z

include r hr s hs in
/-- **Restriction to a subgroup commutes with the connecting map of an extension split as a sequence
of modules**, in every integer degree. -/
theorem tateRes_tateδ (n : ℤ) (x : ↥(tateModule X.X₃ n)) :
    tateRes H X.X₁ (n + 1) (tateδ hX n x)
      = tateδ (resSeq_shortExact hX H) n (tateRes H X.X₃ n x) := by
  match n, x with
  | .ofNat m, x =>
    calc
      tateRes H X.X₁ (Int.ofNat m + 1) (tateδ hX (Int.ofNat m) x)
          = tateRes H X.X₁ (Int.ofNat m + 1) (tateShiftEquiv X.X₁ (Int.ofNat m)
            (tateMap (retractQuotHom hX r hr s hs) (Int.ofNat m) x)) := by
            rw [tateδ_eq_retractQuot hX r hr s hs]
      _ = resShiftEquiv H X.X₁ (Int.ofNat m) (tateRes H (shiftObj X.X₁) (Int.ofNat m)
            (tateMap (retractQuotHom hX r hr s hs) (Int.ofNat m) x)) :=
          tateRes_tateShiftEquiv H X.X₁ m _
      _ = resShiftEquiv H X.X₁ (Int.ofNat m)
            (tateMap (resHom H (retractQuotHom hX r hr s hs)) (Int.ofNat m)
              (tateRes H X.X₃ (Int.ofNat m) x)) := by
            rw [tateRes_naturality]
      _ = tateδ (resSeq_shortExact hX H) (Int.ofNat m) (tateRes H X.X₃ (Int.ofNat m) x) :=
          (tateδ_res_eq_retractQuot hX r hr s hs H (Int.ofNat m) _).symm
  | .negSucc 0, x => exact tateRes_tateδ_negOne hX H x
  | .negSucc (m + 1), x =>
    calc
      tateRes H X.X₁ (Int.negSucc (m + 1) + 1) (tateδ hX (Int.negSucc (m + 1)) x)
          = tateRes H X.X₁ (Int.negSucc (m + 1) + 1)
            (tateMap (traceSubHom hX s hs) (Int.negSucc (m + 1) + 1)
              (tateCoshiftEquiv X.X₃ (Int.negSucc (m + 1)) x)) := by
            rw [tateδ_eq_traceSub hX s hs]
      _ = tateMap (resHom H (traceSubHom hX s hs)) (Int.negSucc (m + 1) + 1)
            (tateRes H (coshiftObj X.X₃) (Int.negSucc (m + 1) + 1)
              (tateCoshiftEquiv X.X₃ (Int.negSucc (m + 1)) x)) := by
            rw [tateRes_naturality]
      _ = tateMap (resHom H (traceSubHom hX s hs)) (Int.negSucc (m + 1) + 1)
            (resCoshiftEquiv H X.X₃ (Int.negSucc (m + 1))
              (tateRes H X.X₃ (Int.negSucc (m + 1)) x)) := by
            rw [tateRes_tateCoshiftEquiv]
      _ = tateδ (resSeq_shortExact hX H) (Int.negSucc (m + 1))
            (tateRes H X.X₃ (Int.negSucc (m + 1)) x) :=
          (tateδ_res_eq_traceSub hX s hs H (Int.negSucc (m + 1)) _).symm

include r hr s hs in
/-- **Corestriction from a subgroup commutes with the connecting map of an extension split as a
sequence of modules**, in every integer degree. -/
theorem tateCor_tateδ (n : ℤ) (z : ↥(tateModule (resSeq H X).X₃ n)) :
    tateCor H X.X₁ (n + 1) (tateδ (resSeq_shortExact hX H) n z)
      = tateδ hX n (tateCor H X.X₃ n z) := by
  match n, z with
  | .ofNat m, z =>
    calc
      tateCor H X.X₁ (Int.ofNat m + 1) (tateδ (resSeq_shortExact hX H) (Int.ofNat m) z)
          = tateCor H X.X₁ (Int.ofNat m + 1) (resShiftEquiv H X.X₁ (Int.ofNat m)
            (tateMap (resHom H (retractQuotHom hX r hr s hs)) (Int.ofNat m) z)) := by
            rw [tateδ_res_eq_retractQuot hX r hr s hs]
      _ = tateShiftEquiv X.X₁ (Int.ofNat m) (tateCor H (shiftObj X.X₁) (Int.ofNat m)
            (tateMap (resHom H (retractQuotHom hX r hr s hs)) (Int.ofNat m) z)) :=
          tateCor_tateShiftEquiv H X.X₁ m _
      _ = tateShiftEquiv X.X₁ (Int.ofNat m)
            (tateMap (retractQuotHom hX r hr s hs) (Int.ofNat m)
              (tateCor H X.X₃ (Int.ofNat m) z)) := by
            rw [tateCor_naturality]
      _ = tateδ hX (Int.ofNat m) (tateCor H X.X₃ (Int.ofNat m) z) :=
          (tateδ_eq_retractQuot hX r hr s hs (Int.ofNat m) _).symm
  | .negSucc 0, z => exact tateCor_tateδ_negOne hX H z
  | .negSucc (m + 1), z =>
    calc
      tateCor H X.X₁ (Int.negSucc (m + 1) + 1)
          (tateδ (resSeq_shortExact hX H) (Int.negSucc (m + 1)) z)
          = tateCor H X.X₁ (Int.negSucc (m + 1) + 1)
            (tateMap (resHom H (traceSubHom hX s hs)) (Int.negSucc (m + 1) + 1)
              (resCoshiftEquiv H X.X₃ (Int.negSucc (m + 1)) z)) := by
            rw [tateδ_res_eq_traceSub hX s hs]
      _ = tateMap (traceSubHom hX s hs) (Int.negSucc (m + 1) + 1)
            (tateCor H (coshiftObj X.X₃) (Int.negSucc (m + 1) + 1)
              (resCoshiftEquiv H X.X₃ (Int.negSucc (m + 1)) z)) := by
            rw [tateCor_naturality]
      _ = tateMap (traceSubHom hX s hs) (Int.negSucc (m + 1) + 1)
            (tateCoshiftEquiv X.X₃ (Int.negSucc (m + 1))
              (tateCor H X.X₃ (Int.negSucc (m + 1)) z)) := by
            rw [tateCor_tateCoshiftEquiv]
      _ = tateδ hX (Int.negSucc (m + 1)) (tateCor H X.X₃ (Int.negSucc (m + 1)) z) :=
          (tateδ_eq_traceSub hX s hs (Int.negSucc (m + 1)) _).symm

end Split

/-! ### The two identifications, in every degree -/

section Identifications

variable (H : Subgroup G) (A : Rep k G)

/-- **Restriction to a subgroup commutes with the identification of the complete cohomology of the
shift**, in every integer degree. -/
theorem tateRes_tateShiftEquiv_int (n : ℤ) (x : ↥(tateModule (shiftObj A) n)) :
    tateRes H A (n + 1) (tateShiftEquiv A n x)
      = resShiftEquiv H A n (tateRes H (shiftObj A) n x) :=
  tateRes_tateδ (shiftSeq_shortExact A) (coindRetract k G) (coindRetract_shiftSeq_f A)
    (shiftSection A.ρ) (shiftSeq_hom_shiftSection A) H n x

/-- **Corestriction from a subgroup commutes with the identification of the complete cohomology of
the shift**, in every integer degree. -/
theorem tateCor_tateShiftEquiv_int (n : ℤ) (y : ↥(tateModule (resObj H (shiftObj A)) n)) :
    tateCor H A (n + 1) (resShiftEquiv H A n y)
      = tateShiftEquiv A n (tateCor H (shiftObj A) n y) :=
  tateCor_tateδ (shiftSeq_shortExact A) (coindRetract k G) (coindRetract_shiftSeq_f A)
    (shiftSection A.ρ) (shiftSeq_hom_shiftSection A) H n y

/-- **Restriction to a subgroup commutes with the identification of the complete cohomology of the
coshift**, in every integer degree. -/
theorem tateRes_tateCoshiftEquiv_int (n : ℤ) (x : ↥(tateModule A n)) :
    tateRes H (coshiftObj A) (n + 1) (tateCoshiftEquiv A n x)
      = resCoshiftEquiv H A n (tateRes H A n x) :=
  tateRes_tateδ (coshiftSeq_shortExact A) (augRetract A.ρ) (augRetract_coshiftSeq_f A)
    (deltaOne k G) (coshiftSeq_hom_deltaOne A) H n x

/-- **Corestriction from a subgroup commutes with the identification of the complete cohomology of
the coshift**, in every integer degree. -/
theorem tateCor_tateCoshiftEquiv_int (n : ℤ) (y : ↥(tateModule (resObj H A) n)) :
    tateCor H (coshiftObj A) (n + 1) (resCoshiftEquiv H A n y)
      = tateCoshiftEquiv A n (tateCor H A n y) :=
  tateCor_tateδ (coshiftSeq_shortExact A) (augRetract A.ρ) (augRetract_coshiftSeq_f A)
    (deltaOne k G) (coshiftSeq_hom_deltaOne A) H n y

end Identifications

end

end InverseGalois.CFT.Tate
