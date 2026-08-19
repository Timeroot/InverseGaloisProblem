import Mathieu.F4

/-!
# The projective plane `PG(2, 4)` and the action of `SL(3, F4)`

We realise the `21` points of the projective plane over the computable field `F4` as the set
`P` of *normalised* nonzero vectors in `F4³` (a vector whose first nonzero coordinate is `1`),
and let `SL(3, F4)` act on them by matrix multiplication followed by renormalisation.  This
gives a group homomorphism `psi21 : SL(3, F4) →* Perm (Fin 21)`, and, extending by the
identity on the two extra points, `psi34 : SL(3, F4) →* Perm (Fin 23)`.

Everything here is *computable* (unlike the `GaloisField 2 2` model), so the resulting
permutations can be evaluated and checked by `native_decide`.
-/

namespace Mathieu

open Matrix Equiv
open scoped MatrixGroups

namespace PSL34

set_option maxRecDepth 4000

/-- The index of the first nonzero coordinate of a vector in `F4³` (`2` if the vector is zero). -/
def leadIdx (v : Fin 3 → F4) : Fin 3 :=
  if v 0 ≠ 0 then 0 else if v 1 ≠ 0 then 1 else 2

/-- Normalise a vector: divide by its first nonzero coordinate. -/
def nrm (v : Fin 3 → F4) : Fin 3 → F4 := (v (leadIdx v))⁻¹ • v

/-- A projective point is a normalised nonzero vector. -/
def IsPt (v : Fin 3 → F4) : Prop := v ≠ 0 ∧ nrm v = v

instance : DecidablePred IsPt := fun v => by unfold IsPt; infer_instance

/-- The type of the `21` points of `PG(2, 4)`. -/
def P : Type := {v : Fin 3 → F4 // IsPt v}

instance : DecidableEq P := Subtype.instDecidableEq
instance : Fintype P := Subtype.fintype _

/-! ### Basic properties of `nrm` -/

theorem leadIdx_spec (v : Fin 3 → F4) (hv : v ≠ 0) : v (leadIdx v) ≠ 0 := by
  decide +revert

theorem leadIdx_smul (a : F4) (ha : a ≠ 0) (v : Fin 3 → F4) :
    leadIdx (a • v) = leadIdx v := by
      decide +revert

/-
Normalisation is scale-invariant.
-/
theorem nrm_smul (a : F4) (ha : a ≠ 0) (v : Fin 3 → F4) : nrm (a • v) = nrm v := by
  unfold nrm;
  simp +decide [ ha, leadIdx_smul, smul_smul ]

theorem nrm_ne_zero (v : Fin 3 → F4) (hv : v ≠ 0) : nrm v ≠ 0 := by
  decide +revert

/-- `nrm v` is a scalar multiple of `v` by a nonzero scalar. -/
theorem nrm_eq_smul (v : Fin 3 → F4) : nrm v = (v (leadIdx v))⁻¹ • v := rfl

theorem nrm_idem (v : Fin 3 → F4) (hv : v ≠ 0) : nrm (nrm v) = nrm v := by
  decide +revert

/-- `nrm v` is a projective point when `v ≠ 0`. -/
theorem nrm_isPt (v : Fin 3 → F4) (hv : v ≠ 0) : IsPt (nrm v) :=
  ⟨nrm_ne_zero v hv, nrm_idem v hv⟩

/-! ### The action of `SL(3, F4)` -/

theorem mulVec_ne_zero (g : SL(3, F4)) (v : Fin 3 → F4) (hv : v ≠ 0) :
    (↑g : Matrix (Fin 3) (Fin 3) F4) *ᵥ v ≠ 0 := by
      have h_inv : ∃ h : Matrix (Fin 3) (Fin 3) F4, h * g.val = 1 := by
        use g⁻¹.val;
        simp +decide [ Matrix.adjugate_mul ];
      obtain ⟨ h, hh ⟩ := h_inv; intro H; have := congr_arg ( fun x => h.mulVec x ) H; norm_num [ hh ] at this; aesop;

/-- The (renormalised) matrix action on vectors. -/
def act (g : SL(3, F4)) (v : Fin 3 → F4) : Fin 3 → F4 := nrm ((↑g : Matrix (Fin 3) (Fin 3) F4) *ᵥ v)

theorem act_isPt (g : SL(3, F4)) (p : P) : IsPt (act g p.1) :=
  nrm_isPt _ (mulVec_ne_zero g p.1 p.2.1)

instance : SMul (SL(3, F4)) P := ⟨fun g p => ⟨act g p.1, act_isPt g p⟩⟩

theorem smul_def (g : SL(3, F4)) (p : P) : (g • p).1 = nrm ((↑g : Matrix (Fin 3) (Fin 3) F4) *ᵥ p.1) := rfl

instance : MulAction (SL(3, F4)) P where
  one_smul p := by
    decide +revert
  mul_smul g h p := by
    apply Subtype.ext
    simp only [smul_def]
    have hwne : (↑h : Matrix (Fin 3) (Fin 3) F4) *ᵥ p.1 ≠ 0 := mulVec_ne_zero h p.1 p.2.1
    have hc : (((↑h : Matrix (Fin 3) (Fin 3) F4) *ᵥ p.1)
        (leadIdx ((↑h : Matrix (Fin 3) (Fin 3) F4) *ᵥ p.1)))⁻¹ ≠ 0 :=
      inv_ne_zero (leadIdx_spec _ hwne)
    rw [nrm_eq_smul ((↑h : Matrix (Fin 3) (Fin 3) F4) *ᵥ p.1), Matrix.mulVec_smul,
      nrm_smul _ hc]
    congr 1
    rw [Matrix.mulVec_mulVec]
    rfl

/-- The permutation representation `SL(3, F4) →* Perm P`. -/
def psiP : SL(3, F4) →* Perm P := MulAction.toPermHom (SL(3, F4)) P

/-! ### Labelling the `21` points by `Fin 21` -/

/-- The explicit list of the `21` normalised representative vectors. -/
def ptv : Fin 21 → (Fin 3 → F4) :=
  ![ ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, ⟨0,1⟩], ![0, 1, ⟨1,1⟩],
     ![1, 0, 0], ![1, 0, 1], ![1, 0, ⟨0,1⟩], ![1, 0, ⟨1,1⟩],
     ![1, 1, 0], ![1, 1, 1], ![1, 1, ⟨0,1⟩], ![1, 1, ⟨1,1⟩],
     ![1, ⟨0,1⟩, 0], ![1, ⟨0,1⟩, 1], ![1, ⟨0,1⟩, ⟨0,1⟩], ![1, ⟨0,1⟩, ⟨1,1⟩],
     ![1, ⟨1,1⟩, 0], ![1, ⟨1,1⟩, 1], ![1, ⟨1,1⟩, ⟨0,1⟩], ![1, ⟨1,1⟩, ⟨1,1⟩] ]

theorem ptv_isPt (i : Fin 21) : IsPt (ptv i) := by revert i; decide

/-- The inverse labelling: find the index of a point's vector in the table. -/
def idxOfPt (p : P) : Fin 21 :=
  match (List.finRange 21).find? (fun i => ptv i = p.1) with
  | some i => i
  | none => 0

/-- The labelling `Fin 21 ≃ P`. -/
def eP : Fin 21 ≃ P where
  toFun i := ⟨ptv i, ptv_isPt i⟩
  invFun := idxOfPt
  left_inv := by decide
  right_inv := by decide

/-- The permutation representation transported to `Perm (Fin 21)`. -/
def psi21 : SL(3, F4) →* Perm (Fin 21) :=
  ((eP.symm).permCongrHom.toMonoidHom).comp psiP

/-! ### Extending to `Fin 23` (fixing the two extra points `21`, `22`) -/

/-- The inclusion `Fin 21 ≃ {x : Fin 23 // x.val < 21}`. -/
def incl21 : Fin 21 ≃ {x : Fin 23 // x.val < 21} where
  toFun i := ⟨⟨i.val, by omega⟩, i.isLt⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv i := by rfl
  right_inv x := by rfl

/-- The full permutation representation `SL(3, F4) →* Perm (Fin 23)`, fixing `21` and `22`. -/
def psi34 : SL(3, F4) →* Perm (Fin 23) :=
  (Equiv.Perm.extendDomainHom incl21).comp psi21

end PSL34

end Mathieu