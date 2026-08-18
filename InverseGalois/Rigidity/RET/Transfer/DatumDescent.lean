/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Transfer.BiGeneric
import InverseGalois.Rigidity.RET.Transfer.Descent
import InverseGalois.Rigidity.RET.Transfer.Datum

/-!
# A presentation of a cover descends to the algebraically closed base

A presentation of a cover is a finite list of polynomials in two variables, together with a finite
list of identities between them, a finite list of nonvanishing conditions, and one irreducibility
condition.  Written generically — every polynomial replaced by one with unknown coefficients, monic
of the prescribed degree where monicity is wanted — the identities become polynomial equations in
the unknowns and the nonvanishing conditions become polynomial inequations.  A specialization of
the unknowns to the algebraically closed base which preserves every equation and every inequation,
and which preserves the irreducibility, therefore carries the whole presentation with it.

The branch points are not among the unknowns: they are prescribed in the base field to begin with,
and only the coefficients of the presentation move.

## Main results

* `Rigidity.RET.exists_coverDatum_descend` — a presentation of a cover over an algebraically closed
  extension field, with branch points in the algebraically closed base, descends to the base.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Transfer

/-- The names of the pieces of a presentation of a cover with deck group `G`. -/
inductive Name (G : Type*)
  | f | f₂ | back | num (g : G) | num₂ | den | den₂ | backDen
  | sepNum (g h : G) | sepDen (g h : G)
  | cofA | cofB | cofA₂ | cofB₂ | res | res₂ | locA | locB
  deriving DecidableEq, Fintype

instance {G : Type*} [Finite G] : Finite (Name G) := by
  classical
  haveI := Fintype.ofFinite G
  infer_instance

/-- The unknown coefficients of a generic presentation: for each name, the coefficient of a
monomial of degree at most `N` in the outer variable and at most `D` in the inner one. -/
abbrev Vars (G : Type*) (N D : ℕ) := Name G × Fin (N + 1) × Fin (D + 1)

variable (k : Type*) [CommRing k] {G : Type*} (N D : ℕ)

/-- The generic piece named `nm`, of degree at most `N` in the outer variable and at most `D` in
the inner one. -/
def genPiece (nm : Name G) : Polynomial (Polynomial (MvPolynomial (Vars G N D) k)) :=
  biPoly N D fun a b => MvPolynomial.X (nm, a, b)

/-- The generic piece named `nm`, monic of degree `d` in the outer variable and of degree at most
`D` in the inner one. -/
def genPieceM (d : ℕ) (hd : d ≤ N + 1) (nm : Name G) :
    Polynomial (Polynomial (MvPolynomial (Vars G N D) k)) :=
  biMonic d D fun a b => MvPolynomial.X (nm, a.castLE hd, b)

end Rigidity.RET.Transfer

namespace Rigidity.RET

open Rigidity.RET.Transfer

/-- The pieces of a presentation, named; those which are polynomials in one variable are recorded
as constants. -/
def CoverDatum.piece {F : Type*} [Field F] {G : Type*} [Group G] {r : ℕ} {t : Fin r → F}
    (Dt : CoverDatum F G t) : Name G → Polynomial (Polynomial F)
  | .f => Dt.f
  | .f₂ => Dt.f₂
  | .back => Dt.back
  | .num g => Dt.num g
  | .num₂ => Dt.num₂
  | .den => C Dt.den
  | .den₂ => C Dt.den₂
  | .backDen => C Dt.backDen
  | .sepNum g h => Dt.sepNum g h
  | .sepDen g h => C (Dt.sepDen g h)
  | .cofA => Dt.cofA
  | .cofB => Dt.cofB
  | .cofA₂ => Dt.cofA₂
  | .cofB₂ => Dt.cofB₂
  | .res => C Dt.res
  | .res₂ => C Dt.res₂
  | .locA => C Dt.locA
  | .locB => C Dt.locB

set_option maxHeartbeats 1000000 in
/-- **A presentation of a cover descends to the algebraically closed base, once the shape of the
generic presentation is large enough to hold it.** -/
theorem coverDatum_descend_aux {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K]
    [Algebra k K] {G : Type} [Group G] [Finite G] {r : ℕ} (t : Fin r → k)
    (Dt : CoverDatum K G fun i => algebraMap k K (t i)) (N D : ℕ) (hnN : Nat.card G ≤ N)
    (hNle : ∀ nm : Name G, (Dt.piece nm).natDegree ≤ N)
    (hDle : ∀ (nm : Name G) (i : ℕ), ((Dt.piece nm).coeff i).natDegree ≤ D) :
    Nonempty (CoverDatum k G t) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hdN : Nat.card G ≤ N + 1 := by omega
  -- the values of the unknowns
  obtain ⟨x, hxdef⟩ : ∃ x : Vars G N D → K,
      ∀ s, x s = ((Dt.piece s.1).coeff s.2.1).coeff s.2.2 := ⟨_, fun _ => rfl⟩
  -- the generic pieces, specialized at those values, are the given ones
  have hgx : ∀ nm : Name G, (genPiece k N D nm).map
      (mapRingHom (MvPolynomial.aeval (R := k) x).toRingHom) = Dt.piece nm := by
    intro nm
    rw [genPiece, biPoly_map]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, hxdef]
    exact biPoly_coeff N D (Dt.piece nm) (hNle nm) (hDle nm)
  have hgMx : ∀ nm : Name G, (Dt.piece nm).Monic → (Dt.piece nm).natDegree = Nat.card G →
      (genPieceM k N D (Nat.card G) hdN nm).map
        (mapRingHom (MvPolynomial.aeval (R := k) x).toRingHom) = Dt.piece nm := by
    intro nm hm hd
    rw [genPieceM, biMonic_map]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, hxdef,
      Fin.val_castLE]
    exact biMonic_coeff (Nat.card G) D (Dt.piece nm) hm hd (hDle nm)
  -- the generic equation
  have hFm : ∀ nm : Name G, (genPieceM k N D (Nat.card G) hdN nm).Monic := fun _ =>
    biMonic_monic _ _ _
  have hFdeg : ∀ nm : Name G, (genPieceM k N D (Nat.card G) hdN nm).natDegree = Nat.card G :=
    fun _ => natDegree_biMonic _ _ _
  have hFpos : 0 < (genPieceM k N D (Nat.card G) hdN (Name.f : Name G)).natDegree := by
    rw [hFdeg]; exact Nat.card_pos
  have hirrx : Irreducible ((((genPieceM k N D (Nat.card G) hdN (Name.f : Name G)).map
      (mapRingHom (MvPolynomial.aeval (R := k) x).toRingHom))).map
        (algebraMap (K[X]) (RatFunc K))) := by
    rw [hgMx Name.f Dt.monic Dt.natDegree_eq]
    exact Dt.irreducible
  -- the inequations
  have hjlt : ∀ nm : Name G, ((Dt.piece nm).coeff 0).natDegree < D + 1 :=
    fun nm => Nat.lt_succ_of_le (hDle nm 0)
  obtain ⟨Q, hQdef⟩ : ∃ Q : {nm : Name G // (Dt.piece nm).coeff 0 ≠ 0} →
      MvPolynomial (Vars G N D) k, ∀ j, Q j = MvPolynomial.X
        (j.1, (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)),
          (⟨((Dt.piece j.1).coeff 0).natDegree, hjlt j.1⟩ : Fin (D + 1))) := ⟨_, fun _ => rfl⟩
  have hQ : ∀ j, MvPolynomial.aeval x (Q j) ≠ 0 := by
    intro j
    rw [hQdef, MvPolynomial.aeval_X, hxdef]
    exact mt leadingCoeff_eq_zero.1 j.2
  -- the specialization
  obtain ⟨y, hy, hyQ, hirr⟩ := Transfer.exists_specialization_irreducible (D := D) (K := K)
    (genPieceM k N D (Nat.card G) hdN Name.f) (hFm _) hFpos
    (fun i hi => weight_bound_biMonic (Nat.card G) D _ i hi) x Q hQ hirrx
  -- the specialized pieces
  obtain ⟨pk, hpk⟩ : ∃ pk : Name G → Polynomial (Polynomial k), ∀ nm, pk nm =
      (genPiece k N D nm).map (mapRingHom (MvPolynomial.aeval (R := k) y).toRingHom) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨pkM, hpkM⟩ : ∃ pkM : Name G → Polynomial (Polynomial k), ∀ nm, pkM nm =
      (genPieceM k N D (Nat.card G) hdN nm).map
        (mapRingHom (MvPolynomial.aeval (R := k) y).toRingHom) := ⟨_, fun _ => rfl⟩
  have hMmonic : ∀ nm : Name G, (pkM nm).Monic := by
    intro nm; rw [hpkM]; exact (hFm nm).map _
  have hMdeg : ∀ nm : Name G, (pkM nm).natDegree = Nat.card G := by
    intro nm; rw [hpkM, (hFm nm).natDegree_map, hFdeg]
  have hco : ∀ (nm : Name G) (a : Fin (N + 1)) (b : Fin (D + 1)),
      ((pk nm).coeff a).coeff b =
        MvPolynomial.aeval (R := k) y (MvPolynomial.X (nm, a, b) : MvPolynomial (Vars G N D) k)
        := by
    intro nm a b
    rw [hpk, coeff_map_bi, coeff_map, genPiece, coeff_coeff_biPoly]
    rfl
  have hne0 : ∀ nm : Name G, (Dt.piece nm).coeff 0 ≠ 0 → (pk nm).coeff 0 ≠ 0 := by
    intro nm h hzero
    refine hyQ ⟨nm, h⟩ ?_
    rw [hQdef]
    have hc := hco nm ⟨0, Nat.succ_pos N⟩ ⟨((Dt.piece nm).coeff 0).natDegree, hjlt nm⟩
    rw [← hc, hzero, coeff_zero]
  -- the identities
  have hnum_root : ∀ g : G, (((pkM Name.f).scaleRoots ((pk Name.den).coeff 0)).comp
      (pkM (Name.num g))) %ₘ (pkM Name.f) = 0 := by
    intro g
    have hx0 : (((((genPieceM k N D (Nat.card G) hdN (Name.f : Name G)).scaleRoots
          ((genPiece k N D (Name.den : Name G)).coeff 0)).comp
          (genPieceM k N D (Nat.card G) hdN (Name.num g)))
          %ₘ (genPieceM k N D (Nat.card G) hdN Name.f))).map
        (mapRingHom (MvPolynomial.aeval (R := k) x).toRingHom) = 0 := by
      rw [push_root _ (hFm _) (hFm _), ← coeff_map_bi, hgx Name.den,
        hgMx Name.f Dt.monic Dt.natDegree_eq,
        hgMx (Name.num g) (Dt.num_monic g) (Dt.num_natDegree g)]
      simpa [CoverDatum.piece] using Dt.num_root g
    have hy0 := map_eq_zero_of_specialize hy _ hx0
    rwa [push_root _ (hFm _) (hFm _), ← coeff_map_bi, ← hpk, ← hpkM, ← hpkM] at hy0
  have hnum_mul : ∀ g h : G, (((((pkM (Name.num h)).scaleRoots ((pk Name.den).coeff 0)).comp
      (pkM (Name.num g))) - C ((pk Name.den).coeff 0) ^ (pkM (Name.num h)).natDegree
        * pkM (Name.num (g * h)))) %ₘ (pkM Name.f) = 0 := by
    intro g h
    rw [hMdeg]
    have hx0 : ((((((genPieceM k N D (Nat.card G) hdN (Name.num h)).scaleRoots
          ((genPiece k N D (Name.den : Name G)).coeff 0)).comp
          (genPieceM k N D (Nat.card G) hdN (Name.num g)))
          - C ((genPiece k N D (Name.den : Name G)).coeff 0) ^ Nat.card G
            * genPieceM k N D (Nat.card G) hdN (Name.num (g * h)))
          %ₘ (genPieceM k N D (Nat.card G) hdN Name.f))).map
        (mapRingHom (MvPolynomial.aeval (R := k) x).toRingHom) = 0 := by
      rw [push_mul _ (hFm _) (hFm _), ← coeff_map_bi, hgx Name.den,
        hgMx Name.f Dt.monic Dt.natDegree_eq,
        hgMx (Name.num g) (Dt.num_monic g) (Dt.num_natDegree g),
        hgMx (Name.num h) (Dt.num_monic h) (Dt.num_natDegree h),
        hgMx (Name.num (g * h)) (Dt.num_monic _) (Dt.num_natDegree _)]
      have := Dt.num_mul g h
      rw [Dt.num_natDegree h] at this
      simpa [CoverDatum.piece] using this
    have hy0 := map_eq_zero_of_specialize hy _ hx0
    rwa [push_mul _ (hFm _) (hFm _), ← coeff_map_bi, ← hpk, ← hpkM, ← hpkM, ← hpkM,
      ← hpkM] at hy0
  have hsep : ∀ g h : G, g ≠ h → (((pkM (Name.num g) - pkM (Name.num h))
      * pk (Name.sepNum g h)) - C ((pk (Name.sepDen g h)).coeff 0)) %ₘ (pkM Name.f) = 0 := by
    intro g h hgh
    have hx0 : (((((genPieceM k N D (Nat.card G) hdN (Name.num g))
          - genPieceM k N D (Nat.card G) hdN (Name.num h))
          * genPiece k N D (Name.sepNum g h))
          - C ((genPiece k N D (Name.sepDen g h)).coeff 0))
          %ₘ (genPieceM k N D (Nat.card G) hdN Name.f)).map
        (mapRingHom (MvPolynomial.aeval (R := k) x).toRingHom) = 0 := by
      rw [push_sep _ (hFm _), ← coeff_map_bi, hgx (Name.sepDen g h), hgx (Name.sepNum g h),
        hgMx Name.f Dt.monic Dt.natDegree_eq,
        hgMx (Name.num g) (Dt.num_monic g) (Dt.num_natDegree g),
        hgMx (Name.num h) (Dt.num_monic h) (Dt.num_natDegree h)]
      simpa [CoverDatum.piece] using Dt.sepNum_spec g h hgh
    have hy0 := map_eq_zero_of_specialize hy _ hx0
    rwa [push_sep _ (hFm _), ← coeff_map_bi, ← hpk, ← hpk, ← hpkM, ← hpkM, ← hpkM] at hy0
  have hnum₂_root : (((pkM Name.f₂).scaleRoots ((pk Name.den₂).coeff 0)).comp
      (pk Name.num₂)) %ₘ (pkM Name.f) = 0 := by
    have hx0 : (((((genPieceM k N D (Nat.card G) hdN (Name.f₂ : Name G)).scaleRoots
          ((genPiece k N D (Name.den₂ : Name G)).coeff 0)).comp
          (genPiece k N D (Name.num₂ : Name G)))
          %ₘ (genPieceM k N D (Nat.card G) hdN Name.f))).map
        (mapRingHom (MvPolynomial.aeval (R := k) x).toRingHom) = 0 := by
      rw [push_root _ (hFm _) (hFm _), ← coeff_map_bi, hgx Name.den₂, hgx Name.num₂,
        hgMx Name.f Dt.monic Dt.natDegree_eq, hgMx Name.f₂ Dt.monic₂ Dt.natDegree₂_eq]
      simpa [CoverDatum.piece] using Dt.num₂_root
    have hy0 := map_eq_zero_of_specialize hy _ hx0
    rwa [push_root _ (hFm _) (hFm _), ← coeff_map_bi, ← hpk, ← hpk, ← hpkM, ← hpkM] at hy0
  have hback : ((((pkM Name.back).scaleRoots ((pk Name.den₂).coeff 0)).comp (pk Name.num₂))
      - C (((pk Name.den₂).coeff 0) ^ (pkM Name.back).natDegree * ((pk Name.backDen).coeff 0)) * X)
      %ₘ (pkM Name.f) = 0 := by
    rw [hMdeg]
    have hx0 : (((((genPieceM k N D (Nat.card G) hdN (Name.back : Name G)).scaleRoots
          ((genPiece k N D (Name.den₂ : Name G)).coeff 0)).comp
          (genPiece k N D (Name.num₂ : Name G)))
          - C (((genPiece k N D (Name.den₂ : Name G)).coeff 0) ^ Nat.card G
              * ((genPiece k N D (Name.backDen : Name G)).coeff 0)) * X)
          %ₘ (genPieceM k N D (Nat.card G) hdN Name.f)).map
        (mapRingHom (MvPolynomial.aeval (R := k) x).toRingHom) = 0 := by
      rw [push_back _ (hFm _) (hFm _), ← coeff_map_bi, ← coeff_map_bi, hgx Name.den₂,
        hgx Name.backDen, hgx Name.num₂, hgMx Name.f Dt.monic Dt.natDegree_eq,
        hgMx Name.back Dt.back_monic Dt.back_natDegree]
      have := Dt.back_spec
      rw [Dt.back_natDegree] at this
      simpa [CoverDatum.piece] using this
    have hy0 := map_eq_zero_of_specialize hy _ hx0
    rwa [push_back _ (hFm _) (hFm _), ← coeff_map_bi, ← coeff_map_bi, ← hpk, ← hpk, ← hpk,
      ← hpkM, ← hpkM] at hy0
  have hbez : (pkM Name.f) * (pk Name.cofA) + (pkM Name.f).derivative * (pk Name.cofB)
      = C ((pk Name.res).coeff 0) := by
    have hx0 : ((genPieceM k N D (Nat.card G) hdN (Name.f : Name G)) * genPiece k N D Name.cofA
          + (genPieceM k N D (Nat.card G) hdN (Name.f : Name G)).derivative
            * genPiece k N D Name.cofB
          - C ((genPiece k N D (Name.res : Name G)).coeff 0)).map
        (mapRingHom (MvPolynomial.aeval (R := k) x).toRingHom) = 0 := by
      rw [push_bezout, ← coeff_map_bi, hgx Name.res, hgx Name.cofA, hgx Name.cofB,
        hgMx Name.f Dt.monic Dt.natDegree_eq]
      simpa [CoverDatum.piece] using sub_eq_zero.2 Dt.bezout
    have hy0 := map_eq_zero_of_specialize hy _ hx0
    rw [push_bezout, ← coeff_map_bi, ← hpk, ← hpk, ← hpk, ← hpkM] at hy0
    exact sub_eq_zero.1 hy0
  have hbez₂ : (pkM Name.f₂) * (pk Name.cofA₂) + (pkM Name.f₂).derivative * (pk Name.cofB₂)
      = C ((pk Name.res₂).coeff 0) := by
    have hx0 : ((genPieceM k N D (Nat.card G) hdN (Name.f₂ : Name G)) * genPiece k N D Name.cofA₂
          + (genPieceM k N D (Nat.card G) hdN (Name.f₂ : Name G)).derivative
            * genPiece k N D Name.cofB₂
          - C ((genPiece k N D (Name.res₂ : Name G)).coeff 0)).map
        (mapRingHom (MvPolynomial.aeval (R := k) x).toRingHom) = 0 := by
      rw [push_bezout, ← coeff_map_bi, hgx Name.res₂, hgx Name.cofA₂, hgx Name.cofB₂,
        hgMx Name.f₂ Dt.monic₂ Dt.natDegree₂_eq]
      simpa [CoverDatum.piece] using sub_eq_zero.2 Dt.bezout₂
    have hy0 := map_eq_zero_of_specialize hy _ hx0
    rw [push_bezout, ← coeff_map_bi, ← hpk, ← hpk, ← hpk, ← hpkM] at hy0
    exact sub_eq_zero.1 hy0
  have hlocus : ((pk Name.res).coeff 0) * ((pk Name.locA).coeff 0)
      + ((pk Name.res₂).coeff 0) * ((pk Name.locB).coeff 0)
      = (∏ i, (X - C (t i))) ^ Dt.expo := by
    have hx0 : (((genPiece k N D (Name.res : Name G)).coeff 0)
          * ((genPiece k N D (Name.locA : Name G)).coeff 0)
          + ((genPiece k N D (Name.res₂ : Name G)).coeff 0)
            * ((genPiece k N D (Name.locB : Name G)).coeff 0)
          - (∏ i, (X - C (MvPolynomial.C (t i) : MvPolynomial (Vars G N D) k))) ^ Dt.expo).map
        (MvPolynomial.aeval (R := k) x).toRingHom = 0 := by
      rw [push_locus, ← coeff_map_bi, ← coeff_map_bi, ← coeff_map_bi, ← coeff_map_bi,
        hgx Name.res, hgx Name.locA, hgx Name.res₂, hgx Name.locB]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
      simpa [CoverDatum.piece] using sub_eq_zero.2 Dt.locus
    have hy0 := map_eq_zero_of_specialize₁ hy _ hx0
    rw [push_locus, ← coeff_map_bi, ← coeff_map_bi, ← coeff_map_bi, ← coeff_map_bi, ← hpk,
      ← hpk, ← hpk, ← hpk] at hy0
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
      Algebra.algebraMap_self_apply] at hy0
    exact sub_eq_zero.1 hy0
  -- the descended presentation
  exact ⟨{ f := pkM Name.f
           monic := hMmonic _
           natDegree_eq := hMdeg _
           irreducible := by rw [hpkM]; exact hirr
           den := (pk Name.den).coeff 0
           den_ne := hne0 _ (by simpa [CoverDatum.piece] using Dt.den_ne)
           num := fun g => pkM (Name.num g)
           num_monic := fun _ => hMmonic _
           num_natDegree := fun _ => hMdeg _
           num_root := hnum_root
           num_mul := hnum_mul
           sepNum := fun g h => pk (Name.sepNum g h)
           sepDen := fun g h => (pk (Name.sepDen g h)).coeff 0
           sepDen_ne := fun g h hgh =>
             hne0 _ (by simpa [CoverDatum.piece] using Dt.sepDen_ne g h hgh)
           sepNum_spec := hsep
           f₂ := pkM Name.f₂
           monic₂ := hMmonic _
           natDegree₂_eq := hMdeg _
           den₂ := (pk Name.den₂).coeff 0
           den₂_ne := hne0 _ (by simpa [CoverDatum.piece] using Dt.den₂_ne)
           num₂ := pk Name.num₂
           num₂_root := hnum₂_root
           back := pkM Name.back
           back_monic := hMmonic _
           back_natDegree := hMdeg _
           backDen := (pk Name.backDen).coeff 0
           backDen_ne := hne0 _ (by simpa [CoverDatum.piece] using Dt.backDen_ne)
           back_spec := hback
           cofA := pk Name.cofA
           cofB := pk Name.cofB
           res := (pk Name.res).coeff 0
           bezout := hbez
           cofA₂ := pk Name.cofA₂
           cofB₂ := pk Name.cofB₂
           res₂ := (pk Name.res₂).coeff 0
           bezout₂ := hbez₂
           locA := (pk Name.locA).coeff 0
           locB := (pk Name.locB).coeff 0
           expo := Dt.expo
           locus := hlocus }⟩

/-- **A presentation of a cover over an algebraically closed extension field, whose branch points
lie in the algebraically closed base, descends to the base.**

The coefficients of the presentation are unknowns; the identities between them are equations, the
nonvanishing conditions are inequations, and the connectedness of the cover is the irreducibility
of the equation.  A specialization of the unknowns preserving all three descends the whole
presentation. -/
theorem exists_coverDatum_descend {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K]
    [Algebra k K] {G : Type} [Group G] [Finite G] {r : ℕ} (t : Fin r → k)
    (Dt : CoverDatum K G fun i => algebraMap k K (t i)) :
    Nonempty (CoverDatum k G t) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  exact coverDatum_descend_aux t Dt
    (max (Nat.card G) (Finset.univ.sup fun nm : Name G => (Dt.piece nm).natDegree))
    (Finset.univ.sup fun nm : Name G => biBound (Dt.piece nm)) (le_max_left _ _)
    (fun nm => le_trans
      (Finset.le_sup (f := fun nm : Name G => (Dt.piece nm).natDegree) (Finset.mem_univ nm))
      (le_max_right _ _))
    (fun nm i => le_trans (natDegree_coeff_le_biBound _ i)
      (Finset.le_sup (f := fun nm : Name G => biBound (Dt.piece nm)) (Finset.mem_univ nm)))

end Rigidity.RET

end
