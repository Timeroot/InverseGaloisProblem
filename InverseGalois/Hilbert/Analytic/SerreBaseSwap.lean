import Mathlib
import InverseGalois.Hilbert.Analytic.SerreBaseCover
import InverseGalois.Hilbert.Analytic.MorseSwap

/-!
# A transposition and full symmetric geometric monodromy for the Serre base cover

This file is the exact analogue of `MorseSwap.lean` for the Serre base family
`serreBaseGeomPoly n = serreBaseP n − T` over `ℚ̄(T)`, where
`serreBaseP n = Xⁿ − C(n/(n−1))·X^{n−1}`.  It produces a transposition in the geometric
Galois group and, via Jordan's theorem (fed the preprimitivity proved in `SerreBaseCover`),
the surjectivity of the permutation representation onto `Sₙ`.

The main mathematical difference from the Morse case is the fibre/ramification analysis:
`serreBaseP` has its relevant double root at `X = 1` (the critical value `t₀ = serreBaseP(1)`),
and the Morse (at-most-one-collision) count only holds modulo primes lying over the branch
ideal `(T − t₀)` (the fibre over `t = 0` degenerates), so `serre_ncard_bound` is stated for
`P.LiesOver (branchIdeal n)` and `exists_nontrivial_inertia` returns such a `P`.
-/

open Polynomial
open scoped Classical
noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace SerreBaseSwap

open SerreBaseCover

abbrev Abase := Polynomial (AlgebraicClosure ℚ)

local instance splitsFact (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

variable (n : ℕ) [hn3 : Fact (3 ≤ n)]

abbrev Lfield := (serreBaseGeomPoly n).SplittingField
abbrev Bring := integralClosure Abase (Lfield n)

instance : IsGalois GeomBase (Lfield n) :=
  IsGalois.of_separable_splitting_field (serreBaseGeomPoly_separable n (by
    have := hn3.out
    omega))

instance : IsFractionRing (Bring n) (Lfield n) :=
  IsIntegralClosure.isFractionRing_of_finite_extension Abase GeomBase (Lfield n) (Bring n)

instance : Module.Finite Abase (Bring n) :=
  IsIntegralClosure.finite Abase GeomBase (Lfield n) (Bring n)

instance : IsDedekindDomain (Bring n) :=
  integralClosure.isDedekindDomain Abase GeomBase (Lfield n)

instance : Algebra.IsIntegral Abase (Bring n) :=
  IsIntegralClosure.isIntegral_algebra Abase (Lfield n)

instance sccGeom : SMulCommClass (serreBaseGeomPoly n).Gal GeomBase (Lfield n) :=
  ⟨fun g a x ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    rw [AlgEquiv.smul_def]
    exact AlgEquiv.commutes g a⟩

instance sccA : SMulCommClass (serreBaseGeomPoly n).Gal Abase (Lfield n) :=
  ⟨fun g a x ↦ by
    have h1 : g • (algebraMap Abase (Lfield n) a) = algebraMap Abase (Lfield n) a := by
      rw [IsScalarTower.algebraMap_apply Abase GeomBase (Lfield n)]
      exact smul_algebraMap g (algebraMap Abase GeomBase a)
    calc g • (a • x) = g • ((algebraMap Abase (Lfield n) a) * x) := by rw [Algebra.smul_def]
      _ = (g • algebraMap Abase (Lfield n) a) * (g • x) := by rw [smul_mul']
      _ = (algebraMap Abase (Lfield n) a) * (g • x) := by rw [h1]
      _ = a • (g • x) := by rw [Algebra.smul_def]⟩

instance iggL : IsGaloisGroup (serreBaseGeomPoly n).Gal GeomBase (Lfield n) :=
  IsGaloisGroup.of_mulEquiv (G := Lfield n ≃ₐ[GeomBase] Lfield n)
    ({ toFun := id, invFun := id, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
       map_mul' := fun _ _ ↦ rfl } : (serreBaseGeomPoly n).Gal ≃* (Lfield n ≃ₐ[GeomBase] Lfield n))
    (fun _ _ ↦ rfl)

instance iggB : IsGaloisGroup (serreBaseGeomPoly n).Gal Abase (Bring n) :=
  IsGaloisGroup.of_isFractionRing (serreBaseGeomPoly n).Gal Abase (Bring n) GeomBase (Lfield n)

/-! ## Bridging `serreBaseGeomPoly` and `serreBaseC` -/

theorem serreBaseGeomPoly_eq_map :
    serreBaseGeomPoly n = (serreBaseC n).map (algebraMap Abase GeomBase) := rfl

/-- Evaluating `serreBaseGeomPoly` and `serreBaseC` at a common point of a tower-algebra agree.
Stated for a generic carrier `L` to avoid `motive is not type correct` when `L = Lfield n`. -/
lemma aeval_geom_eq_serreBaseC {L : Type*} [CommRing L] [Algebra GeomBase L] [Algebra Abase L]
    [IsScalarTower Abase GeomBase L] (z : L) :
    (aeval z) (serreBaseGeomPoly n) = (aeval z) (serreBaseC n) := by
  rw [serreBaseGeomPoly_eq_map, aeval_map_algebraMap]

/-! ## The equivariant bijection between roots in `B` and roots in `L` -/

lemma rootMap_mem (x : (serreBaseC n).rootSet (Bring n)) :
    ((x : Bring n) : Lfield n) ∈ (serreBaseGeomPoly n).rootSet (Lfield n) := by
  have h2 : 2 ≤ n := by
    have := hn3.out
    omega
  have h_root : aeval (x.val : (Lfield n)) (serreBaseC n) = 0 := by
    convert aeval_eq_zero_of_mem_rootSet x.2 using 1
    rw [← Subtype.coe_inj]
    aesop
  rw [mem_rootSet']
  refine ⟨((serreBaseGeomPoly_monic n h2).map _).ne_zero, ?_⟩
  rwa [aeval_geom_eq_serreBaseC]

/-- The inclusion `B ↪ L` on roots. -/
def rootMap (x : (serreBaseC n).rootSet (Bring n)) : (serreBaseGeomPoly n).rootSet (Lfield n) :=
  ⟨((x : Bring n) : Lfield n), rootMap_mem n x⟩

lemma rootMap_bijective : Function.Bijective (rootMap n) := by
  have h2 : 2 ≤ n := by
    have := hn3.out
    omega
  constructor
  · intro x y hxy
    simpa [rootMap] using hxy
  · intro y
    have hy0 : aeval (y.val : Lfield n) (serreBaseC n) = 0 := by
      rw [← aeval_geom_eq_serreBaseC]
      exact aeval_eq_zero_of_mem_rootSet y.2
    have hy_integral : IsIntegral Abase (y.val : Lfield n) :=
      ⟨serreBaseC n, serreBaseC_monic n h2, hy0⟩
    set b : Bring n := ⟨y.val, hy_integral⟩ with hb
    have key : (algebraMap (Bring n) (Lfield n)) (aeval b (serreBaseC n)) = 0 := by
      rw [← IsScalarTower.coe_toAlgHom' Abase (Bring n) (Lfield n),
        ← aeval_algHom_apply]
      show aeval (y.val : Lfield n) (serreBaseC n) = 0
      exact hy0
    rw [← map_zero (algebraMap (Bring n) (Lfield n))] at key
    have hbmem : b ∈ (serreBaseC n).rootSet (Bring n) := by
      rw [mem_rootSet']
      exact ⟨((serreBaseC_monic n h2).map _).ne_zero,
        IsIntegralClosure.algebraMap_injective (Bring n) Abase (Lfield n) key⟩
    refine ⟨⟨b, hbmem⟩, ?_⟩
    apply Subtype.ext
    simp [rootMap, hb]

/-- The inclusion `B ↪ L` restricts to a bijection on root sets. -/
def rootEquiv : (serreBaseC n).rootSet (Bring n) ≃ (serreBaseGeomPoly n).rootSet (Lfield n) :=
  Equiv.ofBijective (rootMap n) (rootMap_bijective n)

@[simp] lemma rootEquiv_apply (x : (serreBaseC n).rootSet (Bring n)) :
    ((rootEquiv n x : (serreBaseGeomPoly n).rootSet (Lfield n)) : Lfield n)
      = ((x : Bring n) : Lfield n) :=
  rfl

lemma gal_smul_coe (g : (serreBaseGeomPoly n).Gal) (y : (serreBaseGeomPoly n).rootSet (Lfield n)) :
    ((galActionAux_perm (serreBaseGeomPoly n) g y : (serreBaseGeomPoly n).rootSet (Lfield n))
        : Lfield n)
      = g ((y : Lfield n)) :=
  galActionAux_perm_val (serreBaseGeomPoly n) g y

lemma rootEquiv_smul (g : (serreBaseGeomPoly n).Gal) (x : (serreBaseC n).rootSet (Bring n)) :
    rootEquiv n (g • x) = galActionAux_perm (serreBaseGeomPoly n) g (rootEquiv n x) := by
  apply Subtype.ext
  rw [gal_smul_coe, rootEquiv_apply, rootSet.coe_smul, integralClosure.coe_smul, rootEquiv_apply,
    AlgEquiv.smul_def]

lemma galActionAux_perm_eq (g : (serreBaseGeomPoly n).Gal) :
    galActionAux_perm (serreBaseGeomPoly n) g
      = (Equiv.permCongr (rootEquiv n)) (MulAction.toPermHom (serreBaseGeomPoly n).Gal
          ((serreBaseC n).rootSet (Bring n)) g) := by
  ext y
  obtain ⟨x, rfl⟩ := (rootEquiv n).surjective y
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, MulAction.toPermHom_apply,
    MulAction.toPerm_apply]
  rw [rootEquiv_smul]

lemma galActionHom_eq_permCongr (g : (serreBaseGeomPoly n).Gal) :
    Gal.galActionHom (serreBaseGeomPoly n) (Lfield n) g
      = (Equiv.permCongr ((rootEquiv n).trans
            (Gal.rootsEquivRoots (serreBaseGeomPoly n) (Lfield n))))
          (MulAction.toPermHom (serreBaseGeomPoly n).Gal
          ((serreBaseC n).rootSet (Bring n)) g) := by
  rw [_root_.galActionHom_eq_permCongr (serreBaseGeomPoly n) (Lfield n) g, galActionAux_perm_eq n g]
  ext x
  simp [Equiv.permCongr_apply]

/-! ## The polynomial splits in `B` -/

lemma serreBaseC_splits_B : ((serreBaseC n).map (algebraMap Abase (Bring n))).Splits := by
  have h2 : 2 ≤ n := by
    have := hn3.out
    omega
  have hmapL : (serreBaseC n).map (algebraMap Abase (Lfield n))
      = (serreBaseGeomPoly n).map (algebraMap GeomBase (Lfield n)) := by
    show (serreBaseC n).map (algebraMap Abase (Lfield n))
      = ((serreBaseC n).map (algebraMap Abase GeomBase)).map (algebraMap GeomBase (Lfield n))
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  obtain ⟨s, hs⟩ : ∃ s : Multiset (↥(Bring n)),
      (serreBaseC n).map (algebraMap Abase (↥(Bring n)))
        = Multiset.prod (Multiset.map (fun r : ↥(Bring n) ↦ X - C r) s) := by
    have h_range : ∀ r ∈ (serreBaseC n).rootSet (Lfield n),
        r ∈ Set.range (algebraMap (Bring n) (Lfield n)) := by
      intro r hr
      rw [mem_rootSet'] at hr
      exact ⟨⟨r, ⟨serreBaseC n, serreBaseC_monic n h2, hr.2⟩⟩, rfl⟩
    have h_prod : (serreBaseC n).map (algebraMap Abase (Lfield n))
        = Multiset.prod (Multiset.map (fun r : Lfield n ↦ X - C r)
            (Polynomial.roots (serreBaseC n |> Polynomial.map (algebraMap Abase (Lfield n))))) := by
      convert Splits.eq_prod_roots_of_monic _ _
      · rw [hmapL]
        exact Polynomial.IsSplittingField.splits (Lfield n) (serreBaseGeomPoly n)
      · exact Monic.map _ (serreBaseC_monic n h2)
    have h_prod_range : ∀ r ∈ Polynomial.roots
        (serreBaseC n |> Polynomial.map (algebraMap Abase (Lfield n))),
        r ∈ Set.range (algebraMap (Bring n) (Lfield n)) := by
      convert h_range using 1
      simp [rootSet_def]
    choose! f hf using h_prod_range
    obtain ⟨t, ht⟩ : ∃ t : Multiset (↥(Bring n)),
        Multiset.map (algebraMap (Bring n) (Lfield n)) t
          = Polynomial.roots (serreBaseC n |> Polynomial.map (algebraMap Abase (Lfield n))) := by
      use Multiset.map f (Polynomial.roots
        (serreBaseC n |> Polynomial.map (algebraMap Abase (Lfield n))))
      rw [Multiset.map_map]
      rw [Multiset.map_congr rfl]
      exacts [Multiset.map_id _, hf]
    use t
    refine Polynomial.map_injective (algebraMap (Bring n) (Lfield n))
      (IsIntegralClosure.algebraMap_injective (Bring n) (Abase) (Lfield n)) ?_
    convert h_prod using 1
    · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    · simp [← ht, Polynomial.map_multiset_prod]
  rw [hs, Splits]
  apply Submonoid.multiset_prod_mem
  simp at *
  rintro a x hx hx' rfl
  refine Submonoid.subset_closure (Or.inr ⟨-x, ?_⟩)
  aesop

/-! ## Pretransitivity and faithfulness on `B`-roots -/

instance pretransitive_B :
    MulAction.IsPretransitive (serreBaseGeomPoly n).Gal ((serreBaseC n).rootSet (Bring n)) := by
  refine ⟨fun x y ↦ ?_⟩
  set e := (rootEquiv n).trans (Gal.rootsEquivRoots (serreBaseGeomPoly n) (Lfield n))
  obtain ⟨g, hg⟩ := (Gal.galAction_isPretransitive (serreBaseGeomPoly n) (Lfield n)
      (serreBaseGeomPoly_irreducible n (by
        have := hn3.out
        omega))).exists_smul_eq (e x) (e y)
  refine ⟨g, ?_⟩
  have hgh : Gal.galActionHom (serreBaseGeomPoly n) (Lfield n) g (e x) = e y := hg
  rw [galActionHom_eq_permCongr n g, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    MulAction.toPermHom_apply, MulAction.toPerm_apply] at hgh
  exact e.injective hgh

lemma toPermHom_B_injective :
    Function.Injective (MulAction.toPermHom (serreBaseGeomPoly n).Gal
      ((serreBaseC n).rootSet (Bring n))) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  ext
  simp_all [Equiv.Perm.ext_iff, MulAction.toPermHom_apply]
  rename_i a ha
  have h_root : ∃ r : (serreBaseC n).rootSet (Bring n), (r : Lfield n) = a := by
    convert rootMap_bijective n |>.surjective ⟨a, ha⟩ using 1
    ext
    simp [rootMap]
  obtain ⟨r, rfl⟩ := h_root
  specialize hx _ _ r.2
  simpa [Subtype.ext_iff] using hx

/-! ## The Morse (at-most-one-collision) condition, fibre analysis -/

/-- The critical value `t₀ = serreBaseP(1)`. -/
def critT : AlgebraicClosure ℚ := (serreBaseP n).eval 1

theorem critT_eval (_hn : 2 ≤ n) :
    critT n = 1 - (n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1) := by
  unfold critT serreBaseP
  simp

theorem critT_ne_zero (hn : 2 ≤ n) : critT n ≠ 0 := by
  rw [critT_eval n hn, sub_ne_zero]
  have hd : (n : AlgebraicClosure ℚ) - 1 ≠ 0 := by
    have hne : (n : AlgebraicClosure ℚ) ≠ 1 := by exact_mod_cast (by omega : (n : ℕ) ≠ 1)
    exact sub_ne_zero.mpr hne
  intro h
  have h2 : (1 : AlgebraicClosure ℚ) * ((n : AlgebraicClosure ℚ) - 1) = (n : AlgebraicClosure ℚ) :=
    (eq_div_iff hd).mp h
  rw [one_mul] at h2
  have : (-1 : AlgebraicClosure ℚ) = 0 := by linear_combination h2
  norm_num at this

theorem serreBaseP_derivative (hn : 2 ≤ n) :
    derivative (serreBaseP n)
      = C (n : AlgebraicClosure ℚ) * X ^ (n - 2) * (X - 1) := by
  rw [serreBaseP_factor n hn, derivative_mul, derivative_X_pow, derivative_sub, derivative_X,
    derivative_C, sub_zero, mul_one]
  have he1 : n - 1 - 1 = n - 2 := by omega
  have he2 : (X : (AlgebraicClosure ℚ)[X]) ^ (n - 1) = X ^ (n - 2) * X := by
    rw [← pow_succ]
    congr 1
    omega
  have hcast : (C ((n - 1 : ℕ) : AlgebraicClosure ℚ) : (AlgebraicClosure ℚ)[X])
      = C ((n : AlgebraicClosure ℚ) - 1) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [he1, he2, hcast]
  have hd : (n : AlgebraicClosure ℚ) - 1 ≠ 0 := by
    have hne : (n : AlgebraicClosure ℚ) ≠ 1 := by exact_mod_cast (by omega : (n : ℕ) ≠ 1)
    exact sub_ne_zero.mpr hne
  have hkey : C ((n : AlgebraicClosure ℚ) - 1)
      * C ((n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1))
      = C (n : AlgebraicClosure ℚ) := by
    rw [← map_mul]
    congr 1
    field_simp
  have hA : C ((n : AlgebraicClosure ℚ) - 1) + 1 = C (n : AlgebraicClosure ℚ) := by
    rw [show (1 : (AlgebraicClosure ℚ)[X]) = C 1 from (map_one C).symm, ← map_add]
    congr 1
    ring
  linear_combination (X ^ (n - 2) * X) * hA - X ^ (n - 2) * hkey

theorem serreBaseP_derivative_eval (hn : 2 ≤ n) (a : AlgebraicClosure ℚ) :
    (derivative (serreBaseP n)).eval a = (n : AlgebraicClosure ℚ) * a ^ (n - 2) * (a - 1) := by
  rw [serreBaseP_derivative n hn]
  simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]

theorem serreBaseP_deriv_root (hn : 3 ≤ n) {a : AlgebraicClosure ℚ}
    (h : (derivative (serreBaseP n)).IsRoot a) : a = 0 ∨ a = 1 := by
  have h2 : 2 ≤ n := by omega
  rw [IsRoot.def, serreBaseP_derivative_eval n h2] at h
  have hn0 : (n : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' hn0
    · left
      exact (pow_eq_zero_iff (by omega : n - 2 ≠ 0)).mp h''
  · right
    rwa [sub_eq_zero] at h'

theorem serreBaseP_deriv2_eval_one (hn : 3 ≤ n) :
    (derivative (derivative (serreBaseP n))).eval 1 = (n : AlgebraicClosure ℚ) := by
  have h2 : 2 ≤ n := by omega
  rw [serreBaseP_derivative n h2]
  have hf : C (n : AlgebraicClosure ℚ) * X ^ (n - 2) * (X - 1)
      = C (n : AlgebraicClosure ℚ) * X ^ (n - 1) - C (n : AlgebraicClosure ℚ) * X ^ (n - 2) := by
    have he2 : (X : (AlgebraicClosure ℚ)[X]) ^ (n - 1) = X ^ (n - 2) * X := by
      rw [← pow_succ]
      congr 1
      omega
    rw [he2]
    ring
  rw [hf, derivative_sub, derivative_C_mul, derivative_C_mul, derivative_X_pow, derivative_X_pow]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  have hc1 : ((n - 1 : ℕ) : AlgebraicClosure ℚ) = (n : AlgebraicClosure ℚ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hc2 : ((n - 2 : ℕ) : AlgebraicClosure ℚ) = (n : AlgebraicClosure ℚ) - 2 := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  rw [hc1, hc2]
  ring

theorem fiber_eval_zero_ne (hn : 2 ≤ n) :
    (serreBaseP n - C (critT n)).eval 0 ≠ 0 := by
  rw [eval_sub, eval_C]
  have h0 : (serreBaseP n).eval 0 = 0 := by
    rw [serreBaseP_factor n hn, eval_mul, eval_pow, eval_X, zero_pow (by omega : n - 1 ≠ 0),
      zero_mul]
  rw [h0, zero_sub, neg_ne_zero]
  exact critT_ne_zero n hn

theorem fiber_deriv_root (hn : 3 ≤ n) {a : AlgebraicClosure ℚ}
    (h : (derivative (serreBaseP n - C (critT n))).IsRoot a) : a = 0 ∨ a = 1 := by
  rw [derivative_sub, derivative_C, sub_zero] at h
  exact serreBaseP_deriv_root n hn h

theorem fiber_common_root_unique (hn : 3 ≤ n) {a b : AlgebraicClosure ℚ}
    (ha : (serreBaseP n - C (critT n)).IsRoot a)
    (ha' : (derivative (serreBaseP n - C (critT n))).IsRoot a)
    (hb : (serreBaseP n - C (critT n)).IsRoot b)
    (hb' : (derivative (serreBaseP n - C (critT n))).IsRoot b) : a = b := by
  have h2 : 2 ≤ n := by omega
  have hone : ∀ z, (serreBaseP n - C (critT n)).IsRoot z →
      (derivative (serreBaseP n - C (critT n))).IsRoot z → z = 1 := fun z hz hz' ↦
    (fiber_deriv_root n hn hz').resolve_left (by
      rintro rfl
      exact fiber_eval_zero_ne n h2 hz)
  rw [hone a ha ha', hone b hb hb']

theorem fiber_rootMultiplicity_le_two (hn : 3 ≤ n) (a : AlgebraicClosure ℚ) :
    (serreBaseP n - C (critT n)).rootMultiplicity a ≤ 2 := by
  have h2 : 2 ≤ n := by omega
  by_contra hc
  have hmul : 2 < (serreBaseP n - C (critT n)).rootMultiplicity a := not_le.mp hc
  have key0 : (serreBaseP n - C (critT n)).IsRoot a :=
    isRoot_iterate_derivative_of_lt_rootMultiplicity
      (by omega : 0 < (serreBaseP n - C (critT n)).rootMultiplicity a)
  have key1 : (derivative (serreBaseP n - C (critT n))).IsRoot a :=
    isRoot_iterate_derivative_of_lt_rootMultiplicity
      (by omega : 1 < (serreBaseP n - C (critT n)).rootMultiplicity a)
  have key2 : (derivative (derivative (serreBaseP n - C (critT n)))).IsRoot a :=
    isRoot_iterate_derivative_of_lt_rootMultiplicity hmul
  have haa : a = 1 := (fiber_deriv_root n hn key1).resolve_left
    (by
      rintro rfl
      exact fiber_eval_zero_ne n h2 key0)
  rw [haa] at key2
  simp only [IsRoot.def] at key2
  have hderiv : derivative (serreBaseP n - C (critT n)) = derivative (serreBaseP n) := by
    rw [derivative_sub, derivative_C, sub_zero]
  rw [hderiv, serreBaseP_deriv2_eval_one n hn] at key2
  have hn0 : (n : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact absurd key2 hn0

theorem fiber_ncard_qbar (hn : 3 ≤ n) :
    (serreBaseP n - C (critT n)).roots.card
      ≤ (serreBaseP n - C (critT n)).roots.toFinset.card + 1 := by
  classical
  set p : (AlgebraicClosure ℚ)[X] := serreBaseP n - C (critT n) with hp
  have h_at_most_one_repeated :
      (p.roots.toFinset.filter (fun a ↦ p.rootMultiplicity a ≥ 2)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb ↦ ?_
    rw [Finset.mem_filter, Multiset.mem_toFinset] at ha hb
    apply fiber_common_root_unique n hn
    · exact isRoot_of_mem_roots ha.1
    · exact isRoot_iterate_derivative_of_lt_rootMultiplicity ha.2
    · exact isRoot_of_mem_roots hb.1
    · exact isRoot_iterate_derivative_of_lt_rootMultiplicity hb.2
  have h_sum_le_one :
      ∑ a ∈ p.roots.toFinset, (p.rootMultiplicity a - 1)
        ≤ (p.roots.toFinset.filter (fun a ↦ p.rootMultiplicity a ≥ 2)).card := by
    rw [Finset.card_filter]
    gcongr with a ha
    split_ifs with hge
    · have h := fiber_rootMultiplicity_le_two n hn a
      rw [← hp] at h
      omega
    · omega
  have h_sum_eq_card :
      ∑ a ∈ p.roots.toFinset, p.rootMultiplicity a = Multiset.card p.roots := by
    rw [← Multiset.toFinset_sum_count_eq]
    simp
  have h_sum_eq_card2 :
      ∑ a ∈ p.roots.toFinset, (p.rootMultiplicity a - 1)
          + ∑ a ∈ p.roots.toFinset, 1 = Multiset.card p.roots := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun x hx ↦
        tsub_add_cancel_of_le <| Nat.succ_le_of_lt <| Nat.pos_of_ne_zero <| by aesop]
    aesop
  norm_num at *
  linarith

theorem fiber_ncard_field (hn : 3 ≤ n) {F : Type*} [CommRing F] [IsDomain F]
    (φ : (AlgebraicClosure ℚ) →+* F) :
    ((serreBaseP n - C (critT n)).map φ).roots.card
      ≤ ((serreBaseP n - C (critT n)).map φ).roots.toFinset.card + 1 := by
  classical
  have hsplit : (serreBaseP n - C (critT n)).Splits := IsAlgClosed.splits _
  have hmap : ((serreBaseP n - C (critT n)).map φ).roots
      = (serreBaseP n - C (critT n)).roots.map φ := hsplit.roots_map_of_injective φ.injective
  rw [hmap, Multiset.card_map, Multiset.toFinset_map, Finset.card_image_of_injective _ φ.injective]
  exact fiber_ncard_qbar n hn

/-- The branch-point maximal ideal `(T − t₀)` of `A = ℚ̄[T]`. -/
def branchIdeal : Ideal Abase := Ideal.span {X - C (critT n)}

instance : (branchIdeal n).IsMaximal := by
  convert PrincipalIdealRing.isMaximal_of_irreducible _
  · infer_instance
  · exact irreducible_X_sub_C _

lemma branchIdeal_ne_bot : branchIdeal n ≠ ⊥ := by
  unfold branchIdeal
  rw [Ne.eq_def, Ideal.span_singleton_eq_bot]
  exact X_sub_C_ne_zero _

/-- Abstract collision bound.  For any `Abase`-algebra domain `S` and maximal ideal `P` of `S`
whose residue field identifies `T` with the branch value `t₀` (`hψX`), the roots of `serreBaseC`
in `S` collide at most once modulo `P`.  Keeping `S` generic lets the (expensive) typeclass
search in `SelmerMorse.ncard_rootSet_le_roots_card` resolve once, avoiding a `whnf` blow-up when
specialised to `B = integralClosure Abase L`. -/
theorem serre_ncard_bound_abstract {S : Type*} [CommRing S] [IsDomain S] [Algebra Abase S]
    (hn : 3 ≤ n) (P : Ideal S) [P.IsMaximal]
    (hψX : algebraMap Abase (S ⧸ P) (X : Abase)
      = algebraMap Abase (S ⧸ P) (C (critT n))) :
    ((serreBaseC n).rootSet S).ncard
      ≤ ((serreBaseC n).rootSet (S ⧸ P)).ncard + 1 := by
  classical
  have h2 : 2 ≤ n := by omega
  have hmapeq : (serreBaseC n).map (algebraMap Abase (S ⧸ P))
      = (serreBaseP n - C (critT n)).map ((algebraMap Abase (S ⧸ P)).comp C) := by
    simp only [serreBaseC, linearCoverC, Polynomial.map_sub, Polynomial.map_map, Polynomial.map_C,
      RingHom.comp_apply, hψX]
  have hfibmonic : (serreBaseP n - C (critT n)).Monic := by
    apply (serreBaseP_monic n h2).sub_of_left
    calc (C (critT n) : (AlgebraicClosure ℚ)[X]).degree ≤ 0 := degree_C_le
      _ < (serreBaseP n).degree := by
          rw [degree_eq_natDegree (serreBaseP_monic n h2).ne_zero,
            serreBaseP_natDegree n h2]
          exact_mod_cast (by omega : (0 : ℕ) < n)
  have hne : (serreBaseC n).map (algebraMap Abase (S ⧸ P)) ≠ 0 := by
    rw [hmapeq]
    exact (hfibmonic.map _).ne_zero
  calc ((serreBaseC n).rootSet S).ncard
      ≤ ((serreBaseC n).map (algebraMap Abase (S ⧸ P))).roots.card :=
        SelmerMorse.ncard_rootSet_le_roots_card (serreBaseC n) hne
    _ = ((serreBaseP n - C (critT n)).map
          ((algebraMap Abase (S ⧸ P)).comp C)).roots.card := by rw [hmapeq]
    _ ≤ ((serreBaseP n - C (critT n)).map
          ((algebraMap Abase (S ⧸ P)).comp C)).roots.toFinset.card + 1 :=
        fiber_ncard_field (F := S ⧸ P) n hn ((algebraMap Abase (S ⧸ P)).comp C)
    _ = ((serreBaseC n).rootSet (S ⧸ P)).ncard + 1 := by
        rw [rootSet_def, Set.ncard_coe_finset, aroots_def, hmapeq]

/-- For any maximal ideal `P` of `B` lying over the branch ideal, the roots of `serreBaseC`
collide at most once modulo `P`. -/
lemma serre_ncard_bound (hn : 3 ≤ n) (P : Ideal (Bring n)) [P.IsMaximal]
    [P.LiesOver (branchIdeal n)] :
    ((serreBaseC n).rootSet (Bring n)).ncard
      ≤ ((serreBaseC n).rootSet (Bring n ⧸ P)).ncard + 1 := by
  have hmemP : algebraMap Abase (Bring n) (X - C (critT n)) ∈ P :=
    (Ideal.mem_of_liesOver (P := P) (p := branchIdeal n) (X - C (critT n))).mp
      (Ideal.mem_span_singleton_self _)
  have hψX : algebraMap Abase (Bring n ⧸ P) (X : Abase)
      = algebraMap Abase (Bring n ⧸ P) (C (critT n)) := by
    rw [← sub_eq_zero, ← map_sub, IsScalarTower.algebraMap_apply Abase (Bring n) (Bring n ⧸ P),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hmemP
  exact serre_ncard_bound_abstract n hn P hψX

/-! ## Existence of a ramified branch point (nontrivial inertia) -/

lemma inertia_of_ramified
    (Smid : Type) [CommRing Smid] [IsDomain Smid] [IsDedekindDomain Smid]
    [Algebra Abase Smid] [Algebra Smid (Bring n)] [IsScalarTower Abase Smid (Bring n)]
    [Module.IsTorsionFree Abase Smid] [Algebra.IsIntegral Smid (Bring n)]
    [Module.Finite Smid (Bring n)] [Module.IsTorsionFree Smid (Bring n)]
    [Module.IsTorsionFree Abase (Bring n)]
    (p : Ideal Abase) [p.IsMaximal] (hp : p ≠ ⊥)
    (hinj : Function.Injective (algebraMap Abase (Bring n)))
    (PS : Ideal Smid) [PS.IsPrime] [PS.LiesOver p]
    (hPS : 2 ≤ Ideal.ramificationIdx (algebraMap Abase Smid) p PS)
    (hmapSB : Ideal.map (algebraMap Smid (Bring n)) PS ≠ ⊥)
    (hmapAB : Ideal.map (algebraMap Abase (Bring n)) p ≠ ⊥)
    (hsep : ∀ (Q : Ideal (Bring n)) [Q.LiesOver p] [Q.IsMaximal],
        Algebra.IsSeparable (Abase ⧸ p) ((Bring n) ⧸ Q)) :
    ∃ (P : Ideal (Bring n)), P.IsMaximal ∧ P.LiesOver p ∧
      ∃ g : (serreBaseGeomPoly n).Gal, g ∈ P.inertia (serreBaseGeomPoly n).Gal ∧ g ≠ 1 := by
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ := PS.nonempty_primesOver (S := Bring n)
  have hQlo_p : Q.LiesOver p := Ideal.LiesOver.trans Q PS p
  have hle : Ideal.map (algebraMap Smid (Bring n)) PS ≤ Q :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.LiesOver.over (P := Q) (p := PS)))
  have htower := Ideal.ramificationIdx_algebra_tower (R := Abase) (S := Smid) (T := Bring n)
    (p := p) (P := PS) (Q := Q) hmapSB hmapAB hle
  have hQbot : Q ≠ ⊥ := by
    intro h
    apply hp
    have hpu := Ideal.LiesOver.over (P := Q) (p := p)
    rw [hpu, h, Ideal.under, Ideal.comap_bot_of_injective _ hinj]
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal hQprime hQbot
  have heQPS : Ideal.ramificationIdx (algebraMap Smid (Bring n)) PS Q ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmapSB hQprime hle
  have h2 : 2 ≤ Ideal.ramificationIdx (algebraMap Abase (Bring n)) p Q := by
    rw [htower]
    calc 2 = 2 * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul hPS (Nat.one_le_iff_ne_zero.mpr heQPS)
  have hIn : p.ramificationIdxIn (Bring n) =
      Ideal.ramificationIdx (algebraMap Abase (Bring n)) p Q :=
    Ideal.ramificationIdxIn_eq_ramificationIdx p Q (serreBaseGeomPoly n).Gal
  have := hsep Q
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := (serreBaseGeomPoly n).Gal) p hp Q
  have h2card : 2 ≤ Nat.card (Ideal.inertia (serreBaseGeomPoly n).Gal Q) := by
    rwa [hcard, hIn]
  have hNT : Nontrivial (Ideal.inertia (serreBaseGeomPoly n).Gal Q) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨g, hg⟩ := exists_ne (1 : Ideal.inertia (serreBaseGeomPoly n).Gal Q)
  refine ⟨Q, inferInstance, hQlo_p, g, g.2, ?_⟩
  simpa using hg

/-! ### The concrete intermediate ring `A[x] = ℚ̄[x] ⊆ B` -/

lemma exists_rootB : ∃ x : Bring n, (aeval x) (serreBaseC n) = 0 := by
  have h2 : 2 ≤ n := by
    have := hn3.out
    omega
  have hcard := serreBaseGeomPoly_card_rootSet n h2
  have hne : Nonempty ((serreBaseGeomPoly n).rootSet (Lfield n)) :=
    Fintype.card_pos_iff.mp (by
      rw [hcard]
      omega)
  obtain ⟨r⟩ := hne
  obtain ⟨s, _⟩ := (rootMap_bijective n).2 r
  exact ⟨s, aeval_eq_zero_of_mem_rootSet s.2⟩

/-- A chosen root of `serreBaseC n` in `B`. -/
def rootB : Bring n := (exists_rootB n).choose

lemma rootB_spec : (aeval (rootB n)) (serreBaseC n) = 0 := (exists_rootB n).choose_spec

/-- The intermediate ring `A[x] = ℚ̄[x] ⊆ B`. -/
abbrev Smid : Type := ↑(Algebra.adjoin Abase ({rootB n} : Set (Bring n)))

/-- The generator `x` viewed inside the intermediate ring. -/
def xS : Smid n := ⟨rootB n, Algebra.subset_adjoin (Set.mem_singleton _)⟩

instance : Module.IsTorsionFree Abase (Bring n) := by
  constructor
  intro r hr x hx h
  replace h := congr_arg Subtype.val h
  simp_all [Algebra.smul_def]
  refine h.resolve_right ?_
  simpa [IsScalarTower.algebraMap_apply Abase GeomBase (Lfield n)] using hr.left.ne_zero

instance : Module.IsTorsionFree Abase (Smid n) := by
  constructor
  intro r hr x y hxy
  replace hxy := congr_arg Subtype.val hxy
  simp_all [Algebra.smul_def]
  refine hxy.resolve_right ?_
  simpa using hr.left.ne_zero

instance : Module.IsTorsionFree (Smid n) (Bring n) := by
  refine ⟨fun x hx ↦ ?_⟩
  intro y z h_eq
  simp_all

instance : Module.Finite (Smid n) (Bring n) :=
  (inferInstance : Module.Finite Abase (Bring n)).of_restrictScalars_finite Abase (Smid n) (Bring n)

instance : Algebra.IsIntegral (Smid n) (Bring n) := by infer_instance

lemma algebraMap_Abase_Bring_injective : Function.Injective (algebraMap Abase (Bring n)) := by
  intro x y hxy
  simpa using hxy

lemma xS_conductor_top : conductor Abase (xS n) = ⊤ := by
  convert (conductor_eq_top_iff_adjoin_eq_top (R := Abase) (x := xS n)).mpr _ using 1
  rw [Algebra.eq_top_iff]
  intro y
  simp [xS]
  rcases y with ⟨y, hy⟩
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hy
  · exact fun x hx ↦ Algebra.subset_adjoin <| by aesop
  · exact Subalgebra.algebraMap_mem _
  · exact fun x y hx hy hx' hy' ↦ Subalgebra.add_mem _ hx' hy'
  · exact fun x y hx hy hx' hy' ↦ Subalgebra.mul_mem _ hx' hy'

lemma xS_minpoly : minpoly Abase (xS n) = serreBaseC n := by
  have h2 : 2 ≤ n := by
    have := hn3.out
    omega
  have h_minpoly_div : minpoly Abase (xS n) ∣ serreBaseC n := by
    refine minpoly.isIntegrallyClosed_dvd ?_ ?_
    · refine ⟨serreBaseC n, serreBaseC_monic n h2, ?_⟩
      convert rootB_spec n using 1
      simp [aeval_def, Polynomial.eval₂_eq_sum_range]
      rw [← Subtype.coe_inj]
      aesop
    · convert rootB_spec n using 1
      rw [← Subtype.coe_inj]
      simp [xS]
  have h_irreducible : Irreducible (serreBaseC n) := serreBaseC_irreducible n
  refine eq_of_monic_of_associated ?_ ?_ ?_
  · apply minpoly.monic
    refine ⟨serreBaseC n, serreBaseC_monic n h2, ?_⟩
    convert rootB_spec n using 1
    simp [xS, aeval_def, Polynomial.eval₂_eq_sum_range, ← Subtype.coe_inj]
  · exact serreBaseC_monic n h2
  · obtain ⟨q, hq⟩ := h_minpoly_div
    have := h_irreducible.2 hq
    exact this.elim (fun h ↦ False.elim <| minpoly.not_isUnit Abase (xS n) h)
      fun h ↦ associated_of_dvd_dvd (by aesop) (by aesop)

/-- The image of the base variable `T` in `A[x] = ℚ̄[x]`:
`T ↦ xⁿ − (n/(n−1))·x^{n−1}` (i.e. `serreBaseP` evaluated at `x`). -/
lemma algebraMap_Abase_Smid_X :
    algebraMap Abase (Smid n) (Polynomial.X)
      = (xS n) ^ n
        - (algebraMap Abase (Smid n)
            (C ((n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1)))) * (xS n) ^ (n - 1) := by
  have hφ := aeval_algHom_apply
    (Subalgebra.val (Algebra.adjoin Abase ({rootB n} : Set (Bring n)))) (xS n) (serreBaseC n)
  have hval : (Subalgebra.val (Algebra.adjoin Abase ({rootB n} : Set (Bring n)))) (xS n)
      = rootB n := rfl
  rw [hval] at hφ
  have hz : (Subalgebra.val (Algebra.adjoin Abase ({rootB n} : Set (Bring n))))
      ((aeval (xS n)) (serreBaseC n)) = 0 := by
    rw [← hφ]
    exact rootB_spec n
  have hxS0 : (aeval (xS n)) (serreBaseC n) = 0 := Subtype.val_injective hz
  have hexpand : (aeval (xS n)) (serreBaseC n)
      = (xS n) ^ n
        - (algebraMap Abase (Smid n)
            (C ((n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1)))) * (xS n) ^ (n - 1)
        - algebraMap Abase (Smid n) X := by
    rw [serreBaseC, linearCoverC, map_sub, aeval_C]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    simp only [serreBaseP, eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, RingHom.comp_apply]
  rw [hexpand] at hxS0
  linear_combination -hxS0

lemma Smid_eval_surjective :
    Function.Surjective
      (Polynomial.eval₂RingHom ((algebraMap Abase (Smid n)).comp Polynomial.C) (xS n)) := by
  intro y
  have h_span : ∀ y : Smid n, y ∈ Subalgebra.toSubmodule (Algebra.adjoin (Abase) {xS n}) := by
    intro y
    apply Algebra.eq_top_iff.mp (by
    convert (conductor_eq_top_iff_adjoin_eq_top (R := Abase) (x := xS n)).mp
      (xS_conductor_top n) using 1) y
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ (h_span y)
  · exact fun x hx ↦ ⟨X, by aesop⟩
  · intro r
    use Polynomial.comp r (serreBaseP n)
    have hkey : Polynomial.eval₂ ((algebraMap Abase (Smid n)).comp C) (xS n)
        (serreBaseP n) = algebraMap Abase (Smid n) X := by
      rw [algebraMap_Abase_Smid_X]
      simp only [serreBaseP, eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, RingHom.comp_apply]
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_comp, hkey]
    rw [Polynomial.eval₂_eq_sum_range]
    conv_rhs => rw [as_sum_range_C_mul_X_pow r]
    simp [map_sum, map_mul, map_pow]
  · rintro x y hx hy ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp⟩
  · rintro x y hx hy ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by simp⟩

instance : IsDedekindDomain (Smid n) := by
  have : IsPrincipalIdealRing (Smid n) :=
    IsPrincipalIdealRing.of_surjective _ (Smid_eval_surjective n)
  infer_instance

/-! ### The branch-point ideal and its ramification -/

theorem sq_dvd_fiber_serre (hn : 3 ≤ n) :
    (X - C (1 : AlgebraicClosure ℚ)) ^ 2 ∣ (serreBaseP n - C (critT n)) := by
  have h2 : 2 ≤ n := by omega
  obtain ⟨q, hq⟩ : ∃ q : (AlgebraicClosure ℚ)[X],
      (X - C (1 : AlgebraicClosure ℚ)) * q = serreBaseP n - C (critT n) := by
    refine ⟨(serreBaseP n - C (critT n)) /ₘ (X - C 1), ?_⟩
    have hroot : (serreBaseP n - C (critT n)).IsRoot 1 := by
      rw [IsRoot.def, eval_sub, eval_C]
      unfold critT
      ring
    rw [mul_divByMonic_eq_iff_isRoot.mpr hroot]
  convert mul_dvd_mul_left (X - C (1 : AlgebraicClosure ℚ))
    (dvd_iff_isRoot.mpr (show q.eval 1 = 0 from ?_)) using 1
  · ring
  · exact hq.symm
  · replace hq := congr_arg derivative hq
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero] at hq
    replace hq := congr_arg (eval 1) hq
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, one_mul, sub_self, zero_mul,
      add_zero] at hq
    rw [hq, derivative_sub, derivative_C, sub_zero, serreBaseP_derivative_eval n h2]
    ring

attribute [local instance] Ideal.Quotient.field

lemma branch_reduced_sq_dvd (hn : 3 ≤ n) :
    (X - C (Ideal.Quotient.mk (branchIdeal n) (Polynomial.C (1 : AlgebraicClosure ℚ)))) ^ 2 ∣
      (serreBaseC n).map (Ideal.Quotient.mk (branchIdeal n)) := by
  set ρ : (AlgebraicClosure ℚ) →+* (Abase ⧸ branchIdeal n) :=
    (Ideal.Quotient.mk (branchIdeal n)).comp C with hρ
  have hXeq : (Ideal.Quotient.mk (branchIdeal n)) X =
      (Ideal.Quotient.mk (branchIdeal n)) (C (critT n)) := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hmapeq : (serreBaseC n).map (Ideal.Quotient.mk (branchIdeal n))
      = (serreBaseP n - C (critT n)).map ρ := by
    simp only [serreBaseC, linearCoverC, Polynomial.map_sub, Polynomial.map_map, Polynomial.map_C,
      hXeq, hρ, RingHom.comp_apply]
  rw [hmapeq]
  have hdvd := sq_dvd_fiber_serre n hn
  have := Polynomial.map_dvd ρ hdvd
  simpa [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hρ,
    RingHom.comp_apply] using this

lemma branch_ramified (hn : 3 ≤ n) :
    ∃ PS : Ideal (Smid n), PS.IsPrime ∧ PS.LiesOver (branchIdeal n) ∧
      2 ≤ Ideal.ramificationIdx (algebraMap Abase (Smid n)) (branchIdeal n) PS ∧
      Ideal.map (algebraMap (Smid n) (Bring n)) PS ≠ ⊥ := by
  classical
  have h2 : 2 ≤ n := by omega
  have hsq := branch_reduced_sq_dvd n hn
  have hI' : branchIdeal n ≠ ⊥ := branchIdeal_ne_bot n
  have hxint : IsIntegral Abase (xS n) := ⟨serreBaseC n, serreBaseC_monic n h2, by
    rw [← xS_minpoly n]
    exact minpoly.aeval Abase (xS n)⟩
  have hx : (conductor Abase (xS n)).comap (algebraMap Abase (Smid n)) ⊔ (branchIdeal n) = ⊤ := by
    rw [xS_conductor_top]
    simp
  set d : (Abase ⧸ branchIdeal n)[X] :=
    X - C (Ideal.Quotient.mk (branchIdeal n) (C (1 : AlgebraicClosure ℚ))) with hd
  have hPne : (minpoly Abase (xS n)).map (Ideal.Quotient.mk (branchIdeal n)) ≠ 0 := by
    rw [xS_minpoly]
    exact (Monic.map _ (serreBaseC_monic n h2)).ne_zero
  have hd_irr : Irreducible d := irreducible_X_sub_C _
  have hd_norm : normalize d = d := (monic_X_sub_C _).normalize_eq_self
  have hcount2 : 2 ≤ Multiset.count d (UniqueFactorizationMonoid.normalizedFactors
      ((minpoly Abase (xS n)).map (Ideal.Quotient.mk (branchIdeal n)))) := by
    have hemult : (2 : ℕ∞) ≤ emultiplicity d
        ((minpoly Abase (xS n)).map (Ideal.Quotient.mk (branchIdeal n))) := by
      rw [xS_minpoly]
      exact pow_dvd_iff_le_emultiplicity.mp hsq
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hd_irr hPne, hd_norm]
      at hemult
    exact_mod_cast hemult
  have hd_mem : d ∈ UniqueFactorizationMonoid.normalizedFactors
      ((minpoly Abase (xS n)).map (Ideal.Quotient.mk (branchIdeal n))) :=
    Multiset.count_pos.mp (by omega)
  set equiv := KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    (inferInstance : (branchIdeal n).IsMaximal) hI' hx hxint with heq
  set PS := (equiv.symm ⟨d, hd_mem⟩ :
    {J // J ∈ UniqueFactorizationMonoid.normalizedFactors
      (Ideal.map (algebraMap Abase (Smid n)) (branchIdeal n))}) with hPS
  have hmem : PS.1 ∈ UniqueFactorizationMonoid.normalizedFactors
      (Ideal.map (algebraMap Abase (Smid n)) (branchIdeal n)) := PS.2
  have hmapI_ne : Ideal.map (algebraMap Abase (Smid n)) (branchIdeal n) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI'
  have hPS_ne : PS.1 ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hmem
  have hPS_prime : Prime PS.1 := UniqueFactorizationMonoid.prime_of_normalized_factor _ hmem
  have hPS_isPrime : PS.1.IsPrime := Ideal.isPrime_of_prime hPS_prime
  have hle : Ideal.map (algebraMap Abase (Smid n)) (branchIdeal n) ≤ PS.1 :=
    (Ideal.dvd_iff_le).mp (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem)
  have hcomap : Ideal.comap (algebraMap Abase (Smid n)) PS.1 = branchIdeal n := by
    have hIle : branchIdeal n ≤ Ideal.comap (algebraMap Abase (Smid n)) PS.1 :=
      Ideal.map_le_iff_le_comap.mp hle
    rcases (inferInstance : (branchIdeal n).IsMaximal).eq_of_le (by
      intro h
      exact hPS_isPrime.ne_top (Ideal.comap_eq_top_iff.mp h)) hIle with h
    exact h.symm
  have hLiesOver : PS.1.LiesOver (branchIdeal n) := ⟨hcomap.symm⟩
  refine ⟨PS.1, hPS_isPrime, hLiesOver, ?_, Ideal.map_ne_bot_of_ne_bot hPS_ne⟩
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hmapI_ne hPS_isPrime hPS_ne]
  have hkd := KummerDedekind.emultiplicity_factors_map_eq_emultiplicity
    (inferInstance : (branchIdeal n).IsMaximal) hI' hx hxint hmem
  have hequiv_eq : (↑(equiv ⟨PS.1, hmem⟩) : (Abase ⧸ branchIdeal n)[X]) = d := by
    have h1 : (⟨PS.1, hmem⟩ :
        {J // J ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.map (algebraMap Abase (Smid n)) (branchIdeal n))}) = PS := Subtype.ext rfl
    rw [h1, hPS, Equiv.apply_symm_apply]
  rw [hequiv_eq] at hkd
  have hPS_irr : Irreducible PS.1 :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hmem
  have hPS_normeq : normalize PS.1 = PS.1 :=
    UniqueFactorizationMonoid.normalize_normalized_factor _ hmem
  have hcount_eq : emultiplicity PS.1 (Ideal.map (algebraMap Abase (Smid n)) (branchIdeal n))
      = ((Multiset.count PS.1 (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.map (algebraMap Abase (Smid n)) (branchIdeal n)))) : ℕ∞) := by
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPS_irr hmapI_ne,
      hPS_normeq]
  have hd_emult : (2 : ℕ∞) ≤ emultiplicity d
      ((minpoly Abase (xS n)).map (Ideal.Quotient.mk (branchIdeal n))) := by
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hd_irr hPne, hd_norm]
    exact_mod_cast hcount2
  rw [← hkd, hcount_eq] at hd_emult
  exact_mod_cast hd_emult

lemma branch_residue_separable (Q : Ideal (Bring n)) [Q.LiesOver (branchIdeal n)] [Q.IsMaximal] :
    Algebra.IsSeparable (Abase ⧸ branchIdeal n) ((Bring n) ⧸ Q) := by
  have : CharZero (Abase ⧸ branchIdeal n) := algebraRat.charZero _
  have : Algebra.IsIntegral (Abase ⧸ branchIdeal n) ((Bring n) ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (branchIdeal n)
  have : Algebra.IsAlgebraic (Abase ⧸ branchIdeal n) ((Bring n) ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

lemma exists_nontrivial_inertia (hn : 3 ≤ n) :
    ∃ (P : Ideal (Bring n)), P.IsMaximal ∧ P.LiesOver (branchIdeal n) ∧
      ∃ g : (serreBaseGeomPoly n).Gal, g ∈ P.inertia (serreBaseGeomPoly n).Gal ∧ g ≠ 1 := by
  obtain ⟨PS, hPSprime, hPSover, hPSe, hPSmap⟩ := branch_ramified n hn
  exact inertia_of_ramified n (Smid n) (branchIdeal n) (branchIdeal_ne_bot n)
    (algebraMap_Abase_Bring_injective n) PS hPSe hPSmap
    (Ideal.map_ne_bot_of_ne_bot (branchIdeal_ne_bot n))
    (fun Q _ _ ↦ branch_residue_separable n Q)

/-! ## Assembling the transposition -/

theorem swap_input_final (hn : 3 ≤ n) :
    ∃ g : (serreBaseGeomPoly n).Gal,
      ((Gal.galActionHom (serreBaseGeomPoly n) (Lfield n)) g).IsSwap := by
  classical
  obtain ⟨P, hPmax, hPlo, g, hg_in, hg_ne⟩ := exists_nontrivial_inertia n hn
  have hmorse := Polynomial.Splits.toPermHom_apply_eq_one_or_isSwap_of_ncard_le_of_mem_inertia
    (R := Abase) (S := Bring n) (G := (serreBaseGeomPoly n).Gal) (f := serreBaseC n)
    (serreBaseC_splits_B n) P (serre_ncard_bound n hn P) g hg_in
  have hne1 : MulAction.toPermHom (serreBaseGeomPoly n).Gal
      ((serreBaseC n).rootSet (Bring n)) g ≠ 1 := by
    intro h
    refine hg_ne (toPermHom_B_injective n ?_)
    simpa using h
  have hswapB : (MulAction.toPermHom (serreBaseGeomPoly n).Gal
      ((serreBaseC n).rootSet (Bring n)) g).IsSwap := hmorse.resolve_left hne1
  refine ⟨g, ?_⟩
  rw [galActionHom_eq_permCongr n g]
  exact MorseSwap.isSwap_permCongr
    ((rootEquiv n).trans (Gal.rootsEquivRoots (serreBaseGeomPoly n) (Lfield n))) hswapB

end SerreBaseSwap

open SerreBaseCover

/-- The polynomial always splits in its own splitting field (top-level `local Fact` instance). -/
local instance splitsInSplittingFieldSerre'' (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

open scoped Classical in
/-- **A transposition in the geometric monodromy group** of the Serre base cover: the group
contains an element acting on the roots as a transposition. -/
theorem serreBaseGeomPoly_hasSwap (n : ℕ) (hn : 3 ≤ n) :
    ∃ g : (serreBaseGeomPoly n).Gal, Equiv.Perm.IsSwap
      ((Gal.galActionHom (serreBaseGeomPoly n) (serreBaseGeomPoly n).SplittingField) g) := by
  have : Fact (3 ≤ n) := ⟨hn⟩
  exact SerreBaseSwap.swap_input_final n hn

open scoped Classical in
/-- **The geometric-monodromy surjectivity for the Serre base cover**, via Jordan's theorem.
The permutation representation of the geometric Galois group of `serreBaseP n − T` over `ℚ̄(T)`
on the roots is surjective onto the full symmetric group. -/
theorem serreBaseGeomPoly_galActionHom_surjective (n : ℕ) (hn : 3 ≤ n) :
    Function.Surjective
      (Gal.galActionHom (serreBaseGeomPoly n) (serreBaseGeomPoly n).SplittingField) := by
  classical
  rw [← MonoidHom.range_eq_top]
  obtain ⟨g, hg⟩ := serreBaseGeomPoly_hasSwap n hn
  exact Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (SerreBaseCover.serreBaseGeomPoly_isPreprimitive n hn)
    (Gal.galActionHom (serreBaseGeomPoly n) (serreBaseGeomPoly n).SplittingField g) hg ⟨g, rfl⟩

end
