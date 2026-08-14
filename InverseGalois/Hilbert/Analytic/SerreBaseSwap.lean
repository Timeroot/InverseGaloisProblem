import Mathlib
import InverseGalois.Hilbert.Analytic.SerreBaseCover
import InverseGalois.Hilbert.Analytic.MorseSwapBranch

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

/-- The coefficient ring acts faithfully on the splitting field: it embeds in the geometric base
field, which embeds in the splitting field. -/
instance (priority := high) : FaithfulSMul Abase (Lfield n) :=
  (faithfulSMul_iff_algebraMap_injective Abase (Lfield n)).2 <| by
    rw [IsScalarTower.algebraMap_eq Abase GeomBase (Lfield n), RingHom.coe_comp]
    exact (algebraMap GeomBase (Lfield n)).injective.comp
      (IsFractionRing.injective Abase GeomBase)

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
    simp
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

set_option synthInstance.maxHeartbeats 200000 in
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
  simp_all
  ext n_1 : 2
  simp_all only [coeff_add, coeff_X, coeff_C, AddMemClass.coe_add, coeff_sub, AddSubgroupClass.coe_sub]
  split
  next h =>
    subst h
    simp_all only [OneMemClass.coe_one, one_ne_zero, ↓reduceIte, ZeroMemClass.coe_zero, add_zero, sub_zero]
  next h =>
    simp_all only [ZeroMemClass.coe_zero, zero_add, zero_sub]
    split
    next h_1 =>
      subst h_1
      simp_all only [one_ne_zero, not_false_eq_true]
    next h_1 => simp_all only [ZeroMemClass.coe_zero, neg_zero]

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
        tsub_add_cancel_of_le <| Nat.succ_le_of_lt <| Nat.pos_of_ne_zero <| by simp_all]
    trivial
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

set_option synthInstance.maxHeartbeats 200000 in
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

end SerreBaseSwap

end
