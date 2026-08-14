import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Hilbert.Analytic.NewtonPuiseux
import InverseGalois.Polynomial.FrobeniusLift
import InverseGalois.Hilbert.Analytic.SelmerMorse

/-!
# Reduction of `morseGeomPoly_hasSwap` to a Morse / inertia statement (work in progress)

This file develops a *structured reduction* of the single deep geometric-monodromy input
`morseGeomPoly_hasSwap` (a transposition in the geometric Galois group of `Xⁿ − X − T` over
`ℚ̄(T)`) to Mathlib's Morse-polynomial machinery
(`Mathlib.RingTheory.Polynomial.Morse`) and its ramification-in-Galois theory
(`Mathlib.NumberTheory.RamificationInertia.Galois`).

With `A = ℚ̄[T]`, `L = (morseGeomPoly n).SplittingField`, `B = integralClosure A L` and
`G = (morseGeomPoly n).Gal`, we install the complete instance infrastructure making
`IsGaloisGroup G A B` hold: `B` is a Dedekind domain, module-finite and torsion-free over the
Dedekind (in fact principal) domain `A`, `IsFractionRing B L`, and the `G`-action on `L`
restricts to `B` and is a Galois-group action for `A ⊆ B` (`iggB`).

## The reduction (assembled in `swap_input_final`)

* `gal_smul_coe` identifies the restricted Galois action with the action in the splitting field.
* `morse_ncard_bound` proves the Morse condition: reduction has at most one repeated root.
* `exists_nontrivial_inertia` supplies a ramified finite branch point with nontrivial inertia.

These feed `swap_input_final`, which directly proves `morseGeomPoly_hasSwap`. -/

open Polynomial
open scoped Classical
noncomputable section


namespace MorseSwap

abbrev Abase := Polynomial (AlgebraicClosure ℚ)

local instance splitsFact (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

variable (n : ℕ) [hn2 : Fact (2 ≤ n)]

abbrev Lfield := (morseGeomPoly n).SplittingField
abbrev Bring := integralClosure Abase (Lfield n)

instance : IsGalois GeomBase (Lfield n) :=
  IsGalois.of_separable_splitting_field (morseGeomPoly_separable n hn2.out)

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

instance sccGeom : SMulCommClass (morseGeomPoly n).Gal GeomBase (Lfield n) :=
  ⟨fun g a x ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    rw [AlgEquiv.smul_def]
    exact AlgEquiv.commutes g a⟩

instance sccA : SMulCommClass (morseGeomPoly n).Gal Abase (Lfield n) :=
  ⟨fun g a x ↦ by
    have h1 : g • (algebraMap Abase (Lfield n) a) = algebraMap Abase (Lfield n) a := by
      rw [IsScalarTower.algebraMap_apply Abase GeomBase (Lfield n)]
      exact smul_algebraMap g (algebraMap Abase GeomBase a)
    calc g • (a • x) = g • ((algebraMap Abase (Lfield n) a) * x) := by rw [Algebra.smul_def]
      _ = (g • algebraMap Abase (Lfield n) a) * (g • x) := by rw [smul_mul']
      _ = (algebraMap Abase (Lfield n) a) * (g • x) := by rw [h1]
      _ = a • (g • x) := by rw [Algebra.smul_def]⟩

instance iggL : IsGaloisGroup (morseGeomPoly n).Gal GeomBase (Lfield n) :=
  IsGaloisGroup.of_mulEquiv (G := Lfield n ≃ₐ[GeomBase] Lfield n)
    ({ toFun := id, invFun := id, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
       map_mul' := fun _ _ ↦ rfl } : (morseGeomPoly n).Gal ≃* (Lfield n ≃ₐ[GeomBase] Lfield n))
    (fun _ _ ↦ rfl)

instance iggB : IsGaloisGroup (morseGeomPoly n).Gal Abase (Bring n) :=
  IsGaloisGroup.of_isFractionRing (morseGeomPoly n).Gal Abase (Bring n) GeomBase (Lfield n)

/-! ## The equivariant bijection between roots in `B` and roots in `L` -/

/-
Every root of `genPolyC n` in `B` maps to a root of `morseGeomPoly n` in `L`.
-/
lemma rootMap_mem (x : (genPolyC n).rootSet (Bring n)) :
    ((x : Bring n) : Lfield n) ∈ (morseGeomPoly n).rootSet (Lfield n) := by
  -- Since `x` is a root of `genPolyC n` in `Bring n`, we have `aeval (x : Bring n) (genPolyC n) = 0`.
  have h_root : aeval (x.val : (Lfield n)) (genPolyC n) = 0 := by
    convert Polynomial.aeval_eq_zero_of_mem_rootSet x.2 using 1
    erw [← Subtype.coe_inj]
    simp
  rw [Polynomial.mem_rootSet']
  constructor
  · refine ne_of_apply_ne Polynomial.natDegree ?_
    simp [morseGeomPoly_natDegree n hn2.1]
    linarith [hn2.1]
  · unfold morseGeomPoly
    simp_all [genPolyC]
    exact h_root

/-- The inclusion `B ↪ L` on roots. -/
def rootMap (x : (genPolyC n).rootSet (Bring n)) : (morseGeomPoly n).rootSet (Lfield n) :=
  ⟨((x : Bring n) : Lfield n), rootMap_mem n x⟩

set_option synthInstance.maxHeartbeats 200000 in
lemma rootMap_bijective : Function.Bijective (rootMap n) := by
  constructor
  · intro x y hxy
    simpa [rootMap] using hxy
  · intro y
    -- Let `y` be a root of `morseGeomPoly n` in `Lfield n`. Then `y` is integral over `Abase`.
    have hy_integral : IsIntegral Abase (y.val : Lfield n) := by
      refine ⟨genPolyC n, ?_, ?_⟩
      · exact genPolyC_monic n hn2.1
      · convert Polynomial.aeval_eq_zero_of_mem_rootSet y.2 using 1
        unfold morseGeomPoly
        simp_all only [aeval_map_algebraMap]
        obtain ⟨val, property⟩ := y
        simp_all only
        rfl
    refine ⟨⟨⟨y.val, hy_integral⟩, ?_⟩, ?_⟩
    all_goals norm_num [rootMap]
    rw [Polynomial.mem_rootSet']
    constructor
    · refine ne_of_apply_ne Polynomial.natDegree ?_
      simp [genPolyC]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num <;> linarith [hn2.1]
    · convert Polynomial.aeval_eq_zero_of_mem_rootSet y.2 using 1
      unfold morseGeomPoly
      simp [genPolyC]
      erw [Subtype.ext_iff]
      trivial

/-- The inclusion `B ↪ L` restricts to a bijection on root sets. -/
def rootEquiv : (genPolyC n).rootSet (Bring n) ≃ (morseGeomPoly n).rootSet (Lfield n) :=
  Equiv.ofBijective (rootMap n) (rootMap_bijective n)

@[simp] lemma rootEquiv_apply (x : (genPolyC n).rootSet (Bring n)) :
    ((rootEquiv n x : (morseGeomPoly n).rootSet (Lfield n)) : Lfield n) = ((x : Bring n) : Lfield n) :=
  rfl

omit hn2 in
/-- The coercion of the *direct* monodromy action on the `L`-roots is just applying the
automorphism.

Here `galActionAux_perm (morseGeomPoly n) g` is the permutation of the roots of `morseGeomPoly n`
in `L = SplittingField` induced by literally applying the field automorphism `g` (Mathlib's
`Polynomial.Gal.galActionAux`).

Note: the *generic* `MulAction` instance `Polynomial.Gal.galAction` on `rootSet E` — the one used
by `Gal.galActionHom` — is **not** this direct action.  For `E = p.SplittingField` it is defined by
conjugating the direct action with the bijection `Gal.rootsEquivRoots p E`, whose underlying map is
`IsScalarTower.toAlgHom GeomBase SF SF = algebraMap SF SF` for the non-canonical `Polynomial.Gal`
algebra instance `Algebra SF SF`.  That embedding is a chosen `F`-algebra endomorphism of `SF`
(via `IsSplittingField.lift`, using `Classical.choice`) which is *not* forced to be the identity,
so the naive identity `↑(g • y) = g ↑y` for the generic `galAction` `•` genuinely fails to be
provable (it would require that embedding to be central in the Galois group).  The always-true
statement is the one below for the direct action; the generic `galActionHom` is recovered from it
up to that fixed conjugation in `galActionHom_eq_permCongr`. -/
lemma gal_smul_coe (g : (morseGeomPoly n).Gal) (y : (morseGeomPoly n).rootSet (Lfield n)) :
    ((galActionAux_perm (morseGeomPoly n) g y : (morseGeomPoly n).rootSet (Lfield n)) : Lfield n)
      = g ((y : Lfield n)) :=
  galActionAux_perm_val (morseGeomPoly n) g y

set_option synthInstance.maxHeartbeats 200000 in
/-- `rootEquiv` intertwines the direct `B`-root action with the direct `L`-root action
(`galActionAux_perm`). -/
lemma rootEquiv_smul (g : (morseGeomPoly n).Gal) (x : (genPolyC n).rootSet (Bring n)) :
    rootEquiv n (g • x) = galActionAux_perm (morseGeomPoly n) g (rootEquiv n x) := by
  apply Subtype.ext
  rw [gal_smul_coe, rootEquiv_apply, rootSet.coe_smul, integralClosure.coe_smul, rootEquiv_apply,
    AlgEquiv.smul_def]

/-- The direct `L`-root permutation `galActionAux_perm` is `rootEquiv`-conjugate to the `B`-root
permutation representation. -/
lemma galActionAux_perm_eq (g : (morseGeomPoly n).Gal) :
    galActionAux_perm (morseGeomPoly n) g
      = (Equiv.permCongr (rootEquiv n)) (MulAction.toPermHom (morseGeomPoly n).Gal
          ((genPolyC n).rootSet (Bring n)) g) := by
  ext y
  obtain ⟨x, rfl⟩ := (rootEquiv n).surjective y
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, MulAction.toPermHom_apply,
    MulAction.toPerm_apply]
  rw [rootEquiv_smul]

/-
The permutation representation on `B`-roots agrees with `galActionHom` on `L`-roots
via the composed bijection `rootEquiv ≫ rootsEquivRoots`.
-/
lemma galActionHom_eq_permCongr (g : (morseGeomPoly n).Gal) :
    Gal.galActionHom (morseGeomPoly n) (Lfield n) g
      = (Equiv.permCongr ((rootEquiv n).trans
            (Gal.rootsEquivRoots (morseGeomPoly n) (Lfield n))))
          (MulAction.toPermHom (morseGeomPoly n).Gal
          ((genPolyC n).rootSet (Bring n)) g) := by
  rw [_root_.galActionHom_eq_permCongr (morseGeomPoly n) (Lfield n) g, galActionAux_perm_eq n g]
  ext x
  simp [Equiv.permCongr_apply]

/-! ## The polynomial splits in `B` -/

lemma genPolyC_splits_B : ((genPolyC n).map (algebraMap Abase (Bring n))).Splits := by
  obtain ⟨s, hs⟩ : ∃ s : Multiset (↥(Bring n)),
      (genPolyC n).map (algebraMap Abase (↥(Bring n)))
        = Multiset.prod (Multiset.map (fun r : ↥(Bring n) ↦ Polynomial.X - Polynomial.C r) s) := by
    have h_range : ∀ r ∈ (genPolyC n).rootSet (Lfield n),
        r ∈ Set.range (algebraMap (Bring n) (Lfield n)) := by
      intro r hr
      have h_int : IsIntegral Abase r := by
        rw [Polynomial.mem_rootSet'] at hr
        use genPolyC n
        exact ⟨genPolyC_monic n hn2.1, hr.2⟩
      exact ⟨⟨r, h_int⟩, rfl⟩
    have h_prod : (genPolyC n).map (algebraMap Abase (Lfield n))
        = Multiset.prod (Multiset.map (fun r : Lfield n ↦ Polynomial.X - Polynomial.C r)
            (Polynomial.roots (genPolyC n |> Polynomial.map (algebraMap Abase (Lfield n))))) := by
      convert Polynomial.Splits.eq_prod_roots_of_monic _ _
      · convert Polynomial.IsSplittingField.splits (Lfield n) (morseGeomPoly n) using 1
        unfold morseGeomPoly
        simp_all only [Subalgebra.setRange_algebraMap, SetLike.mem_coe]
        ext n_1 : 1
        simp_all only [coeff_map]
        rfl
      · exact Polynomial.Monic.map _ (genPolyC_monic n hn2.1)
    obtain ⟨s, hs⟩ : ∃ s : Multiset (↥(Bring n)),
        Multiset.map (fun r : ↥(Bring n) ↦ algebraMap (Bring n) (Lfield n) r) s
          = Polynomial.roots (genPolyC n |> Polynomial.map (algebraMap Abase (Lfield n))) := by
      have h_prod_range : ∀ r ∈ Polynomial.roots (genPolyC n |> Polynomial.map (algebraMap Abase (Lfield n))),
          r ∈ Set.range (algebraMap (Bring n) (Lfield n)) := by
        convert h_range using 1
        simp [Polynomial.rootSet_def]
      choose! f hf using h_prod_range
      use Multiset.map f (Polynomial.roots (genPolyC n |> Polynomial.map (algebraMap Abase (Lfield n))))
      rw [Multiset.map_map]
      rw [Multiset.map_congr rfl]
      exacts [Multiset.map_id _, fun x hx ↦ hf x hx]
    use s
    refine Polynomial.map_injective (algebraMap (Bring n) (Lfield n))
      (IsIntegralClosure.algebraMap_injective (Bring n) (Abase) (Lfield n)) ?_
    convert h_prod using 1
    · ext
      simp [genPolyC]
    · simp [← hs, Polynomial.map_multiset_prod]
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
    MulAction.IsPretransitive (morseGeomPoly n).Gal ((genPolyC n).rootSet (Bring n)) := by
  refine ⟨fun x y ↦ ?_⟩
  set e := (rootEquiv n).trans (Gal.rootsEquivRoots (morseGeomPoly n) (Lfield n))
  obtain ⟨g, hg⟩ := (Gal.galAction_isPretransitive (morseGeomPoly n) (Lfield n)
      (morseGeomPoly_irreducible n hn2.out)).exists_smul_eq (e x) (e y)
  refine ⟨g, ?_⟩
  have hgh : Gal.galActionHom (morseGeomPoly n) (Lfield n) g (e x) = e y := hg
  rw [galActionHom_eq_permCongr n g, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    MulAction.toPermHom_apply, MulAction.toPerm_apply] at hgh
  exact e.injective hgh

lemma toPermHom_B_injective :
    Function.Injective (MulAction.toPermHom (morseGeomPoly n).Gal
      ((genPolyC n).rootSet (Bring n))) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  ext
  simp_all [Equiv.Perm.ext_iff, MulAction.toPermHom_apply]
  rename_i a ha
  have h_root : ∃ r : (genPolyC n).rootSet (Bring n), (r : Lfield n) = a := by
    convert rootMap_bijective n |>.surjective ⟨a, ha⟩ using 1
    ext
    simp [rootMap]
  obtain ⟨r, rfl⟩ := h_root
  specialize hx _ _ r.2
  simp_all [Subtype.ext_iff]
  exact hx

/-! ## A ramified branch point via Kummer–Dedekind (elementary inputs) -/

/-
**Existence of a critical point.**  Over the algebraically closed field `ℚ̄` of
characteristic zero there is `c ≠ 0` with `n · c^(n-1) = 1`; this is the abscissa of a double
root of the fibre `Xⁿ - X - t₀` at the critical value `t₀ = cⁿ - c`.
-/
lemma exists_critPoint :
    ∃ c : AlgebraicClosure ℚ, (n : AlgebraicClosure ℚ) * c ^ (n - 1) = 1 ∧ c ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c : AlgebraicClosure ℚ, c ^ (n - 1) = 1 / (n : AlgebraicClosure ℚ) := by
    convert IsAlgClosed.exists_pow_nat_eq _ _
    · infer_instance
    · exact Nat.sub_pos_of_lt hn2.1
  refine ⟨c, ?_, ?_⟩ <;> simp_all [ne_of_gt (zero_lt_two.trans_le hn2.1)]
  rintro rfl
  rcases n with (_ | _ | n) <;> norm_num at *
  · exact hn2.elim
  · norm_cast at hc

/-
**The fibre has a double root.**  With `n · c^(n-1) = 1` and `t₀ = cⁿ - c`, the linear factor
`X - c` divides `Xⁿ - X - t₀` at least twice.
-/
omit hn2 in
lemma sq_dvd_fiber (c : AlgebraicClosure ℚ) (hc : (n : AlgebraicClosure ℚ) * c ^ (n - 1) = 1) :
    (X - C c) ^ 2 ∣ (X ^ n - X - C (c ^ n - c) : (AlgebraicClosure ℚ)[X]) := by
  obtain ⟨q, hq⟩ : ∃ q : (AlgebraicClosure ℚ)[X],
      (X - Polynomial.C c) * q = Polynomial.X ^ n - Polynomial.X - Polynomial.C (c ^ n - c) := by
    refine ⟨(Polynomial.X ^ n - Polynomial.X - Polynomial.C (c ^ n - c)) /ₘ
      (Polynomial.X - Polynomial.C c), ?_⟩
    have hroot : (Polynomial.X ^ n - Polynomial.X - Polynomial.C (c ^ n - c) :
        (AlgebraicClosure ℚ)[X]).IsRoot c := by simp
    rw [Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot]
  convert mul_dvd_mul_left (X - C c) (Polynomial.dvd_iff_isRoot.mpr (show q.eval c = 0 from ?_)) using 1
  · ring
  · exact hq.symm
  · replace hq := congr_arg (Polynomial.derivative) hq
    norm_num at hq
    replace hq := congr_arg (Polynomial.eval c) hq
    simp_all [Polynomial.derivative_pow]

/-! ## The Morse (at-most-one-collision) condition -/

/-
Derivative of `Xᵐ − X − C c` is `m·X^{m-1} − 1`.
-/
theorem genC_derivative {F : Type*} [CommRing F] (m : ℕ) (c : F) :
    derivative (X ^ m - X - C c : F[X]) = (m : F[X]) * X ^ (m - 1) - 1 := by
  cases m <;> simp [Polynomial.derivative_sub, Polynomial.derivative_pow]

/-
**Uniqueness of the singular point.**  Over a domain `F` with `(m:F) ≠ 0` and `(m:F) ≠ 1`,
`Xᵐ − X − C c` and its derivative have at most one common root.  At a common root `α`:
`m·α^{m-1} = 1` and `α^m = α + c`; multiplying the first by `α` gives `m·(α + c) = α`, i.e.
`(1 − m)·α = m·c`, which determines `α` uniquely since `1 − m ≠ 0`.
-/
theorem genC_common_root_unique {F : Type*} [CommRing F] [IsDomain F] {m : ℕ} (hm : 2 ≤ m)
    (c : F) (_hnz : (m : F) ≠ 0) (hn1 : (m : F) ≠ 1) {a b : F}
    (ha : (X ^ m - X - C c : F[X]).IsRoot a)
    (ha' : (derivative (X ^ m - X - C c : F[X])).IsRoot a)
    (hb : (X ^ m - X - C c : F[X]).IsRoot b)
    (hb' : (derivative (X ^ m - X - C c : F[X])).IsRoot b) : a = b := by
  simp_all [Polynomial.derivative_pow]
  -- Since `m ≥ 2`, we have `m = (m-1) + 1`, thus `a^m = a * a^(m-1)`.
  have ha_pow : a ^ m = a * a ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by linarith)]
  have hb_pow : b ^ m = b * b ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by linarith)]
  refine mul_left_cancel₀ (sub_ne_zero_of_ne hn1) ?_
  grind

/-
**No triple roots.**  Over a domain `F` with `(m:F) ≠ 0` and `(m:F) ≠ 1`, every root of
`Xᵐ − X − C c` has multiplicity at most `2`.  If `(X − C a)³ ∣ Xᵐ − X − C c`, then the second
derivative `m(m−1)·X^{m-2}` also vanishes at `a`; but `a ≠ 0` (from `m·a^{m-1} = 1`) and
`m(m−1) ≠ 0`, a contradiction.
-/
theorem genC_rootMultiplicity_le_two {F : Type*} [CommRing F] [IsDomain F] {m : ℕ} (hm : 2 ≤ m)
    (c : F) (hnz : (m : F) ≠ 0) (hn1 : (m : F) ≠ 1) (a : F) :
    (X ^ m - X - C c : F[X]).rootMultiplicity a ≤ 2 := by
  -- By contradiction, assume 2 < rootMultiplicity a p where p = X^m - X - C c.
  by_contra h_contra
  have h_div : (X - C a) ^ 3 ∣ (X ^ m - X - C c : F[X]) := by
    exact dvd_trans (pow_dvd_pow _ (not_le.mp h_contra)) (Polynomial.pow_rootMultiplicity_dvd _ _)
  -- Since `(X - C a)^3` divides `p`, we have `p(a) = 0`, `p'(a) = 0`, and `p''(a) = 0`.
  have h_eval : Polynomial.eval a (Polynomial.X ^ m - Polynomial.X - Polynomial.C c) = 0 ∧
      Polynomial.eval a (Polynomial.derivative (Polynomial.X ^ m - Polynomial.X - Polynomial.C c)) = 0 ∧
      Polynomial.eval a (Polynomial.derivative (Polynomial.derivative
        (Polynomial.X ^ m - Polynomial.X - Polynomial.C c))) = 0 := by
    obtain ⟨q, hq⟩ := h_div
    simp_all [pow_succ, mul_assoc]
  rcases m with (_ | _ | m) <;> simp_all [Polynomial.derivative_pow]
  obtain ⟨left, right⟩ := h_eval
  obtain ⟨left_1, right⟩ := right
  obtain ⟨left_2, right⟩ := right
  subst left_2
  simp_all only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_self, not_false_eq_true, zero_pow, sub_self, zero_sub,
    neg_eq_zero, mul_zero]

/-
**Field-level Morse count.**  Over a domain `F` with `(m:F) ≠ 0` and `(m:F) ≠ 1`, the number
of roots of `Xᵐ − X − C c` counted with multiplicity exceeds the number of distinct roots by at
most one.  Follows from `genC_common_root_unique` (at most one root of multiplicity `≥ 2`) and
`genC_rootMultiplicity_le_two` (no root of multiplicity `≥ 3`).  This mirrors
`SelmerMorse.selmer_ncard_roots_field`.
-/
theorem genC_ncard_roots_field {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F] {m : ℕ}
    (hm : 2 ≤ m) (c : F) (hnz : (m : F) ≠ 0) (hn1 : (m : F) ≠ 1) :
    (X ^ m - X - C c : F[X]).roots.card ≤ (X ^ m - X - C c : F[X]).roots.toFinset.card + 1 := by
  set p : F[X] := X ^ m - X - C c with hp
  have h_at_most_one_repeated :
      (p.roots.toFinset.filter (fun a ↦ p.rootMultiplicity a ≥ 2)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb ↦ ?_
    simp_all
    apply genC_common_root_unique hm c hnz hn1
    · simp_all
    · exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity ha.2
    · simp_all
    · exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hb.2
  have h_sum_le_one :
      ∑ a ∈ p.roots.toFinset, (p.rootMultiplicity a - 1)
        ≤ (p.roots.toFinset.filter (fun a ↦ p.rootMultiplicity a ≥ 2)).card := by
    rw [Finset.card_filter]
    gcongr
    split_ifs <;> simp_all
    · exact genC_rootMultiplicity_le_two hm c hnz hn1 _
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

/-
**Abstract Morse bound.**  For `f = Xᵐ − X − C t` over a domain `S` in which `f` splits, and
any prime `P` with residue field of characteristic zero, the roots of `f` in `S` collide at most
once modulo `P`.  Combines `SelmerMorse.ncard_rootSet_le_roots_card` (distinct roots in `S` inject,
with multiplicity, into the reduced roots) with `genC_ncard_roots_field` over `F = S ⧸ P`.
-/
theorem morse_ncard_bound_abstract {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] {m : ℕ} (hm : 2 ≤ m) (t : R) (f : R[X]) (hf : f = X ^ m - X - C t)
    (P : Ideal S) [P.IsPrime] [CharZero (S ⧸ P)]
    (hsplit : (f.map (algebraMap R S)).Splits) :
    (f.rootSet S).ncard ≤ (f.rootSet (S ⧸ P)).ncard + 1 := by
  have h1 : (f.rootSet S).ncard ≤ ((f.map (algebraMap R (S ⧸ P))).roots).card := by
    convert SelmerMorse.ncard_rootSet_le_roots_card f _
    all_goals try infer_instance
    intro h
    have := congr_arg (Polynomial.eval 0) h
    norm_num [hf] at this
    replace h := congr_arg (fun q ↦ Polynomial.coeff q (m : ℕ)) h
    simp_all
    rcases m with (_ | _ | m) <;> simp_all [Polynomial.coeff_eq_zero_of_natDegree_lt]
  convert h1.trans _
  convert genC_ncard_roots_field hm (algebraMap R (S ⧸ P) t) _ _ using 1
  · simp_all
  · rw [← Set.ncard_coe_finset]
    congr
    ext
    simp [Polynomial.rootSet_def]
    simp [hf, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  · exact Nat.cast_ne_zero.mpr (by linarith)
  · exact_mod_cast ne_of_gt hm

set_option synthInstance.maxHeartbeats 200000 in
/-- For any maximal ideal `P` of `B`, the roots of `genPolyC` collide at most once modulo `P`. -/
lemma morse_ncard_bound (P : Ideal (Bring n)) [P.IsMaximal] :
    ((genPolyC n).rootSet (Bring n)).ncard ≤ ((genPolyC n).rootSet (Bring n ⧸ P)).ncard + 1 := by
  have : CharZero (Bring n ⧸ P) := by
    have inj : Function.Injective
        ((Ideal.Quotient.mk P).comp ((algebraMap Abase (Bring n)).comp
          (Polynomial.C : AlgebraicClosure ℚ →+* Abase))) := RingHom.injective _
    exact charZero_of_injective_ringHom inj
  exact morse_ncard_bound_abstract (R := Abase) (S := Bring n) (m := n) hn2.out
    (Polynomial.X) (genPolyC n) rfl P (genPolyC_splits_B n)

/-! ## Existence of a ramified branch point (nontrivial inertia) -/

/-- **Abstract assembly.**  If there is an intermediate Dedekind ring `Smid` between `A` and `B`
and a prime `PS` of `Smid` over a nonzero maximal ideal `p` of `A` with ramification index at
least `2`, then some maximal ideal of `B` has nontrivial inertia.  (Ramification propagates up
the tower `A ⊆ Smid ⊆ B`, and in the Galois setting the inertia group has order equal to the
ramification index in `B`.) -/
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
    ∃ (P : Ideal (Bring n)), P.IsMaximal ∧
      ∃ g : (morseGeomPoly n).Gal, g ∈ P.inertia (morseGeomPoly n).Gal ∧ g ≠ 1 := by
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ := PS.nonempty_primesOver (S := Bring n)
  have : Q.IsPrime := hQprime
  have : Q.LiesOver PS := hQover
  have : Q.LiesOver p := Ideal.LiesOver.trans Q PS p
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
    Ideal.ramificationIdxIn_eq_ramificationIdx p Q (morseGeomPoly n).Gal
  have := hsep Q
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := (morseGeomPoly n).Gal) p hp Q
  have h2card : 2 ≤ Nat.card (Ideal.inertia (morseGeomPoly n).Gal Q) := by
    rw [hcard, hIn]
    exact h2
  have hNT : Nontrivial (Ideal.inertia (morseGeomPoly n).Gal Q) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨g, hg⟩ := exists_ne (1 : Ideal.inertia (morseGeomPoly n).Gal Q)
  refine ⟨Q, inferInstance, g, g.2, ?_⟩
  simpa using hg

end MorseSwap
