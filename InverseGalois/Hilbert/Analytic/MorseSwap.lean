import Mathlib
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

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
    aesop
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
        aesop
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
      aesop

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
        aesop
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
  aesop

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
        (AlgebraicClosure ℚ)[X]).IsRoot c := by aesop
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
  aesop

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
    · aesop
    · exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity ha.2
    · aesop
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
        tsub_add_cancel_of_le <| Nat.succ_le_of_lt <| Nat.pos_of_ne_zero <| by aesop]
    aesop
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
  · aesop
  · rw [← Set.ncard_coe_finset]
    congr
    ext
    simp [Polynomial.rootSet_def]
    simp [hf, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  · exact Nat.cast_ne_zero.mpr (by linarith)
  · exact_mod_cast ne_of_gt hm

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

/-! ### The concrete intermediate ring `A[x] = ℚ̄[x] ⊆ B` -/

/-
There is a root of `genPolyC n` inside `B = Bring n`.
-/
lemma exists_rootB : ∃ x : Bring n, (aeval x) (genPolyC n) = 0 := by
  have hcard := morseGeomPoly_card_rootSet n hn2.out
  have hne : Nonempty ((morseGeomPoly n).rootSet (Lfield n)) :=
    Fintype.card_pos_iff.mp (hcard.symm ▸ hn2.1.trans_lt' (by decide))
  obtain ⟨r⟩ := hne
  obtain ⟨s, _⟩ := (rootMap_bijective n).2 r
  exact ⟨s, Polynomial.aeval_eq_zero_of_mem_rootSet s.2⟩

/-- A chosen root of `genPolyC n` in `B`. -/
def rootB : Bring n := (exists_rootB n).choose

lemma rootB_spec : (aeval (rootB n)) (genPolyC n) = 0 := (exists_rootB n).choose_spec

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

instance : Module.Finite (Smid n) (Bring n) := by
  have h_finite : Module.Finite Abase (Bring n) := by
    infer_instance
  exact h_finite.of_restrictScalars_finite Abase (Smid n) (Bring n)

instance : Algebra.IsIntegral (Smid n) (Bring n) := by
  infer_instance

omit hn2 in
lemma algebraMap_Abase_Bring_injective : Function.Injective (algebraMap Abase (Bring n)) := by
  -- Assume `x : Abase` maps to `0 : Bring n`. Then `x = 0` because (by `integralClosure`/`IsIntegralClosure`) the algebra map `Abase ↪ Lfield n` is injective, and `Bring n ↪ Lfield n` is injective (`subtype quotation`).
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
  · exact fun r ↦ Subalgebra.algebraMap_mem _ r
  · exact fun x y hx hy hx' hy' ↦ Subalgebra.add_mem _ hx' hy'
  · exact fun x y hx hy hx' hy' ↦ Subalgebra.mul_mem _ hx' hy'

lemma xS_minpoly : minpoly Abase (xS n) = genPolyC n := by
  -- Since `genPolyC n` is irreducible and monic, and `xS n` is a root, it must be the minimal polynomial.
  have h_minpoly_div : minpoly Abase (xS n) ∣ genPolyC n := by
    refine minpoly.isIntegrallyClosed_dvd ?_ ?_
    · refine ⟨genPolyC n, ?_, ?_⟩
      · exact genPolyC_monic n hn2.1
      · convert rootB_spec n using 1
        simp [aeval_def, Polynomial.eval₂_eq_sum_range]
        erw [← Subtype.coe_inj]
        aesop
    · convert rootB_spec n using 1
      erw [← Subtype.coe_inj]
      simp [xS]
  have h_irreducible : Irreducible (genPolyC n) := by
    exact genPolyC_irreducible n
  refine Polynomial.eq_of_monic_of_associated ?_ ?_ ?_
  · apply minpoly.monic
    refine ⟨genPolyC n, ?_, ?_⟩
    · exact genPolyC_monic n hn2.1
    · convert rootB_spec n using 1
      simp [xS, aeval_def, Polynomial.eval₂_eq_sum_range]
      simp [← Subtype.coe_inj]
  · exact genPolyC_monic n hn2.1
  · obtain ⟨q, hq⟩ := h_minpoly_div
    have := h_irreducible.2
    specialize this hq
    exact this.elim (fun h ↦ False.elim <| minpoly.not_isUnit Abase (xS n) h)
      fun h ↦ associated_of_dvd_dvd (by aesop) (by aesop)

/-
The image of the base variable `T` in `A[x]` is `xⁿ - x`.
-/
lemma algebraMap_Abase_Smid_X :
    algebraMap Abase (Smid n) (Polynomial.X) = (xS n) ^ n - xS n := by
  convert rootB_spec n using 1
  simp [← Subtype.coe_inj, genPolyC]
  simp [sub_eq_zero, xS]
  exact eq_comm

/-
`A[x]` is generated as a ring by `ℚ̄` and `x`: the `ℚ̄`-polynomial evaluation map at `x` is
surjective onto `A[x]`.  Consequently `A[x]` is a quotient (in fact isomorphic image) of a
principal ideal ring, hence itself a principal ideal ring.
-/
lemma Smid_eval_surjective :
    Function.Surjective
      (Polynomial.eval₂RingHom ((algebraMap Abase (Smid n)).comp Polynomial.C) (xS n)) := by
  intro y
  have h_span : ∀ y : Smid n, y ∈ Subalgebra.toSubmodule (Algebra.adjoin (Abase) {xS n}) := by
    intro y
    apply Algebra.eq_top_iff.mp (by
    convert (conductor_eq_top_iff_adjoin_eq_top (R := Abase) (x := xS n)).mp (xS_conductor_top n) using 1) y
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ (h_span y)
  · exact fun x hx ↦ ⟨Polynomial.X, by aesop⟩
  · intro r
    use Polynomial.comp r (Polynomial.X ^ n - Polynomial.X)
    simp [Polynomial.eval₂_comp]
    rw [Polynomial.eval₂_eq_sum_range]
    conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow r]
    simp [map_sum, map_mul, map_pow, algebraMap_Abase_Smid_X]
  · rintro x y hx hy ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp⟩
  · rintro x y hx hy ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by simp⟩

instance : IsDedekindDomain (Smid n) := by
  have : IsPrincipalIdealRing (Smid n) :=
    IsPrincipalIdealRing.of_surjective _ (Smid_eval_surjective n)
  infer_instance

/-! ### The branch-point ideal and its ramification -/

/-- The critical constant `c` (abscissa of a double root). -/
def critC : AlgebraicClosure ℚ := (exists_critPoint n).choose

lemma critC_spec : (n : AlgebraicClosure ℚ) * (critC n) ^ (n - 1) = 1 ∧ critC n ≠ 0 :=
  (exists_critPoint n).choose_spec

/-- The critical value `t₀ = cⁿ - c`. -/
def critT : AlgebraicClosure ℚ := (critC n) ^ n - critC n

/-- The branch-point maximal ideal `(T - t₀)` of `A = ℚ̄[T]`. -/
def branchIdeal : Ideal Abase := Ideal.span {Polynomial.X - Polynomial.C (critT n)}

instance : (branchIdeal n).IsMaximal := by
  convert PrincipalIdealRing.isMaximal_of_irreducible _
  · infer_instance
  · exact Polynomial.irreducible_X_sub_C _

lemma branchIdeal_ne_bot : branchIdeal n ≠ ⊥ := by
  unfold branchIdeal
  rw [Ne.eq_def, Ideal.span_singleton_eq_bot]
  exact Polynomial.X_sub_C_ne_zero _

attribute [local instance] Ideal.Quotient.field

/-- Over the residue field `A/(T - t₀) ≅ ℚ̄`, the reduced polynomial `genPolyC mod` has the double
root `c`: the square of the linear factor `X - c` divides it. -/
lemma branch_reduced_sq_dvd :
    (X - C (Ideal.Quotient.mk (branchIdeal n) (Polynomial.C (critC n))))^2 ∣
      (genPolyC n).map (Ideal.Quotient.mk (branchIdeal n)) := by
  set ρ : (AlgebraicClosure ℚ) →+* (Abase ⧸ branchIdeal n) :=
    (Ideal.Quotient.mk (branchIdeal n)).comp Polynomial.C with hρ
  have hXeq : (Ideal.Quotient.mk (branchIdeal n)) (Polynomial.X) =
      (Ideal.Quotient.mk (branchIdeal n)) (Polynomial.C (critT n)) := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hmapeq : (genPolyC n).map (Ideal.Quotient.mk (branchIdeal n))
      = (X ^ n - X - C (critC n ^ n - critC n)).map ρ := by
    rw [genPolyC]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [hXeq, hρ]
    simp [critT, RingHom.comp_apply]
  rw [hmapeq]
  have hdvd := sq_dvd_fiber n (critC n) (critC_spec n).1
  have := Polynomial.map_dvd ρ hdvd
  simpa [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hρ,
    RingHom.comp_apply] using this

/-- **The branch point ramifies in the intermediate ring.**  There is a prime `PS` of `A[x]`
over the branch ideal whose ramification index is at least `2` — coming from the double root of
the fibre `Xⁿ - X - t₀` via Kummer–Dedekind. -/
lemma branch_ramified :
    ∃ PS : Ideal (Smid n), PS.IsPrime ∧ PS.LiesOver (branchIdeal n) ∧
      2 ≤ Ideal.ramificationIdx (algebraMap Abase (Smid n)) (branchIdeal n) PS ∧
      Ideal.map (algebraMap (Smid n) (Bring n)) PS ≠ ⊥ := by
  classical
  have hsq := branch_reduced_sq_dvd n
  have hI' : branchIdeal n ≠ ⊥ := branchIdeal_ne_bot n
  have hxint : IsIntegral Abase (xS n) := ⟨genPolyC n, genPolyC_monic n hn2.out, by
    have := xS_minpoly n
    have h2 := minpoly.aeval Abase (xS n)
    rwa [this] at h2⟩
  have hx : (conductor Abase (xS n)).comap (algebraMap Abase (Smid n)) ⊔ (branchIdeal n) = ⊤ := by
    rw [xS_conductor_top]
    simp
  set d : (Abase ⧸ branchIdeal n)[X] := X - C (Ideal.Quotient.mk (branchIdeal n) (Polynomial.C (critC n))) with hd
  have hPne : (minpoly Abase (xS n)).map (Ideal.Quotient.mk (branchIdeal n)) ≠ 0 := by
    rw [xS_minpoly]
    exact (Polynomial.Monic.map _ (genPolyC_monic n hn2.out)).ne_zero
  have hd_irr : Irreducible d := irreducible_X_sub_C _
  have hd_norm : normalize d = d := (monic_X_sub_C _).normalize_eq_self
  have hcount2 : 2 ≤ Multiset.count d (UniqueFactorizationMonoid.normalizedFactors
      ((minpoly Abase (xS n)).map (Ideal.Quotient.mk (branchIdeal n)))) := by
    have hemult : (2 : ℕ∞) ≤ emultiplicity d ((minpoly Abase (xS n)).map (Ideal.Quotient.mk (branchIdeal n))) := by
      rw [xS_minpoly]
      exact pow_dvd_iff_le_emultiplicity.mp hsq
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hd_irr hPne, hd_norm] at hemult
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
  have hmapI_ne : Ideal.map (algebraMap Abase (Smid n)) (branchIdeal n) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI'
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
  have hPS_irr : Irreducible PS.1 := UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hmem
  have hPS_normeq : normalize PS.1 = PS.1 := UniqueFactorizationMonoid.normalize_normalized_factor _ hmem
  have hcount_eq : emultiplicity PS.1 (Ideal.map (algebraMap Abase (Smid n)) (branchIdeal n))
      = ((Multiset.count PS.1 (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.map (algebraMap Abase (Smid n)) (branchIdeal n)))) : ℕ∞) := by
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPS_irr hmapI_ne, hPS_normeq]
  have hd_emult : (2 : ℕ∞) ≤ emultiplicity d ((minpoly Abase (xS n)).map (Ideal.Quotient.mk (branchIdeal n))) := by
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hd_irr hPne, hd_norm]
    exact_mod_cast hcount2
  rw [← hkd, hcount_eq] at hd_emult
  exact_mod_cast hd_emult

/-
The residue field of `A` at the branch ideal is `ℚ̄`, which is perfect, so every residue
extension is separable.
-/
lemma branch_residue_separable (Q : Ideal (Bring n)) [Q.LiesOver (branchIdeal n)] [Q.IsMaximal] :
    Algebra.IsSeparable (Abase ⧸ branchIdeal n) ((Bring n) ⧸ Q) := by
  have : CharZero (Abase ⧸ branchIdeal n) := algebraRat.charZero _
  have : Algebra.IsIntegral (Abase ⧸ branchIdeal n) ((Bring n) ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (branchIdeal n)
  have : Algebra.IsAlgebraic (Abase ⧸ branchIdeal n) ((Bring n) ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

lemma exists_nontrivial_inertia :
    ∃ (P : Ideal (Bring n)), P.IsMaximal ∧
      ∃ g : (morseGeomPoly n).Gal, g ∈ P.inertia (morseGeomPoly n).Gal ∧ g ≠ 1 := by
  obtain ⟨PS, hPSprime, hPSover, hPSe, hPSmap⟩ := branch_ramified n
  have := hPSprime
  have := hPSover
  refine inertia_of_ramified n (Smid n) (branchIdeal n) (branchIdeal_ne_bot n)
    (algebraMap_Abase_Bring_injective n) PS hPSe hPSmap ?_ ?_
  · exact Ideal.map_ne_bot_of_ne_bot (branchIdeal_ne_bot n)
  · intro Q _ _
    exact branch_residue_separable n Q

/-
`permCongr` preserves being a transposition.
-/
lemma isSwap_permCongr {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    {σ : Equiv.Perm α} (h : σ.IsSwap) : (e.permCongr σ).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := h
  refine ⟨e a, e b, ?_, ?_⟩
  · simp [hab]
  · grind +qlia

/-! ## Assembling the transposition -/

theorem swap_input_final :
    ∃ g : Equiv.Perm ((morseGeomPoly n).rootSet (Lfield n)),
        g.IsSwap ∧
          g ∈ (Gal.galActionHom (morseGeomPoly n) (Lfield n)).range := by
  classical
  obtain ⟨P, hPmax, g, hg_in, hg_ne⟩ := exists_nontrivial_inertia n
  have : P.IsPrime := hPmax.isPrime
  -- residue field is `ℚ̄`, hence separable over `A/(P ∩ A)`
  -- Morse: `toPermHom g` is `1` or a swap
  have hmorse := Polynomial.Splits.toPermHom_apply_eq_one_or_isSwap_of_ncard_le_of_mem_inertia
    (R := Abase) (S := Bring n) (G := (morseGeomPoly n).Gal) (f := genPolyC n)
    (genPolyC_splits_B n) P (morse_ncard_bound n P) g hg_in
  -- it's not `1` because `g ≠ 1` and the action is faithful
  have hne1 : MulAction.toPermHom (morseGeomPoly n).Gal ((genPolyC n).rootSet (Bring n)) g ≠ 1 := by
    intro h
    refine hg_ne (toPermHom_B_injective n ?_)
    simpa using h
  have hswapB : (MulAction.toPermHom (morseGeomPoly n).Gal
      ((genPolyC n).rootSet (Bring n)) g).IsSwap := hmorse.resolve_left hne1
  -- transport to `L`-roots
  refine ⟨Gal.galActionHom (morseGeomPoly n) (Lfield n) g, ?_, ⟨g, rfl⟩⟩
  rw [galActionHom_eq_permCongr n g]
  exact isSwap_permCongr ((rootEquiv n).trans (Gal.rootsEquivRoots (morseGeomPoly n) (Lfield n)))
    hswapB

end MorseSwap

/-- The polynomial always splits in its own splitting field (top-level `local Fact` instance so
that `Gal.galActionHom` typechecks for the wired-in theorems below). -/
local instance splitsInSplittingField'' (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

open scoped Classical in
/-- **A transposition in the geometric monodromy group** (the second conjunct of the deep
input `morseGeomPoly_monodromy_input`): the group contains an element acting on the roots as a
transposition — the local monodromy / inertia generator at a simple finite branch point of the
cover `X ↦ Xⁿ − X` of the affine `T`-line, where two sheets collide as a square-root branch. -/
theorem morseGeomPoly_hasSwap (n : ℕ) (hn : 2 ≤ n) :
    ∃ g : Equiv.Perm ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField),
        g.IsSwap ∧
          g ∈ (Gal.galActionHom (morseGeomPoly n) (morseGeomPoly n).SplittingField).range := by
  have : Fact (2 ≤ n) := ⟨hn⟩
  exact MorseSwap.swap_input_final n

open scoped Classical in
/-- **The single deep geometric-monodromy input for the Morse family.** -/
theorem morseGeomPoly_monodromy_input (n : ℕ) (hn : 2 ≤ n) :
    (∀ B : Set ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField),
        MulAction.IsBlock (morseGeomPoly n).Gal B → MulAction.IsTrivialBlock B) ∧
      (∃ g : Equiv.Perm ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField),
        g.IsSwap ∧
          g ∈ (Gal.galActionHom (morseGeomPoly n) (morseGeomPoly n).SplittingField).range) :=
  ⟨morseGeomPoly_primitive n hn, morseGeomPoly_hasSwap n hn⟩

/-- **Primitivity of the geometric monodromy action** (extracted from the deep input
`morseGeomPoly_monodromy_input`): every block of the `p.Gal`-action on the roots is trivial. -/
theorem morseGeomPoly_blocks_trivial (n : ℕ) (hn : 2 ≤ n)
    {B : Set ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField)}
    (hB : MulAction.IsBlock (morseGeomPoly n).Gal B) : MulAction.IsTrivialBlock B :=
  (morseGeomPoly_monodromy_input n hn).1 B hB

/-- **Preprimitivity of the geometric monodromy action.**

The geometric Galois group of `Xⁿ − X − T` over `ℚ̄(T)`, acting on the roots, is
*preprimitive*: the action is transitive (`Gal.galAction_isPretransitive` from
`morseGeomPoly_irreducible`) and admits no nontrivial blocks
(`morseGeomPoly_blocks_trivial`).  Together with a transposition (`morseGeomPoly_hasSwap`)
this yields the full symmetric group by Jordan's theorem
(`Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`). -/
theorem morseGeomPoly_isPreprimitive (n : ℕ) (hn : 2 ≤ n) :
    MulAction.IsPreprimitive
      (Gal.galActionHom (morseGeomPoly n) (morseGeomPoly n).SplittingField).range
      ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) := by
  apply isPreprimitive_range_of_isPreprimitive
  have htrans : MulAction.IsPretransitive (morseGeomPoly n).Gal
      ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :=
    Gal.galAction_isPretransitive _ _ (morseGeomPoly_irreducible n hn)
  exact { toIsPretransitive := htrans
          isTrivialBlock_of_isBlock := fun {B} hB ↦ morseGeomPoly_blocks_trivial n hn hB }

/-- **The geometric-monodromy surjectivity, via Jordan's theorem.**

The permutation representation of the geometric Galois group of `Xⁿ − X − T` over `ℚ̄(T)` on
the roots is *surjective* onto the full symmetric group (equivalently, the geometric Galois
group is `Sₙ`).  This is the classical Morse-polynomial monodromy computation, here obtained
by feeding the preprimitivity of the action (`morseGeomPoly_isPreprimitive`) and a
transposition in the group (`morseGeomPoly_hasSwap`) into Jordan's theorem
(`Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`). -/
theorem morseGeomPoly_galActionHom_surjective (n : ℕ) (hn : 2 ≤ n) :
    Function.Surjective
      (Gal.galActionHom (morseGeomPoly n) (morseGeomPoly n).SplittingField) := by
  classical
  rw [← MonoidHom.range_eq_top]
  obtain ⟨g, hg2, hgmem⟩ := morseGeomPoly_hasSwap n hn
  exact Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (morseGeomPoly_isPreprimitive n hn) g hg2 hgmem

open scoped Classical in
/-- **The range of `galActionHom` contains a generating set of transpositions (proved from the
monodromy input).**

Once the permutation representation is surjective
(`morseGeomPoly_galActionHom_surjective`), its range is the whole symmetric group, so it
contains *every* transposition of the roots; and the set of all transpositions generates the
symmetric group by `Equiv.Perm.closure_isSwap`.  This is the exact hypothesis consumed by the
general transfer lemma `gal_swaps_of_range_swaps`. -/
theorem morseGeomPoly_range_contains_generating_swaps (n : ℕ) (hn : 2 ≤ n) :
    ∃ S : Set (Equiv.Perm ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField)),
      (∀ t ∈ S, t.IsSwap) ∧
      (∀ t ∈ S, t ∈ (Gal.galActionHom (morseGeomPoly n) (morseGeomPoly n).SplittingField).range) ∧
      Subgroup.closure S = ⊤ := by
  classical
  refine ⟨{σ | σ.IsSwap}, fun t ht ↦ ht, ?_, Equiv.Perm.closure_isSwap⟩
  intro t _
  rw [MonoidHom.range_eq_top.mpr (morseGeomPoly_galActionHom_surjective n hn)]
  exact Subgroup.mem_top t

open scoped Classical in
/-- **The geometric monodromy conclusion for `morseGeomPoly`.**

The geometric Galois group of `Xⁿ − X − T` over `ℚ̄(T)` admits a generating set each of whose
elements acts on the roots as a transposition.  Assembled from the isolated monodromy input
`morseGeomPoly_range_contains_generating_swaps` via the general transfer lemma
`gal_swaps_of_range_swaps`. -/
theorem morseGeomPoly_gal_generated_by_swaps (n : ℕ) (hn : 2 ≤ n) :
    ∃ S : Set (morseGeomPoly n).Gal,
      (∀ σ ∈ S,
        (Gal.galActionHom (morseGeomPoly n) (morseGeomPoly n).SplittingField σ).IsSwap) ∧
      Subgroup.closure S = ⊤ :=
  gal_swaps_of_range_swaps (morseGeomPoly n)
    (morseGeomPoly_range_contains_generating_swaps n hn)