/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.KummerCover
import InverseGalois.Rigidity.RET.Pi1.AbsoluteGaloisQuotient

/-!
# Kummer theory for several radicals, and abelian geometric covers

This module proves the Riemann Existence conclusion (`IsGeometricGaloisCover`) for every finite
**abelian** group, outright and by algebra alone.

The mechanism is Kummer theory with several radicals.  Over a field `K` containing a primitive
`N`-th root of unity, adjoining `N`-th roots `yᵢ` of elements `bᵢ ∈ K` produces a Galois extension
whose group maps to `(μ_N)ʳ` by `σ ↦ (σ yᵢ / yᵢ)`; the map is *onto* as soon as the `bᵢ` are
multiplicatively independent modulo `N`-th powers.  Duality for finite abelian groups turns a
proper subgroup of `(μ_N)ʳ` into a nontrivial character killing it, and such a character exhibits a
product `∏ yᵢ^{eᵢ}` fixed by the whole Galois group — hence in `K`, contradicting independence.

Over `ℚ̄(T)` the radicands are taken to be the linear polynomials `T - cᵢ` at distinct points `cᵢ`,
whose independence modulo `N`-th powers is unique factorization in `ℚ̄[T]`.  The resulting cover of
`ℙ¹` is branched over the `cᵢ` and `∞`.

## Main results

* `Rigidity.RET.kummerHom` — the monodromy homomorphism `Gal(L/K) →* (μ_N)ʳ`, `σ ↦ (σ yᵢ / yᵢ)`.
* `Rigidity.RET.kummerHom_surjective` — it is surjective when the radicands are independent modulo
  `N`-th powers.
* `Rigidity.RET.eq_zero_of_prod_linear_isPow` — distinct linear polynomials are independent modulo
  `N`-th powers in `k(T)`.
* `Rigidity.RET.isGeometricGaloisCover_of_commGroup` — every finite abelian group is realized by a
  geometric Galois cover of `ℙ¹_ℚ̄`.
-/

namespace Rigidity.RET

open Polynomial

section Kummer

variable {K L : Type} [Field K] [Field L] [Algebra K L] {N : ℕ} [NeZero N]
  {ζ : K} (hζ : IsPrimitiveRoot ζ N)

include hζ in
/-- Every `N`-th root of unity of `L` lies in `K`, so is fixed by every `K`-automorphism. -/
theorem apply_eq_self_of_pow_eq_one (σ : L ≃ₐ[K] L) {c : L} (hc : c ^ N = 1) : σ c = c := by
  obtain ⟨k, -, rfl⟩ :=
    (hζ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one hc
  rw [map_pow, AlgEquiv.commutes]

variable {ι : Type} [Fintype ι] {y : ι → L} {b : ι → K}
  (hb : ∀ i, b i ≠ 0) (hy : ∀ i, y i ^ N = algebraMap K L (b i))

omit [Fintype ι] in
include hb hy in
theorem radical_ne_zero (i : ι) : y i ≠ 0 := by
  intro h
  refine hb i ((map_eq_zero_iff _ (algebraMap K L).injective).mp ?_)
  rw [← hy i, h, zero_pow (NeZero.ne N)]

omit [NeZero N] [Fintype ι] in
include hb hy in
theorem radical_ratio_pow_eq_one (σ : L ≃ₐ[K] L) (i : ι) : (σ (y i) / y i) ^ N = 1 := by
  rw [div_pow, ← map_pow, hy i, AlgEquiv.commutes,
    div_self ((map_ne_zero_iff _ (algebraMap K L).injective).mpr (hb i))]

/-- **The Kummer monodromy homomorphism.**  An automorphism `σ` of `L / K` multiplies each radical
`yᵢ` by an `N`-th root of unity; recording those roots of unity is a group homomorphism, because
the roots of unity themselves lie in `K` and are therefore fixed. -/
noncomputable def kummerHom :
    (L ≃ₐ[K] L) →* (ι → rootsOfUnity N L) where
  toFun σ i := rootsOfUnity.mkOfPowEq (σ (y i) / y i) (radical_ratio_pow_eq_one hb hy σ i)
  map_one' := by
    funext i
    refine Subtype.ext (Units.ext ?_)
    rw [rootsOfUnity.coe_mkOfPowEq]
    simp [div_self (radical_ne_zero hb hy i)]
  map_mul' σ τ := by
    funext i
    refine Subtype.ext (Units.ext ?_)
    have hne : y i ≠ 0 := radical_ne_zero hb hy i
    have hfix : σ (τ (y i) / y i) = τ (y i) / y i :=
      apply_eq_self_of_pow_eq_one hζ σ (radical_ratio_pow_eq_one hb hy τ i)
    have hστ : σ (τ (y i)) = (τ (y i) / y i) * σ (y i) := by
      conv_lhs => rw [show τ (y i) = τ (y i) / y i * y i from (div_mul_cancel₀ _ hne).symm]
      rw [map_mul, hfix]
    simp only [rootsOfUnity.coe_mkOfPowEq, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul,
      AlgEquiv.mul_apply, hστ]
    field_simp

omit [Fintype ι] in
@[simp]
theorem kummerHom_apply (σ : L ≃ₐ[K] L) (i : ι) :
    ((kummerHom hζ hb hy σ i : Lˣ) : L) = σ (y i) / y i :=
  rootsOfUnity.coe_mkOfPowEq _

/-- A primitive `N`-th root of unity generates the whole group of `N`-th roots of unity. -/
private theorem exists_pow_eq_of_isPrimitiveRoot {u : rootsOfUnity N L}
    (hu : IsPrimitiveRoot ((u : Lˣ) : L) N) (t : rootsOfUnity N L) : ∃ a : ℕ, t = u ^ a := by
  have h : ((t : Lˣ)) ^ N = 1 := (mem_rootsOfUnity _ _).mp t.2
  have ht : (((t : Lˣ) : L)) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  obtain ⟨a, -, ha⟩ := hu.eq_pow_of_pow_eq_one ht
  refine ⟨a, Subtype.ext (Units.ext ?_)⟩
  push_cast
  exact ha.symm

/-- **Surjectivity of the Kummer monodromy homomorphism.**

If no nontrivial product `∏ bᵢ^{eᵢ}` with exponents below `N` is an `N`-th power in `K`, then every
prescribed tuple of `N`-th roots of unity is realized by an automorphism of `L / K`.

The proof is duality for finite abelian groups: were the image a proper subgroup, a character of
`(μ_N)ʳ` killing it and not killing some element would produce exponents `eᵢ`, not all zero, for
which `∏ yᵢ^{eᵢ}` is fixed by the whole Galois group — hence lies in `K`, making `∏ bᵢ^{eᵢ}` an
`N`-th power there. -/
theorem kummerHom_surjective [FiniteDimensional K L] [IsGalois K L]
    (hind : ∀ e : ι → ℕ, (∀ i, e i < N) → (∃ c : K, ∏ i, b i ^ e i = c ^ N) → ∀ i, e i = 0) :
    Function.Surjective (kummerHom hζ hb hy) := by
  classical
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) N :=
    hζ.map_of_injective (algebraMap K L).injective
  set ζM : rootsOfUnity N L :=
    rootsOfUnity.mkOfPowEq (algebraMap K L ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one]) with hζMdef
  have hζMcoe : ((ζM : Lˣ) : L) = algebraMap K L ζ := rootsOfUnity.coe_mkOfPowEq _
  haveI : HasEnoughRootsOfUnity L N := ⟨⟨_, hζL⟩, rootsOfUnity.isCyclic L N⟩
  -- every element of the target has exponent dividing `N`
  have hpowN : ∀ m : ι → rootsOfUnity N L, m ^ N = 1 := by
    intro m
    funext i
    show m i ^ N = 1
    have h := (m i).2
    rw [mem_rootsOfUnity] at h
    exact Subtype.ext (by push_cast; exact_mod_cast h)
  by_contra hns
  simp only [Function.Surjective, not_forall] at hns
  obtain ⟨m₀, hm₀⟩ := hns
  set H := (kummerHom hζ hb hy).range with hHdef
  have hm₀H : m₀ ∉ H := fun h => hm₀ (MonoidHom.mem_range.mp h)
  -- duality: a character of the quotient not killing `m₀`
  have hexp : Monoid.exponent ((ι → rootsOfUnity N L) ⧸ H) ∣ N :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (by
      intro x
      induction x using QuotientGroup.induction_on with
      | _ m =>
        have h := map_pow (QuotientGroup.mk' H) m N
        rw [hpowN m, map_one] at h
        exact h.symm)
  haveI : HasEnoughRootsOfUnity L (Monoid.exponent ((ι → rootsOfUnity N L) ⧸ H)) :=
    HasEnoughRootsOfUnity.of_dvd L hexp
  have hne1 : (QuotientGroup.mk m₀ : (ι → rootsOfUnity N L) ⧸ H) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hm₀H
  obtain ⟨χ', hχ'⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    ((ι → rootsOfUnity N L) ⧸ H) L hne1
  set χ : (ι → rootsOfUnity N L) →* Lˣ := χ'.comp (QuotientGroup.mk' H) with hχdef
  -- the exponents cut out by the character
  have hprim : ∀ i, ((χ (Pi.mulSingle i ζM) : Lˣ) : L) ^ N = 1 := by
    intro i
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hpowN _, map_one, Units.val_one]
  choose e heN he using fun i => hζL.eq_pow_of_pow_eq_one (hprim i)
  -- the character is the monomial `m ↦ ∏ mᵢ^{eᵢ}`
  let ψ : (ι → rootsOfUnity N L) →* Lˣ :=
    { toFun := fun m => ∏ i, ((m i : Lˣ)) ^ e i
      map_one' := by simp
      map_mul' := fun m n => by
        simp only [Pi.mul_apply, Subgroup.coe_mul, mul_pow, Finset.prod_mul_distrib] }
  have hχψ : χ = ψ := by
    refine MonoidHom.functions_ext Lˣ χ ψ fun j t => ?_
    obtain ⟨a, rfl⟩ := exists_pow_eq_of_isPrimitiveRoot (u := ζM) (hζMcoe ▸ hζL) t
    have hRHS : ψ (Pi.mulSingle j (ζM ^ a)) = ((ζM : Lˣ) ^ a) ^ e j := by
      show (∏ i, (((Pi.mulSingle j (ζM ^ a) : ι → rootsOfUnity N L) i : Lˣ)) ^ e i) = _
      rw [Finset.prod_eq_single j (fun i _ hij => by rw [Pi.mulSingle_eq_of_ne hij]; simp)
        (fun h => absurd (Finset.mem_univ j) h), Pi.mulSingle_eq_same]
      push_cast
      rfl
    rw [hRHS, Pi.mulSingle_pow, map_pow]
    refine Units.ext ?_
    push_cast
    rw [← he j, hζMcoe, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have key : ∀ m : ι → rootsOfUnity N L,
      ((χ m : Lˣ) : L) = ∏ i, ((m i : Lˣ) : L) ^ e i := by
    intro m
    rw [hχψ]
    show ((∏ i, ((m i : Lˣ)) ^ e i : Lˣ) : L) = _
    push_cast
    rfl
  -- the corresponding monomial in the radicals is Galois-fixed, hence lies in `K`
  set w : L := ∏ i, y i ^ e i with hwdef
  have hfix : ∀ σ : L ≃ₐ[K] L, σ w = w := by
    intro σ
    have h1 : ((χ (kummerHom hζ hb hy σ) : Lˣ) : L) = 1 := by
      have hmem : (QuotientGroup.mk (kummerHom hζ hb hy σ) :
          (ι → rootsOfUnity N L) ⧸ H) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨σ, rfl⟩
      rw [hχdef]
      simp [hmem]
    rw [key] at h1
    simp only [kummerHom_apply] at h1
    calc σ w = ∏ i, (σ (y i)) ^ e i := by rw [hwdef, map_prod]; simp only [map_pow]
      _ = (∏ i, (σ (y i) / y i) ^ e i) * ∏ i, y i ^ e i := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun i _ => by
            rw [← mul_pow, div_mul_cancel₀ _ (radical_ne_zero hb hy i)]
      _ = w := by rw [h1, one_mul, hwdef]
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed w).mpr hfix
  have hcN : ∏ i, b i ^ e i = c ^ N := by
    refine (algebraMap K L).injective ?_
    rw [map_pow, hc, hwdef, ← Finset.prod_pow, map_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [map_pow, ← hy i, ← pow_mul, ← pow_mul, Nat.mul_comm]
  -- so all exponents vanish, and the character is trivial after all
  have hzero := hind e heN ⟨c, hcN⟩
  refine hχ' ?_
  have hk := key m₀
  simp only [hzero, pow_zero, Finset.prod_const_one] at hk
  rw [hχdef] at hk
  exact Units.ext (by simpa using hk)

end Kummer

section Independence

/-- The multiplicity of a root of a power. -/
private theorem rootMultiplicity_pow {R : Type*} [CommRing R] [IsDomain R] {p : R[X]} (hp : p ≠ 0)
    (x : R) (n : ℕ) : rootMultiplicity x (p ^ n) = n * rootMultiplicity x p := by
  induction n with
  | zero => simp only [pow_zero, Nat.zero_mul]; exact rootMultiplicity_eq_zero (by simp)
  | succ n ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp), ih, Nat.succ_mul]

variable {k : Type*} [Field k]

/-- **Distinct linear polynomials are independent modulo `N`-th powers in `k(T)`.**

If a product `∏ (T - cᵢ)^{eᵢ}` over distinct points `cᵢ` is an `N`-th power in the rational
function field, then `N` divides every exponent: comparing the multiplicity of the root `c_j` on
both sides of the cleared-denominator identity shows `N ∣ e_j`. -/
theorem dvd_of_prod_linear_isPow {ι : Type} [Fintype ι] {N : ℕ} [NeZero N] {c : ι → k}
    (hc : Function.Injective c) (e : ι → ℕ)
    (h : ∃ f : RatFunc k, ∏ i, (RatFunc.X - RatFunc.C (c i)) ^ e i = f ^ N) :
    ∀ i, N ∣ e i := by
  classical
  obtain ⟨f, hf⟩ := h
  intro j
  set P : k[X] := ∏ i, (X - C (c i)) ^ e i with hPdef
  have hPne : P ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_sub_C_ne_zero (c i))
  have hmapP : algebraMap k[X] (RatFunc k) P = ∏ i, (RatFunc.X - RatFunc.C (c i)) ^ e i := by
    rw [hPdef, map_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [map_pow, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hinj : Function.Injective (algebraMap k[X] (RatFunc k)) :=
    IsFractionRing.injective k[X] (RatFunc k)
  have hfne : f ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hf
    exact hPne (hinj (by rw [hmapP, hf, map_zero]))
  have hden0 : algebraMap k[X] (RatFunc k) f.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.denom_ne_zero f)
  have hnum : f * algebraMap k[X] (RatFunc k) f.denom = algebraMap k[X] (RatFunc k) f.num :=
    ((div_eq_iff hden0).mp (RatFunc.num_div_denom f)).symm
  have hpoly : P * f.denom ^ N = f.num ^ N := by
    refine hinj ?_
    rw [map_mul, map_pow, map_pow, hmapP, hf, ← hnum, mul_pow]
  -- compare multiplicities of the root `c j`
  have hsplit : P = (X - C (c j)) ^ e j * ∏ i ∈ Finset.univ.erase j, (X - C (c i)) ^ e i :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  have hQ0 : rootMultiplicity (c j) (∏ i ∈ Finset.univ.erase j, (X - C (c i)) ^ e i) = 0 := by
    refine rootMultiplicity_eq_zero ?_
    simp only [IsRoot, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr fun i hi =>
      pow_ne_zero _ (sub_ne_zero_of_ne (hc.ne (Ne.symm (Finset.mem_erase.mp hi).1)))
  have hPm : rootMultiplicity (c j) P = e j := by
    conv_lhs => rw [hsplit]
    rw [rootMultiplicity_mul (hsplit ▸ hPne), rootMultiplicity_X_sub_C_pow, hQ0, add_zero]
  have hmain := congrArg (rootMultiplicity (c j)) hpoly
  rw [rootMultiplicity_mul (mul_ne_zero hPne (pow_ne_zero N (RatFunc.denom_ne_zero f))), hPm,
    rootMultiplicity_pow (RatFunc.denom_ne_zero f), rootMultiplicity_pow
      (RatFunc.num_ne_zero hfne)] at hmain
  rw [Nat.eq_sub_of_add_eq hmain]
  exact Nat.dvd_sub (dvd_mul_right N _) (dvd_mul_right N _)

/-- **Distinct linear polynomials are independent modulo `N`-th powers in `k(T)`**, in the form
used by Kummer duality: exponents below `N` whose product is an `N`-th power all vanish. -/
theorem eq_zero_of_prod_linear_isPow {ι : Type} [Fintype ι] {N : ℕ} [NeZero N] {c : ι → k}
    (hc : Function.Injective c) (e : ι → ℕ) (heN : ∀ i, e i < N)
    (h : ∃ f : RatFunc k, ∏ i, (RatFunc.X - RatFunc.C (c i)) ^ e i = f ^ N) :
    ∀ i, e i = 0 :=
  fun i => Nat.eq_zero_of_dvd_of_lt (dvd_of_prod_linear_isPow hc e h i) (heN i)

end Independence

section Abelian

/-- **Every finite abelian group is realized by a geometric Galois cover of `ℙ¹_ℚ̄`.**

Write `A ≃* ∏ ZMod (nᵢ)` and put `N = ∏ nᵢ`.  Adjoining to `ℚ̄(T)` an `N`-th root of `T - cᵢ` for
distinct points `cᵢ ∈ ℚ̄`, one for each factor, gives a finite Galois extension whose group is all
of `(μ_N)ʳ` — surjectivity is Kummer duality (`kummerHom_surjective`) fed by the independence of
the `T - cᵢ` modulo `N`-th powers (`eq_zero_of_prod_linear_isPow`).  Projecting `(μ_N)ʳ` onto
`∏ ZMod (nᵢ)` and passing to the fixed field of the kernel realizes `A` itself.

This is the conclusion of the Riemann Existence Theorem for abelian groups, obtained by pure
algebra: the cover is branched over the `cᵢ` and `∞`. -/
theorem isGeometricGaloisCover_of_commGroup (A : Type) [CommGroup A] [Finite A] :
    IsGeometricGaloisCover A := by
  classical
  obtain ⟨ι, hιfin, n, hn1, ⟨eA⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  set N : ℕ := ∏ i, n i with hNdef
  have hNpos : 0 < N := Finset.prod_pos fun i _ => lt_trans one_pos (hn1 i)
  haveI : NeZero N := ⟨hNpos.ne'⟩
  have hdvd : ∀ i, n i ∣ N := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  -- a primitive `N`-th root of unity in `ℚ̄ ⊆ ℚ̄(T)`
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hNpos.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  have hζ : IsPrimitiveRoot (algebraMap (AlgebraicClosure ℚ) GeomFunctionField ζ₀) N :=
    hζ₀.map_of_injective (algebraMap (AlgebraicClosure ℚ) GeomFunctionField).injective
  -- distinct branch points and the radicands `T - cᵢ`
  set c : ι → AlgebraicClosure ℚ := fun i => ((Fintype.equivFin ι i : ℕ) : AlgebraicClosure ℚ)
    with hcdef
  have hc : Function.Injective c := fun i j hij =>
    (Fintype.equivFin ι).injective (Fin.val_injective (Nat.cast_injective hij))
  set b : ι → GeomFunctionField := fun i => RatFunc.X - RatFunc.C (c i) with hbdef
  have hbmap : ∀ i, b i =
      algebraMap (AlgebraicClosure ℚ)[X] GeomFunctionField (X - C (c i)) := fun i => by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hb : ∀ i, b i ≠ 0 := fun i => by
    rw [hbmap i]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_sub_C_ne_zero (c i))
  -- the field generated by all the `N`-th roots
  set P : GeomFunctionField[X] := ∏ i, (X ^ N - C (b i)) with hPdef
  have hPne : P ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (monic_X_pow_sub_C (b i) (NeZero.ne N)).ne_zero
  set L := P.SplittingField with hLdef
  haveI : FiniteDimensional GeomFunctionField L := IsSplittingField.finiteDimensional L P
  haveI : Normal GeomFunctionField L := Normal.of_isSplittingField P
  haveI : PerfectField GeomFunctionField := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic GeomFunctionField L := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable GeomFunctionField L :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois GeomFunctionField L := ⟨⟩
  have hroot : ∀ i, ∃ x : L, x ^ N = algebraMap GeomFunctionField L (b i) := by
    intro i
    have hsplit : ((X ^ N - C (b i)).map (algebraMap GeomFunctionField L)).Splits :=
      Polynomial.Splits.of_dvd (IsSplittingField.splits L P)
        ((Polynomial.map_ne_zero_iff (algebraMap GeomFunctionField L).injective).mpr hPne)
        (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
    obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero (by
      rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, degree_X_pow_sub_C hNpos]
      exact_mod_cast hNpos.ne')
    refine ⟨x, ?_⟩
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero] at hx
    exact hx
  choose y hy using hroot
  -- Kummer duality: the monodromy is all of `(μ_N)^ι`
  have hkummer : Function.Surjective (kummerHom hζ hb hy) :=
    kummerHom_surjective hζ hb hy fun e heN hpow =>
      eq_zero_of_prod_linear_isPow hc e heN (by simpa only [hbdef] using hpow)
  -- project `(μ_N)^ι` onto `∏ ZMod (nᵢ)`
  haveI : HasEnoughRootsOfUnity L N :=
    ⟨⟨_, hζ.map_of_injective (algebraMap GeomFunctionField L).injective⟩,
      rootsOfUnity.isCyclic L N⟩
  have hcard : Nat.card (rootsOfUnity N L) = Nat.card (Multiplicative (ZMod N)) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity L N]
    exact (Nat.card_zmod N).symm
  let eμ : rootsOfUnity N L ≃* Multiplicative (ZMod N) := mulEquivOfCyclicCardEq hcard
  let ψ : ∀ i, rootsOfUnity N L →* Multiplicative (ZMod (n i)) := fun i =>
    (AddMonoidHom.toMultiplicative (ZMod.castHom (hdvd i) (ZMod (n i))).toAddMonoidHom).comp
      eμ.toMonoidHom
  have hψ : ∀ i, Function.Surjective (ψ i) := fun i t => by
    obtain ⟨x, hx⟩ := ZMod.castHom_surjective (hdvd i) (Multiplicative.toAdd t)
    exact ⟨eμ.symm (Multiplicative.ofAdd x), by simpa [ψ] using congrArg Multiplicative.ofAdd hx⟩
  let Φ : (ι → rootsOfUnity N L) →* (∀ i, Multiplicative (ZMod (n i))) :=
    { toFun := fun m i => ψ i (m i)
      map_one' := by funext i; simp
      map_mul' := fun m m' => by funext i; simp }
  have hΦ : Function.Surjective Φ := fun t => by
    choose g hg using fun i => hψ i (t i)
    exact ⟨g, funext hg⟩
  -- assemble the surjection onto `A` and pass to the fixed field of its kernel
  exact (isGeometricGaloisCover_iff_isGaloisGroupOver A).mpr
    (isGaloisGroupOver_of_surjective
      ((eA.symm.toMonoidHom.comp Φ).comp (kummerHom hζ hb hy))
      (eA.symm.surjective.comp (hΦ.comp hkummer)))

end Abelian

end Rigidity.RET
