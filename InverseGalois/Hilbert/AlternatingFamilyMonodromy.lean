/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.AlternatingFamilyDescent
import InverseGalois.Hilbert.AlternatingFamilyDisc
import InverseGalois.Resolvent.AlternatingResolvent
import InverseGalois.Resolvent.ResolventFamily
import InverseGalois.Hilbert.RegularExtension

/-!
# The explicit `Aₙ`-family (Serre §4.5) — monodromy decomposition

This file **decomposes** the deep absolute-irreducibility input
`AlternatingFamily.anResolvent_abs_irreducible` (a bare `sorry` in
`Hilbert/AlternatingFamilyAnalytic.lean`) into a chain of precise intermediate lemmas, a direct
mirror of the `Sₙ` reduction chain for the Morse family in `Resolvent/ResolventFamily.lean`
(`morseResolventFrac_irreducible` → `abs_irreducible_of_geometric_galois_surjective` →
`fullResolvent_abs_irreducible`).

The only structural difference from the `Sₙ` chain is that the relevant Galois orbit of the base
linear form `w₁ = ∑ᵢ i·xᵢ` has size `|Aₙ| = n!/2` (the degree of the descended resolvent `G`),
not `|Sₙ| = n!`.  Consequently the geometric-monodromy hypothesis is that the image of the
permutation representation `galActionHom` is *exactly the alternating group* (not full
surjectivity onto `Sₙ`).

This file sits *before* `AlternatingFamilyAnalytic` in the import graph: that file's
`anResolvent_abs_irreducible` is discharged by delegating to the `anResolvent_abs_irreducible'`
assembly below, so the single opaque monodromy `sorry` is replaced by the three tractable leaves
here (`serreAnOverFrac_separable`, `anResolventFrac_irreducible`, `an_geometric_galois_alternating`),
each a well-typed statement at which an automated prover can be aimed.
-/

open Polynomial

noncomputable section

namespace AlternatingFamily

open ResolventFamily AlternatingResolvent

open scoped Classical

/-- `Fact` instance: any polynomial splits in its own splitting field.  Re-declared `local` (as in
`ResolventFamily`) so that `galActionHom` statements over the splitting field typecheck. -/
local instance splitsInSplittingField (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

/-! ## Step 1–3: the base-changed family over `ℚ̄(T)` -/

/-- The concrete Serre `Aₙ`-family `serreAnFamily n` base-changed to the geometric base field
`ℚ̄(T)`.  Mirror of `ResolventFamily.morseOverFrac`. -/
def serreAnOverFrac (n : ℕ) : Polynomial (FractionRing (Polynomial (AlgebraicClosure ℚ))) :=
  (serreAnFamily n).map toClosureFrac

/-- `serreAnOverFrac n` is monic.  Mirror of `morseOverFrac_monic`. -/
theorem serreAnOverFrac_monic (n : ℕ) (hn : 2 ≤ n) : (serreAnOverFrac n).Monic :=
  (serreAnFamily_monic n hn).map _

/-- `serreAnOverFrac n` has degree `n`.  Mirror of `morseOverFrac_natDegree`. -/
theorem serreAnOverFrac_natDegree (n : ℕ) (hn : 2 ≤ n) :
    (serreAnOverFrac n).natDegree = n := by
  rw [serreAnOverFrac, Polynomial.natDegree_map_eq_of_injective toClosureFrac_injective]
  exact serreAnFamily_natDegree n hn

/-- **[algebraic leaf]** The value of `serreAnFamily n` at `X = 0` (its constant-in-`X`
coefficient) is `1/(n−1) + (−1)^{n/2}·T² ∈ ℚ[T]`. -/
theorem serreAnFamily_eval_zero (n : ℕ) (hn : 2 ≤ n) :
    (serreAnFamily n).eval 0
      = C (1 / ((n : ℚ) - 1)) + C ((-1 : ℚ) ^ (n / 2)) * X ^ 2 := by
  unfold serreAnFamily
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  rw [zero_pow (by omega : n ≠ 0), zero_pow (by omega : n - 1 ≠ 0)]
  ring

/-- **[algebraic leaf]** The value of `serreAnFamily n` at `X = 1` is `(−1)^{n/2}·T² ∈ ℚ[T]`
(the field identity `1 − n/(n−1) + 1/(n−1) = 0` kills the constant part). -/
theorem serreAnFamily_eval_one (n : ℕ) (hn : 2 ≤ n) :
    (serreAnFamily n).eval 1 = C ((-1 : ℚ) ^ (n / 2)) * X ^ 2 := by
  have hne : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hzero : (1 : ℚ) - (n : ℚ) / ((n : ℚ) - 1) + 1 / ((n : ℚ) - 1) = 0 := by
    field_simp; ring
  unfold serreAnFamily
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, one_pow, mul_one]
  rw [← C_1, ← C_sub, ← add_assoc, ← C_add, hzero, C_0, zero_add]

/-- **[algebraic leaf]** `serreAnFamily n |_{X=0}` is a nonzero element of `ℚ[T]` (its `T²`
coefficient is `(−1)^{n/2} ≠ 0`). -/
theorem serreAnFamily_eval_zero_ne (n : ℕ) (hn : 2 ≤ n) :
    (serreAnFamily n).eval 0 ≠ 0 := by
  rw [serreAnFamily_eval_zero n hn]
  intro h
  have hc := congr_arg (fun p => Polynomial.coeff p 2) h
  simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  norm_num at hc

/-- **[algebraic leaf]** `serreAnFamily n |_{X=1}` is a nonzero element of `ℚ[T]`. -/
theorem serreAnFamily_eval_one_ne (n : ℕ) (hn : 2 ≤ n) :
    (serreAnFamily n).eval 1 ≠ 0 := by
  rw [serreAnFamily_eval_one n hn]
  exact mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ (by norm_num))) (pow_ne_zero 2 X_ne_zero)

/-- **[separability leaf — proved]** The base-changed family is separable over `ℚ̄(T)`.

A common root `α` of `serreAnOverFrac n` and its derivative in `L = AlgebraicClosure ℚ̄(T)` must,
by `serreAnFamily_derivative` (`f' = n·X^{n-2}·(X−1)`), satisfy `α ∈ {0, 1}`.  But `f(0)` and
`f(1)` are the images under the injective `χ = (ℚ[T] → ℚ̄(T) → L)` of the *nonzero* polynomials
`serreAnFamily_eval_zero/one`, so `f(α) ≠ 0` — contradiction.  Mirror of `morseOverFrac_separable`
but cleaner: the critical points here are exactly `{0,1}` rather than an algebraic locus. -/
theorem serreAnOverFrac_separable (n : ℕ) (hn : 2 ≤ n) (_heven : Even n) :
    (serreAnOverFrac n).Separable := by
  refine IsCoprime.symm ?_
  by_contra h_not_coprime
  set K := FractionRing (Polynomial (AlgebraicClosure ℚ)) with hK
  set L := AlgebraicClosure K with hL
  set χ : Polynomial ℚ →+* L := (algebraMap K L).comp toClosureFrac with hχ
  -- A common root `α ∈ L` of `f` and `f'`.
  have h_common_root : ∃ α : L,
      eval α ((serreAnOverFrac n).map (algebraMap K L)) = 0 ∧
      eval α ((derivative (serreAnOverFrac n)).map (algebraMap K L)) = 0 := by
    contrapose! h_not_coprime
    apply isCoprime_of_irreducible_dvd
    · intro h
      have := serreAnOverFrac_natDegree n hn
      aesop
    · intro z hz hz' hz''
      obtain ⟨α, hα⟩ : ∃ α : L, eval α (z.map (algebraMap K L)) = 0 := by
        apply IsAlgClosed.exists_root
        rw [Polynomial.degree_map]
        exact ne_of_gt (Polynomial.degree_pos_of_irreducible hz)
      refine h_not_coprime α ?_ ?_
      · simpa [hα] using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
          (Polynomial.map_dvd (algebraMap K L) hz'') hα
      · simpa [hα] using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
          (Polynomial.map_dvd (algebraMap K L) hz') hα
  obtain ⟨α, hf, hf'⟩ := h_common_root
  -- Rewrite both evaluations as evaluations of `serreAnFamily n` mapped by `χ`.
  have hmap_f : (serreAnOverFrac n).map (algebraMap K L) = (serreAnFamily n).map χ := by
    rw [serreAnOverFrac, Polynomial.map_map, ← hχ]
  have hmap_f' : (derivative (serreAnOverFrac n)).map (algebraMap K L)
      = (derivative (serreAnFamily n)).map χ := by
    rw [serreAnOverFrac, Polynomial.derivative_map, Polynomial.map_map, ← hχ]
  rw [hmap_f] at hf
  rw [hmap_f', serreAnFamily_derivative n hn] at hf'
  -- From `f'(α) = 0`: `n·α^{n-2}·(α − 1) = 0`, hence `α = 0` or `α = 1`.
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_natCast, eval_sub, eval_mul, eval_pow, eval_X,
    Polynomial.eval_natCast, map_natCast] at hf'
  have hn0 : (n : L) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  have hr01 : α = 0 ∨ α = 1 := by
    have hfact : (n : L) * α ^ (n - 2) * (α - 1) = 0 := by
      have hm : n - 1 = (n - 2) + 1 := by omega
      rw [hm, pow_succ] at hf'
      linear_combination hf'
    rcases mul_eq_zero.mp hfact with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hn0
      · rcases eq_or_ne (n - 2) 0 with he | he
        · rw [he, pow_zero] at h'; exact absurd h' one_ne_zero
        · exact Or.inl ((pow_eq_zero_iff he).mp h')
    · exact Or.inr (by linear_combination h)
  -- `χ` is injective (composite of two injective maps).
  have hχinj : Function.Injective χ := by
    rw [hχ, RingHom.coe_comp]
    exact (algebraMap K L).injective.comp toClosureFrac_injective
  -- Plug `α ∈ {0,1}` into `f(α) = 0`; each forces a nonzero `ℚ[T]` element to vanish.
  rcases hr01 with h0 | h1
  · subst h0
    rw [Polynomial.eval_map, show (0 : L) = χ 0 from (map_zero χ).symm,
      eval₂_at_apply] at hf
    exact serreAnFamily_eval_zero_ne n hn (hχinj hf)
  · subst h1
    rw [Polynomial.eval_map, eval₂_at_one] at hf
    exact serreAnFamily_eval_one_ne n hn (hχinj (hf.trans (map_zero χ).symm))

/-! ## Step 5: the resolvent is irreducible over `ℚ̄(T)` given the geometric group is `Aₙ` -/

/-- **[orbit ↔ range, proved]** The `Aₙ`-analogue of `ResolventFamily.orbit_genForm_eq_range`.
If the Galois group acts on the root-enumeration `x` by *even* permutations (`hgal`) and every
even permutation is realised by an automorphism (`hsurj2`), then the Galois orbit of the base
form `w₁ = ∑ᵢ i·xᵢ` equals the set of `n!/2` forms `{w_σ : σ ∈ Aₙ}`. -/
theorem orbit_genForm_eq_alternating_range {n : ℕ} {L M : Type*} [Field L] [Field M] [Algebra L M]
    (x : Fin n → M)
    (hgal : ∀ γ : M ≃ₐ[L] M, ∃ σ : alternatingGroup (Fin n),
        ∀ i, γ (x i) = x ((σ : Equiv.Perm (Fin n)) i))
    (hsurj2 : ∀ σ : alternatingGroup (Fin n), ∃ γ : M ≃ₐ[L] M,
        ∀ i, γ (x i) = x ((σ : Equiv.Perm (Fin n)) i)) :
    MulAction.orbit (M ≃ₐ[L] M) (genForm n x 1)
      = Set.range (fun σ : alternatingGroup (Fin n) ↦ genForm n x (σ : Equiv.Perm (Fin n))) := by
  ext y
  simp only [MulAction.mem_orbit_iff, Set.mem_range]
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨σ, hσ⟩ := hgal γ
    exact ⟨σ, by simp [genForm, hσ]⟩
  · rintro ⟨σ, rfl⟩
    obtain ⟨γ, hγ⟩ := hsurj2 σ
    exact ⟨γ, by simp [genForm, hγ]⟩

/-- **Crux (irreducibility of the standard `Aₙ`-representation over `ℚ`, `sorry`).**

If `x : Fin n → M` are *distinct* elements of a characteristic-zero field and `c : Fin n → ℤ` is
a nonzero, sum-zero integer vector such that *every* even-permutation translate of the linear
relation `∑ⱼ cⱼ · xⱼ` vanishes, then we reach a contradiction.

Concretely, the `ℤ`-span of the `Aₙ`-translates of a nonzero sum-zero vector `c` contains a
vector supported on exactly two coordinates, say `m·(eᵢ - eⱼ)` with `m ≠ 0` and `i ≠ j`; the
corresponding relation reads `m·(xᵢ - xⱼ) = 0`, forcing `xᵢ = xⱼ`, against injectivity.  (For
`n ≤ 3` this is a finite check; for `n ≥ 4` it is the irreducibility of the `Aₙ` standard
representation over `ℚ`.)  This is the genuine remaining content of `genForm_alternating_injective`:
the fiddly `Aₙ`-symmetry reduction below discharges everything else. -/
lemma alternating_no_nontrivial_relation {n : ℕ} {M : Type*} [Field M] [CharZero M]
    (x : Fin n → M) (hxinj : Function.Injective x) (c : Fin n → ℤ)
    (hc : c ≠ 0) (hsum : ∑ j, c j = 0)
    (hrel : ∀ π : alternatingGroup (Fin n),
      ∑ k, (c (((π : Equiv.Perm (Fin n))⁻¹) k) : M) * x k = 0) : False := by
  sorry

/-- **[distinctness kernel — representation theory]** When every even permutation of the
roots is realised by a `K`-algebra automorphism of the splitting field (`hsurj2`), the `n!/2`
linear forms `σ ↦ ∑ᵢ i·x_(σ i)` (`σ ∈ Aₙ`) are pairwise distinct.

This is the genuine remaining content of `Aₙ`-irreducibility, and the point where the `Sₙ` proof
(`ResolventFamily.genForm_perm_injective`) does **not** transfer: that proof realises an arbitrary
transposition `(a b)` as a ring endomorphism, which is impossible here (a transposition is odd, so
it flips the square-root of the discriminant `δ ∈ K` and is not a `K`-automorphism).  The
alternating analogue instead rests on the irreducibility of the standard representation of `Aₙ`
over `ℚ`: a collision `∑_j c_j x_j = 0` with `c` a permutation-difference (so `∑ c_j = 0`,
`c ≠ 0`) would make the relation module a nonzero `Aₙ`-submodule of the standard representation,
forcing all `x_j` equal — contradicting injectivity of `x`. -/
theorem genForm_alternating_injective {n : ℕ} {K M : Type*} [Field K] [Field M] [Algebra K M]
    [CharZero M] (x : Fin n → M) (hxinj : Function.Injective x)
    (hsurj2 : ∀ σ : alternatingGroup (Fin n), ∃ γ : M ≃ₐ[K] M,
        ∀ i, γ (x i) = x ((σ : Equiv.Perm (Fin n)) i)) :
    Function.Injective (fun σ : alternatingGroup (Fin n) ↦ genForm n x (σ : Equiv.Perm (Fin n))) := by
  intro σ τ hστ
  simp only at hστ
  -- The permutation whose triviality we must establish.
  set ρ' : Equiv.Perm (Fin n) := (τ : Equiv.Perm (Fin n))⁻¹ * (σ : Equiv.Perm (Fin n))
    with hρ'def
  -- It suffices to show `ρ' = 1`.
  suffices hfin : ρ' = 1 by
    rw [hρ'def] at hfin
    exact (Subtype.ext (inv_mul_eq_one.mp hfin)).symm
  -- Transport `w_σ = w_τ` by the automorphism realising `τ⁻¹`, turning it into `w_ρ' = w_1`.
  obtain ⟨γ, hγ⟩ := hsurj2 τ⁻¹
  simp only [InvMemClass.coe_inv] at hγ
  have e1 : γ (genForm n x (σ : Equiv.Perm (Fin n))) = genForm n x ρ' := by
    unfold genForm
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, map_natCast, hγ ((σ : Equiv.Perm (Fin n)) i), hρ'def, Equiv.Perm.mul_apply]
  have e2 : γ (genForm n x (τ : Equiv.Perm (Fin n))) = genForm n x 1 := by
    unfold genForm
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, map_natCast, hγ ((τ : Equiv.Perm (Fin n)) i)]
    simp [Equiv.Perm.one_apply]
  have hρ : genForm n x ρ' = genForm n x 1 := by rw [← e1, hστ, e2]
  -- Arithmetic form of `w_ρ' = w_1`.
  have hρ0 : ∑ i : Fin n, ((i : ℕ) : M) * x (ρ' i) = ∑ i : Fin n, ((i : ℕ) : M) * x i := by
    have h := hρ
    unfold genForm at h
    simpa [Equiv.Perm.one_apply] using h
  -- Reindex the left sum to expose `ρ'⁻¹`.
  have hreindex : ∑ i : Fin n, ((i : ℕ) : M) * x (ρ' i) =
      ∑ i : Fin n, (((ρ'⁻¹ i : Fin n) : ℕ) : M) * x i := by
    rw [← Equiv.sum_comp ρ'⁻¹ (fun i => ((i : ℕ) : M) * x (ρ' i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
  -- The integer relation vector.
  set c : Fin n → ℤ := fun k => ((ρ'⁻¹ k : Fin n).val : ℤ) - (k.val : ℤ) with hcdef
  -- Base relation `∑ⱼ cⱼ · xⱼ = 0`.
  have hbase : ∑ k : Fin n, ((c k : ℤ) : M) * x k = 0 := by
    have key : ∑ k : Fin n, (((ρ'⁻¹ k : Fin n) : ℕ) : M) * x k
        = ∑ k : Fin n, ((k : ℕ) : M) * x k := by
      rw [← hreindex]; exact hρ0
    simp only [hcdef]
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib, key, sub_self]
  -- `c` is sum-zero.
  have hsum : ∑ j, c j = 0 := by
    simp only [hcdef, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp ρ'⁻¹ (fun k => (k.val : ℤ))]
    exact sub_self _
  -- Prove `ρ' = 1` by contradiction using the crux lemma.
  by_contra hρne
  -- `c ≠ 0`, otherwise `ρ'⁻¹ = 1` hence `ρ' = 1`.
  have hc : c ≠ 0 := by
    intro h0
    apply hρne
    have hinv : ρ'⁻¹ = 1 := by
      ext k
      have hk := congrFun h0 k
      simp only [hcdef, Pi.zero_apply, sub_eq_zero] at hk
      exact_mod_cast hk
    have : ρ' = (ρ'⁻¹)⁻¹ := (inv_inv ρ').symm
    rw [this, hinv, inv_one]
  -- Every `Aₙ`-translate of the base relation vanishes.
  have hrel : ∀ π : alternatingGroup (Fin n),
      ∑ k, (c (((π : Equiv.Perm (Fin n))⁻¹) k) : M) * x k = 0 := by
    intro π
    obtain ⟨γπ, hγπ⟩ := hsurj2 π
    -- Apply `γπ` to the base relation.
    have hg : ∑ k : Fin n, ((c k : ℤ) : M) * x ((π : Equiv.Perm (Fin n)) k) = 0 := by
      have := congrArg γπ hbase
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_mul, map_intCast, hγπ k]
    calc ∑ k : Fin n, (c (((π : Equiv.Perm (Fin n))⁻¹) k) : M) * x k
        = ∑ k : Fin n, ((c ((π : Equiv.Perm (Fin n))⁻¹ k) : ℤ) : M)
            * x ((π : Equiv.Perm (Fin n)) ((π : Equiv.Perm (Fin n))⁻¹ k)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      _ = ∑ k : Fin n, ((c k : ℤ) : M) * x ((π : Equiv.Perm (Fin n)) k) :=
          Equiv.sum_comp ((π : Equiv.Perm (Fin n))⁻¹)
            (fun k => ((c k : ℤ) : M) * x ((π : Equiv.Perm (Fin n)) k))
      _ = 0 := hg
  exact alternating_no_nontrivial_relation x hxinj c hc hsum hrel

/-- **[root enumeration with `Aₙ`-Galois transport, `sorry`]** The `Aₙ`-analogue of
`ResolventFamily.morse_root_enum` bundled with the `IsAltResolvent` coupling.  Over the splitting
field `M` of `serreAnOverFrac n` there is an enumeration `x : Fin n → M` of the roots such that:
* `x` is injective (`serreAnOverFrac n` is separable);
* the base-changed resolvent factors as `G.map ev = altResolventProduct n x` (the coupling `hG`
  applied at `ev`, with `x` re-oriented into the coset picked out by `IsAltResolvent`);
* the Galois group acts on `x` by **even** permutations (parity from the square-discriminant
  certificate: any `K`-automorphism fixes `δ = √disc ∈ K`, hence realises `σ` with `sign σ = 1`);
* every even permutation of `x` is realised by an automorphism (from `hAlt`: the range of the
  permutation representation is exactly the alternating group on the root set).

The two `Galois`-transport clauses are the `Aₙ`-refinement of the `Sₙ` enumeration; the parity
clause is where the square-discriminant hypothesis (`Even n`) enters. -/
theorem an_root_enum (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (G : Polynomial (Polynomial ℚ)) (_hGmonic : G.Monic)
    (hG : IsAltResolvent n (serreAnFamily n) G)
    (hAlt : (Gal.galActionHom (serreAnOverFrac n) (serreAnOverFrac n).SplittingField).range
      = alternatingGroup ((serreAnOverFrac n).rootSet (serreAnOverFrac n).SplittingField)) :
    ∃ x : Fin n → (serreAnOverFrac n).SplittingField, Function.Injective x ∧
      G.map ((algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ)))
          (serreAnOverFrac n).SplittingField).comp toClosureFrac)
        = altResolventProduct n x ∧
      (∀ γ : (serreAnOverFrac n).SplittingField
          ≃ₐ[FractionRing (Polynomial (AlgebraicClosure ℚ))] (serreAnOverFrac n).SplittingField,
        ∃ σ : alternatingGroup (Fin n), ∀ i, γ (x i) = x ((σ : Equiv.Perm (Fin n)) i)) ∧
      (∀ σ : alternatingGroup (Fin n),
        ∃ γ : (serreAnOverFrac n).SplittingField
          ≃ₐ[FractionRing (Polynomial (AlgebraicClosure ℚ))] (serreAnOverFrac n).SplittingField,
        ∀ i, γ (x i) = x ((σ : Equiv.Perm (Fin n)) i)) := by
  set K := FractionRing (Polynomial (AlgebraicClosure ℚ)) with hK
  set M := (serreAnOverFrac n).SplittingField with hM
  set ev := (algebraMap K M).comp toClosureFrac with hev_def
  -- `serreAnOverFrac n = (serreAnFamily n).map toClosureFrac` by definition, so mapping the
  -- integral family by `ev` agrees with mapping the base-changed family into `M`.
  have hmapev : (serreAnFamily n).map ev = (serreAnOverFrac n).map (algebraMap K M) := by
    rw [hev_def, ← Polynomial.map_map]; rfl
  -- Step 1: degree.
  have hdeg : ((serreAnFamily n).map ev).natDegree = n := by
    rw [hmapev, Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
    · exact serreAnOverFrac_natDegree n hn
    · rw [(serreAnOverFrac_monic n hn).leadingCoeff, map_one]; exact one_ne_zero
  have hsplit_f : ((serreAnOverFrac n).map (algebraMap K M)).Splits :=
    SplittingField.splits (serreAnOverFrac n)
  -- Step 2: an initial root enumeration.
  obtain ⟨x0, hx0⟩ : ∃ x0 : Fin n → M,
      ((serreAnFamily n).map ev).roots = Finset.univ.val.map x0 := by
    have hcard : Multiset.card ((serreAnFamily n).map ev).roots = n := by
      have hsp : ((serreAnFamily n).map ev).Splits := by rw [hmapev]; exact hsplit_f
      rw [Polynomial.splits_iff_card_roots.mp hsp, hdeg]
    obtain ⟨x0, hx0⟩ := ResolventConstruction.exists_fin_map_eq _ n hcard
    exact ⟨x0, hx0.symm⟩
  -- Step 3: couple with `IsAltResolvent` to re-orient into the alternating coset.
  obtain ⟨x, hxroots, hGx⟩ := hG ev x0 hdeg hx0
  -- Separability transported to `M`.
  have hsep : ((serreAnFamily n).map ev).Separable := by
    rw [hmapev]; exact (serreAnOverFrac_separable n hn heven).map
  -- Step 4: injectivity of `x`.
  have hxinj : Function.Injective x := by
    have hnd : ((serreAnFamily n).map ev).roots.Nodup := Polynomial.nodup_roots hsep
    rw [hxroots] at hnd
    intro i j hij
    exact Multiset.inj_on_of_nodup_map hnd i (by simp) j (by simp) hij
  -- Step 5: each `x i` lies in the root set of `serreAnOverFrac n` over `M`.
  have hxmem : ∀ i, x i ∈ (serreAnOverFrac n).rootSet M := by
    intro i
    rw [Polynomial.mem_rootSet]
    refine ⟨(serreAnOverFrac_monic n hn).ne_zero, ?_⟩
    have hmemroots : x i ∈ ((serreAnFamily n).map ev).roots := by
      rw [hxroots]; exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    have hroot : eval (x i) ((serreAnFamily n).map ev) = 0 :=
      (Polynomial.mem_roots'.mp hmemroots).2
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← hmapev]
    exact hroot
  -- Step 6: the bijection `v : Fin n ≃ rootSet` with `(v i : M) = x i`.
  have hcardrs : Fintype.card ((serreAnOverFrac n).rootSet M) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree (serreAnOverFrac_separable n hn heven) hsplit_f,
      serreAnOverFrac_natDegree n hn]
  have hbij : Function.Bijective (fun i : Fin n => (⟨x i, hxmem i⟩ : (serreAnOverFrac n).rootSet M)) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
    · intro i j hij; exact hxinj (Subtype.ext_iff.mp hij)
    · rw [Fintype.card_fin, hcardrs]
  set v := Equiv.ofBijective _ hbij with hv_def
  have hvx : ∀ i, (v i : M) = x i := fun i => rfl
  -- Step 7: the half-discriminant is nonzero (Vandermonde).
  have h_ne : discElem (fun i => (v i : M)) ≠ 0 := by
    unfold discElem
    rw [← Matrix.det_vandermonde, Ne, Matrix.det_vandermonde_eq_zero_iff]
    push_neg
    exact fun i j h => (Subtype.val_injective.comp v.injective) h
  -- Step 8: the discriminant is a square in `K`.
  have h_sq : ∃ d : K, discSq (fun i => (v i : M)) = (algebraMap K M d) ^ 2 := by
    refine ⟨toClosureFrac (serreAnDeltaPoly n), ?_⟩
    have hvx' : (fun i => (v i : M)) = x := funext hvx
    rw [discSq, hvx', serreAnFamily_discSq_general n hn ev x hdeg hxroots,
      ← serreAnDeltaPoly_sq n heven, map_pow, hev_def, RingHom.comp_apply]
  -- Step 9: parity clause — every automorphism acts by an even permutation.
  have hgal_alt := gal_le_alternating_of_disc_sq (serreAnOverFrac n)
    (serreAnOverFrac_monic n hn).ne_zero v h_sq h_ne
  refine ⟨x, hxinj, hGx, ?_, ?_⟩
  · intro γ
    obtain ⟨π, hπ, hsign⟩ := hgal_alt γ
    refine ⟨⟨π, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, fun i => ?_⟩
    show γ (x i) = x (π i)
    rw [← hvx i, ← hvx (π i)]
    exact hπ i
  -- Step 10: realization clause — every even permutation is induced by an automorphism.
  · intro σ
    set πrs : Equiv.Perm ((serreAnOverFrac n).rootSet M) :=
      v.permCongr (σ : Equiv.Perm (Fin n)) with hπrs
    have hπrs_sign : Equiv.Perm.sign πrs = 1 := by
      rw [hπrs, Equiv.Perm.sign_permCongr]
      exact Equiv.Perm.mem_alternatingGroup.mp σ.2
    have hmem : πrs ∈ (Gal.galActionHom (serreAnOverFrac n) M).range := by
      rw [hAlt]; exact Equiv.Perm.mem_alternatingGroup.mpr hπrs_sign
    obtain ⟨φ, hφ⟩ := MonoidHom.mem_range.mp hmem
    obtain ⟨ϕ, hϕ⟩ := Gal.restrict_surjective (serreAnOverFrac n) M φ
    have key : ∀ i, (πrs (v i) : M) = x ((σ : Equiv.Perm (Fin n)) i) := by
      intro i
      rw [hπrs, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      exact hvx _
    refine ⟨ϕ, fun i => ?_⟩
    have hr := Gal.galActionHom_restrict (p := serreAnOverFrac n) (E := M) ϕ (v i)
    rw [hϕ, hφ] at hr
    rw [hvx i, key i] at hr
    exact hr.symm

/-- **[monodromy core — geometric algebra, proved from three leaves]** The base-changed resolvent
`G.map toClosureFrac ∈ ℚ̄(T)[Y]` is irreducible, **given** that the image of the permutation
representation of the geometric Galois group of `serreAnFamily n` over `ℚ̄(T)` is exactly the
alternating group on the roots.

Mirror of `ResolventFamily.morseResolventFrac_irreducible`, with the orbit-cardinality
computation adjusted from `|Sₙ| = n!` to `|Aₙ| = n!/2` (`altResolventProduct_natDegree`).  Over
the splitting field `M`, the coupling `IsAltResolvent` writes `G` as `∏_{σ ∈ Aₙ}(Y − w_{σ})` for
distinct roots `x` (`an_root_enum`); when the geometric group acts as exactly `Aₙ`, the Galois
orbit of `w₁` is the full set of `n!/2` distinct forms `{w_σ : σ ∈ Aₙ}`
(`orbit_genForm_eq_alternating_range` + `genForm_alternating_injective`), whose cardinality equals
`(G.map toClosureFrac).natDegree`.  Apply `Monic.irreducible_of_galois_orbit_card`.

The hypothesis is stated as *range equals the alternating group on the root set* (not full
surjectivity), because the resolvent `G` has degree `n!/2`: if the geometric group were all of
`Sₙ` the orbit would have size `n!` and `G` would not be irreducible. -/
theorem anResolventFrac_irreducible (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (G : Polynomial (Polynomial ℚ)) (hGmonic : G.Monic)
    (hG : IsAltResolvent n (serreAnFamily n) G)
    (hAlt : (Gal.galActionHom (serreAnOverFrac n) (serreAnOverFrac n).SplittingField).range
      = alternatingGroup ((serreAnOverFrac n).rootSet (serreAnOverFrac n).SplittingField)) :
    Irreducible (G.map toClosureFrac) := by
  obtain ⟨x, hxinj, hGx, hgal, hsurj2⟩ := an_root_enum n hn heven G hGmonic hG hAlt
  set ev := (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ)))
    (serreAnOverFrac n).SplittingField).comp toClosureFrac with hev_def
  haveI : IsGalois (FractionRing (Polynomial (AlgebraicClosure ℚ)))
      (serreAnOverFrac n).SplittingField :=
    IsGalois.of_separable_splitting_field (serreAnOverFrac_separable n hn heven)
  have hev_deg : (G.map ev).natDegree = G.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _
      (by rw [hGmonic.leadingCoeff, map_one]; exact one_ne_zero)
  have hdegG : (G.map toClosureFrac).natDegree = n.factorial / 2 := by
    have e1 : (G.map toClosureFrac).natDegree = G.natDegree :=
      natDegree_map_of_leadingCoeff_ne_zero _
        (by rw [hGmonic.leadingCoeff, map_one]; exact one_ne_zero)
    rw [e1, ← hev_deg, hGx, altResolventProduct_natDegree n hn]
  have hw : (aeval (genForm n x 1)) (G.map toClosureFrac) = 0 := by
    have h1 : (G.map toClosureFrac).map
        (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ)))
          (serreAnOverFrac n).SplittingField) = altResolventProduct n x := by
      rw [Polynomial.map_map]; exact hGx
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, h1]
    exact altResolventProduct_isRoot_genForm_one n x
  haveI hNT : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  refine Monic.irreducible_of_galois_orbit_card (hGmonic.map toClosureFrac) hw ?_
  rw [orbit_genForm_eq_alternating_range x hgal hsurj2,
      Nat.card_range_of_injective (genForm_alternating_injective x hxinj hsurj2),
      Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin, hdegG]

/-! ## Step 6: reduction to absolute (geometric) irreducibility over `ℚ̄` -/

/-- **[reduction — Gauss, proved]** If the geometric Galois group of `serreAnFamily n` over
`ℚ̄(T)` is exactly the alternating group, then the descended resolvent `G` stays irreducible after
base change to `ℚ̄`.

Mirror of `ResolventFamily.abs_irreducible_of_geometric_galois_surjective`: `GK := G.map (ℚ → ℚ̄)`
is monic, so by Gauss (`Monic.irreducible_iff_irreducible_map_fraction_map`) it is irreducible iff
its image over `ℚ̄(T)` is, and `Polynomial.map_map` identifies that image with `G.map toClosureFrac`;
close via `anResolventFrac_irreducible`. -/
theorem abs_irreducible_of_geometric_galois_alternating (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (G : Polynomial (Polynomial ℚ)) (hGmonic : G.Monic)
    (hG : IsAltResolvent n (serreAnFamily n) G)
    (hAlt : (Gal.galActionHom (serreAnOverFrac n) (serreAnOverFrac n).SplittingField).range
      = alternatingGroup ((serreAnOverFrac n).rootSet (serreAnOverFrac n).SplittingField)) :
    Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) := by
  have hmonicGK : (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).Monic := hGmonic.map _
  rw [hmonicGK.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (Polynomial (AlgebraicClosure ℚ)))]
  have heq : (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).map
      (algebraMap (Polynomial (AlgebraicClosure ℚ))
        (FractionRing (Polynomial (AlgebraicClosure ℚ))))
      = G.map toClosureFrac := by
    rw [Polynomial.map_map]
    rfl
  rw [heq]
  exact anResolventFrac_irreducible n hn heven G hGmonic hG hAlt

/-! ## Step 7: the deep geometric monodromy input -/

/-- **[parity half — proved]** The image of the permutation representation of the geometric Galois
group of `serreAnFamily n` over `ℚ̄(T)` is **contained in** the alternating group on the roots.

This is the "easy" (`≤`) half of `an_geometric_galois_alternating`: the square-discriminant
certificate (`serreAnDeltaPoly n` squares to the closed-form discriminant, `serreAnDeltaPoly_sq`,
using `Even n`) makes `√disc ∈ K`, so every `K`-automorphism fixes it and hence permutes the roots
evenly (`gal_le_alternating_of_disc_sq`).  The reverse inclusion (`≥`, the genuine
3-cycle/transitivity content) is the remaining `sorry`. -/
theorem an_geometric_le_alternating (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    (Gal.galActionHom (serreAnOverFrac n) (serreAnOverFrac n).SplittingField).range
      ≤ alternatingGroup ((serreAnOverFrac n).rootSet (serreAnOverFrac n).SplittingField) := by
  set K := FractionRing (Polynomial (AlgebraicClosure ℚ)) with hK
  set M := (serreAnOverFrac n).SplittingField with hM
  set ev := (algebraMap K M).comp toClosureFrac with hev_def
  have hmapev : (serreAnFamily n).map ev = (serreAnOverFrac n).map (algebraMap K M) := by
    rw [hev_def, ← Polynomial.map_map]; rfl
  have hdeg : ((serreAnFamily n).map ev).natDegree = n := by
    rw [hmapev, Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
    · exact serreAnOverFrac_natDegree n hn
    · rw [(serreAnOverFrac_monic n hn).leadingCoeff, map_one]; exact one_ne_zero
  have hsplit_f : ((serreAnOverFrac n).map (algebraMap K M)).Splits :=
    SplittingField.splits (serreAnOverFrac n)
  -- Root enumeration of `f` over `M` (independent of the `IsAltResolvent` coupling).
  obtain ⟨x, hxroots⟩ : ∃ x : Fin n → M,
      ((serreAnFamily n).map ev).roots = Finset.univ.val.map x := by
    have hcard : Multiset.card ((serreAnFamily n).map ev).roots = n := by
      have hsp : ((serreAnFamily n).map ev).Splits := by rw [hmapev]; exact hsplit_f
      rw [Polynomial.splits_iff_card_roots.mp hsp, hdeg]
    obtain ⟨x, hx⟩ := ResolventConstruction.exists_fin_map_eq _ n hcard
    exact ⟨x, hx.symm⟩
  have hsep : ((serreAnFamily n).map ev).Separable := by
    rw [hmapev]; exact (serreAnOverFrac_separable n hn heven).map
  have hxinj : Function.Injective x := by
    have hnd : ((serreAnFamily n).map ev).roots.Nodup := Polynomial.nodup_roots hsep
    rw [hxroots] at hnd
    intro i j hij
    exact Multiset.inj_on_of_nodup_map hnd i (by simp) j (by simp) hij
  have hxmem : ∀ i, x i ∈ (serreAnOverFrac n).rootSet M := by
    intro i
    rw [Polynomial.mem_rootSet]
    refine ⟨(serreAnOverFrac_monic n hn).ne_zero, ?_⟩
    have hmemroots : x i ∈ ((serreAnFamily n).map ev).roots := by
      rw [hxroots]; exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    have hroot : eval (x i) ((serreAnFamily n).map ev) = 0 :=
      (Polynomial.mem_roots'.mp hmemroots).2
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← hmapev]
    exact hroot
  have hcardrs : Fintype.card ((serreAnOverFrac n).rootSet M) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree (serreAnOverFrac_separable n hn heven) hsplit_f,
      serreAnOverFrac_natDegree n hn]
  have hbij : Function.Bijective
      (fun i : Fin n => (⟨x i, hxmem i⟩ : (serreAnOverFrac n).rootSet M)) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
    · intro i j hij; exact hxinj (Subtype.ext_iff.mp hij)
    · rw [Fintype.card_fin, hcardrs]
  set v := Equiv.ofBijective _ hbij with hv_def
  have hvx : ∀ i, (v i : M) = x i := fun i => rfl
  have h_ne : discElem (fun i => (v i : M)) ≠ 0 := by
    unfold discElem
    rw [← Matrix.det_vandermonde, Ne, Matrix.det_vandermonde_eq_zero_iff]
    push_neg
    exact fun i j h => (Subtype.val_injective.comp v.injective) h
  have h_sq : ∃ d : K, discSq (fun i => (v i : M)) = (algebraMap K M d) ^ 2 := by
    refine ⟨toClosureFrac (serreAnDeltaPoly n), ?_⟩
    have hvx' : (fun i => (v i : M)) = x := funext hvx
    rw [discSq, hvx', serreAnFamily_discSq_general n hn ev x hdeg hxroots,
      ← serreAnDeltaPoly_sq n heven, map_pow, hev_def, RingHom.comp_apply]
  have hpar := gal_le_alternating_of_disc_sq (serreAnOverFrac n)
    (serreAnOverFrac_monic n hn).ne_zero v h_sq h_ne
  -- Each element of the range is even.
  intro y hy
  obtain ⟨ψ, rfl⟩ := MonoidHom.mem_range.mp hy
  obtain ⟨ϕ, hϕ⟩ := Gal.restrict_surjective (serreAnOverFrac n) M ψ
  obtain ⟨π, hπ, hsign⟩ := hpar ϕ
  rw [Equiv.Perm.mem_alternatingGroup]
  have hperm : Gal.galActionHom (serreAnOverFrac n) M ψ = v.permCongr π := by
    refine Equiv.ext (fun r => ?_)
    obtain ⟨i, rfl⟩ := v.surjective r
    apply Subtype.ext
    have hr := Gal.galActionHom_restrict (p := serreAnOverFrac n) (E := M) ϕ (v i)
    rw [hϕ] at hr
    rw [hr, hπ i, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [hperm, Equiv.Perm.sign_permCongr]
  exact hsign

/-- **[residual leaf — the sole remaining `sorry` of `serreAnOverFrac_irreducible`]**
`g := Xⁿ − (n/(n−1))X^{n-1} + 1/(n−1)` is **not** a perfect square in `ℚ̄[X]`.

Math content: `g' = n·X^{n-2}(X − 1)`, so the only possible multiple root of `g` is `X = 1`
(note `g(0) = 1/(n−1) ≠ 0`).  But `g ≠ (X−1)ⁿ` because their `X^{n-1}`-coefficients (`−n/(n−1)`
vs. `−n`) differ for `n ≥ 3`; hence `g` has a root `≠ 1`, which is therefore simple, so `g` is
not a square.

WARNING — this statement is **FALSE at `n = 2`**: there `g = X² − 2X + 1 = (X − 1)²`, a square.
(Correspondingly, `serreAnOverFrac_irreducible` itself is false at `n = 2`: `serreAnFamily 2 =
(X−1)² − T² = (X−1−T)(X−1+T)` is reducible.)  So the whole geometric-irreducibility chain below
requires `3 ≤ n`; with the `Even n` hypothesis this is effectively `n ≥ 4`, and the only caller
(`exists_alternating_resolvent_family`, invoked solely for `n ≥ 4`) supplies it. -/
theorem serreAn_g_not_isSquare (n : ℕ) (hn : 3 ≤ n) :
    ¬ IsSquare (X ^ n
        - C (algebraMap ℚ (AlgebraicClosure ℚ) ((n : ℚ) / ((n : ℚ) - 1))) * X ^ (n - 1)
        + C (algebraMap ℚ (AlgebraicClosure ℚ) (1 / ((n : ℚ) - 1)))
        : Polynomial (AlgebraicClosure ℚ)) := by
  set R := AlgebraicClosure ℚ with hR
  set φ := algebraMap ℚ R with hφ
  have hn1 : (n : ℚ) - 1 ≠ 0 := by
    have : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  set a₁ : R := φ ((n : ℚ) / ((n : ℚ) - 1)) with ha1def
  set a₀ : R := φ (1 / ((n : ℚ) - 1)) with ha0def
  set g : R[X] := X ^ n - C a₁ * X ^ (n - 1) + C a₀ with hg
  have hn0 : n ≠ 0 := by omega
  have hn10 : n - 1 ≠ 0 := by omega
  have h1n : 1 ≤ n := by omega
  have hcast : (↑(n - 1) : R) = φ ((n : ℚ) - 1) := by
    rw [hφ, ← map_natCast (algebraMap ℚ R) (n - 1), Nat.cast_sub h1n, Nat.cast_one]
  have ha1mul : a₁ * (↑(n - 1) : R) = (n : R) := by
    rw [ha1def, hcast, ← map_mul,
      show ((n : ℚ) / ((n : ℚ) - 1)) * ((n : ℚ) - 1) = (n : ℚ) by field_simp]
    exact map_natCast (algebraMap ℚ R) n
  have ha0ne : a₀ ≠ 0 := by
    rw [ha0def]
    have hx : (1 : ℚ) / ((n : ℚ) - 1) ≠ 0 := div_ne_zero one_ne_zero hn1
    exact (map_ne_zero_iff (algebraMap ℚ R) (FaithfulSMul.algebraMap_injective ℚ R)).mpr hx
  have hmonic : g.Monic := by
    rw [hg]; monicity!
    rw [if_neg (show ¬ (n = n - 1) by omega), if_neg (show ¬ (n = 0) by omega)]; ring
  have hdeg : g.natDegree = n := by
    rw [hg]; compute_degree!
    rw [if_neg (show ¬ (n = n - 1) by omega), if_neg (show ¬ (n = 0) by omega)]; simp
  have hg_ne : g ≠ 0 := hmonic.ne_zero
  have hg0 : g.eval 0 = a₀ := by
    rw [hg]; simp [zero_pow hn0, zero_pow hn10]
  have hDerivRoot : ∀ r : R, (derivative g).eval r = (↑n : R) * r ^ (n - 2) * (r - 1) := by
    intro r
    have hrpow : r ^ (n - 1) = r ^ (n - 2) * r := by rw [← pow_succ]; congr 1; omega
    have e1 : n - 1 - 1 = n - 2 := by omega
    rw [hg]
    simp only [derivative_add, derivative_sub, derivative_C_mul, derivative_X_pow, derivative_C,
      eval_sub, eval_mul, eval_C, eval_pow, eval_X, add_zero]
    rw [e1, hrpow, show a₁ * (↑(n - 1) * r ^ (n - 2)) = (a₁ * ↑(n - 1)) * r ^ (n - 2) by ring,
      ha1mul]
    ring
  have hsplit : g.Splits := IsAlgClosed.splits g
  have hcard : g.roots.card = n := (splits_iff_card_roots.mp hsplit).trans hdeg
  have hne_n : (↑n : R) ≠ 0 := by
    simp only [Ne, Nat.cast_eq_zero]; omega
  rintro ⟨h, hh⟩
  have hh_ne : h ≠ 0 := fun h0 => hg_ne (by rw [hh, h0, mul_zero])
  have hroots1 : ∀ r ∈ g.roots, r = 1 := by
    intro r hr
    have hIsRoot : g.IsRoot r := (mem_roots'.mp hr).2
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, IsRoot, hg0] at hIsRoot
      exact ha0ne hIsRoot
    have hhr : h.IsRoot r := by
      have hsq : h.eval r * h.eval r = 0 := by
        have := hIsRoot; rw [IsRoot, hh, eval_mul] at this; exact this
      exact mul_self_eq_zero.mp hsq
    have hmh : 1 ≤ h.rootMultiplicity r := (rootMultiplicity_pos hh_ne).mpr hhr
    have hmg : g.rootMultiplicity r = h.rootMultiplicity r + h.rootMultiplicity r := by
      conv_lhs => rw [hh]
      exact rootMultiplicity_mul (by rw [← hh]; exact hg_ne)
    have hderivmult : (derivative g).rootMultiplicity r = g.rootMultiplicity r - 1 :=
      derivative_rootMultiplicity_of_root hIsRoot
    have hderiv_pos : 0 < (derivative g).rootMultiplicity r := by omega
    have hderivroot : (derivative g).eval r = 0 := (rootMultiplicity_pos'.mp hderiv_pos).2
    have hform := hDerivRoot r
    rw [hderivroot] at hform
    have hzero : (↑n : R) * r ^ (n - 2) * (r - 1) = 0 := hform.symm
    rcases mul_eq_zero.mp hzero with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hne_n
      · exact absurd h'' (pow_ne_zero _ hr0)
    · exact sub_eq_zero.mp h'
  have hroots_eq : g.roots = Multiset.replicate n 1 := by
    have := Multiset.eq_replicate_card.mpr hroots1
    rwa [hcard] at this
  have hgpow : g = (X - C (1 : R)) ^ n := by
    have h1 := hsplit.eq_prod_roots_of_monic hmonic
    rw [hroots_eq, Multiset.map_replicate, Multiset.prod_replicate] at h1
    exact h1
  have hd0 : (derivative g).eval 0 = 0 := by
    rw [hDerivRoot]; simp [zero_pow (show n - 2 ≠ 0 by omega)]
  have hd0' : (derivative g).eval 0 ≠ 0 := by
    rw [hgpow, derivative_pow]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero]
    rw [mul_one, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_C]
    exact mul_ne_zero hne_n (pow_ne_zero _ (by norm_num))
  exact hd0' hd0

/-- **[geometric irreducibility over `ℚ̄`, proved from `serreAn_g_not_isSquare`]** The Serre family
base-changed to `ℚ̄` is irreducible in `ℚ̄[T][X]`.

Proof: swap the variables (`Polynomial.Bivariate.swap`) so the family becomes quadratic in `T`,
namely `C(C u)·T² + C g = C(C u)·(T² − C a)` with `u = (−1)^{n/2}` (a unit, `u² = 1`) and
`a = −(C u · g)`.  The monic quadratic `T² − C a` is irreducible over `ℚ̄[X]` iff (Gauss) it is
over `Frac(ℚ̄[X])`, and there `X² − C a` is Kummer-irreducible (`p = 2`) since `a` is not a square
in `Frac(ℚ̄[X])` — a descent (`ℚ̄[X]` integrally closed) reducing to `g` not a square in `ℚ̄[X]`,
which is `serreAn_g_not_isSquare`. -/
theorem serreAnFamily_geom_irr (n : ℕ) (hn : 3 ≤ n) (heven : Even n) :
    Irreducible ((serreAnFamily n).map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) := by
  have hnsq := serreAn_g_not_isSquare n hn
  set R := AlgebraicClosure ℚ
  set φ := algebraMap ℚ R
  set c1 := φ ((n : ℚ) / ((n : ℚ) - 1)) with hc1
  set c0 := φ (1 / ((n : ℚ) - 1)) with hc0
  set u : R := (φ (-1)) ^ (n / 2) with hu
  set g : Polynomial R := X ^ n - C c1 * X ^ (n - 1) + C c0 with hg
  set a : Polynomial R := -(C u * g) with ha
  refine (MulEquiv.irreducible_iff Polynomial.Bivariate.swap
    (x := (serreAnFamily n).map (mapRingHom φ))).mp ?_
  have hswap : Polynomial.Bivariate.swap ((serreAnFamily n).map (mapRingHom φ))
      = C (C u) * X ^ 2 + C g := by
    unfold serreAnFamily
    rw [hu, hg]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, coe_mapRingHom, Polynomial.map_C, map_C, map_add, map_sub, map_mul,
      map_pow, Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_C_C,
      Polynomial.Bivariate.swap_X]
    ring
  rw [hswap]
  set M : Polynomial (Polynomial R) := X ^ 2 - C a with hM
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← pow_mul]
    have hnn : n / 2 * 2 = n := by obtain ⟨k, hk⟩ := heven; omega
    rw [hnn, ← map_pow, Even.neg_one_pow heven, map_one]
  have hune : u ≠ 0 := by
    intro h; rw [h, zero_pow (by norm_num)] at hu2; exact zero_ne_one hu2
  have hcancel : (C u : Polynomial R) * -(C u * g) = -g := by
    rw [mul_neg, ← mul_assoc, ← C_mul, ← pow_two, hu2, C_1, one_mul]
  have hQM : C (C u) * X ^ 2 + C g = C (C u) * M := by
    rw [hM, ha, mul_sub, ← C_mul, hcancel, map_neg, sub_neg_eq_add]
  have hunit : IsUnit (C (C u) : Polynomial (Polynomial R)) := by
    apply isUnit_C.mpr; apply isUnit_C.mpr
    exact IsUnit.of_mul_eq_one u (by rw [← sq]; exact hu2)
  rw [hQM]
  have hassoc : Associated M (C (C u) * M) := by
    rw [mul_comm]; exact (associated_mul_unit_left M _ hunit).symm
  refine hassoc.irreducible_iff.mp ?_
  have hMmonic : M.Monic := by rw [hM]; exact monic_X_pow_sub_C a (by norm_num)
  rw [hMmonic.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (Polynomial R))]
  have hmapM : M.map (algebraMap (Polynomial R) (FractionRing (Polynomial R)))
      = X ^ 2 - C (algebraMap (Polynomial R) (FractionRing (Polynomial R)) a) := by
    rw [hM, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [hmapM]
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b hb
  have hint : IsIntegral (Polynomial R) (b ^ 2) := by
    rw [hb]; exact isIntegral_algebraMap
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (n := 2) (by norm_num) hint
  have hinj := IsFractionRing.injective (Polynomial R) (FractionRing (Polynomial R))
  have hasq : a = s ^ 2 := by
    apply hinj; rw [← hb, map_pow, hs]
  obtain ⟨w, hw⟩ : ∃ w : R, w ^ 2 = -u := by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-u) (n := 2) (by norm_num); exact ⟨w, hw⟩
  have hwne : w ≠ 0 := by
    rintro rfl; rw [zero_pow (by norm_num)] at hw; exact hune (neg_eq_zero.mp hw.symm)
  have hcw : IsUnit (C w : Polynomial R) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hwne)
  have ha2 : (C w) ^ 2 * g = -(C u * g) := by rw [← C_pow, hw, map_neg, neg_mul]
  have hkey : (C w) ^ 2 * g = s ^ 2 := ha2.trans (ha.symm.trans hasq)
  have hinv : (↑hcw.unit⁻¹ : Polynomial R) * (C w) = 1 := hcw.val_inv_mul
  apply hnsq
  refine ⟨(↑hcw.unit⁻¹ : Polynomial R) * s, ?_⟩
  have hthis : ((↑hcw.unit⁻¹ : Polynomial R) * s) ^ 2 = (↑hcw.unit⁻¹) ^ 2 * s ^ 2 := by ring
  rw [← hkey] at hthis
  rw [show (↑hcw.unit⁻¹ : Polynomial R) ^ 2 * ((C w) ^ 2 * g)
        = ((↑hcw.unit⁻¹) * C w) ^ 2 * g from by ring, hinv, one_pow, one_mul] at hthis
  rw [← hthis]; ring

/-- **[transitivity leaf — geometric irreducibility, proved]** The base-changed Serre family
`serreAnOverFrac n` is **irreducible** over `ℚ̄(T)`.  This is the geometric irreducibility of the
family — equivalently, the geometric Galois group acts *transitively* on the roots
(`an_geometric_isPretransitive`).  Proved from `serreAnFamily_geom_irr` by Gauss's lemma
(`Monic.irreducible_iff_irreducible_map_fraction_map`), transferring irreducibility from
`ℚ̄[T][X]` to `ℚ̄(T)[X]`.  Requires `3 ≤ n` (false at `n = 2`; see `serreAn_g_not_isSquare`). -/
theorem serreAnOverFrac_irreducible (n : ℕ) (hn : 3 ≤ n) (heven : Even n) :
    Irreducible (serreAnOverFrac n) := by
  have hmonic : ((serreAnFamily n).map
      (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).Monic :=
    (serreAnFamily_monic n (by omega)).map _
  have heq : serreAnOverFrac n = ((serreAnFamily n).map
      (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).map
        (algebraMap (Polynomial (AlgebraicClosure ℚ))
          (FractionRing (Polynomial (AlgebraicClosure ℚ)))) := by
    rw [serreAnOverFrac, Polynomial.map_map]; rfl
  rw [heq, ← hmonic.irreducible_iff_irreducible_map_fraction_map]
  exact serreAnFamily_geom_irr n hn heven

/-- **[transitivity — proved from `serreAnOverFrac_irreducible`]** The geometric Galois group of
`serreAnFamily n` acts **transitively** on the roots.  Immediate from irreducibility of
`serreAnOverFrac n` via Mathlib's `Polynomial.Gal.galAction_isPretransitive`, transported along the
surjection `p.Gal ↠ (galActionHom).range`. -/
theorem an_geometric_isPretransitive (n : ℕ) (hn : 3 ≤ n) (heven : Even n) :
    MulAction.IsPretransitive
      (Gal.galActionHom (serreAnOverFrac n) (serreAnOverFrac n).SplittingField).range
      ((serreAnOverFrac n).rootSet (serreAnOverFrac n).SplittingField) := by
  haveI htrans : MulAction.IsPretransitive (serreAnOverFrac n).Gal
      ((serreAnOverFrac n).rootSet (serreAnOverFrac n).SplittingField) :=
    Gal.galAction_isPretransitive (p := serreAnOverFrac n)
      (E := (serreAnOverFrac n).SplittingField) (serreAnOverFrac_irreducible n hn heven)
  refine ⟨fun x y => ?_⟩
  obtain ⟨ϕ, hϕ⟩ := MulAction.exists_smul_eq (serreAnOverFrac n).Gal x y
  exact ⟨⟨Gal.galActionHom (serreAnOverFrac n) _ ϕ, MonoidHom.mem_range.mpr ⟨ϕ, rfl⟩⟩, hϕ⟩

/-- **[monodromy leaf — geometric primitivity, `sorry`]** The geometric Galois group of
`serreAnFamily n` acts **preprimitively** on the roots.

Built from the transitive part (`an_geometric_isPretransitive`, now reduced to the geometric
irreducibility leaf `serreAnOverFrac_irreducible`) and the remaining *primitivity* content: the
only blocks are trivial, i.e. there is no intermediate field strictly between `ℚ̄(T)` and
`ℚ̄(T)(α)` for a single root `α`.  Together with a 3-cycle in the group
(`an_geometric_isThreeCycle_mem`) and the even-permutation bound (`an_geometric_le_alternating`) it
forces the group to be exactly `Aₙ` via
`Equiv.Perm.eq_alternatingGroup_of_isPreprimitive_of_isThreeCycle`. -/
theorem an_geometric_isPreprimitive (n : ℕ) (hn : 3 ≤ n) (heven : Even n) :
    MulAction.IsPreprimitive
      (Gal.galActionHom (serreAnOverFrac n) (serreAnOverFrac n).SplittingField).range
      ((serreAnOverFrac n).rootSet (serreAnOverFrac n).SplittingField) where
  toIsPretransitive := an_geometric_isPretransitive n hn heven
  isTrivialBlock_of_isBlock := by
    sorry

/-- **[monodromy leaf — geometric, `sorry`; the genuine deep content]** The geometric Galois group
of `serreAnFamily n` over `ℚ̄(T)` contains a **3-cycle** on the roots.

This is the analytic heart of the `Aₙ` (Mestre/Serre) construction: after the square-discriminant
substitution the finite inertia generator at the single ramified value of the family is a 3-cycle
(vs. a transposition for the un-substituted `Sₙ` family).  It is the `Aₙ`-analogue of the
transposition-inertia computation in the `Sₙ` `MorseSwap`/`NewtonPuiseux` stack, and the only input
to `an_geometric_galois_alternating` that is not now reduced to previously-proved facts. -/
theorem an_geometric_isThreeCycle_mem (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    ∃ g : Equiv.Perm ((serreAnOverFrac n).rootSet (serreAnOverFrac n).SplittingField),
      g.IsThreeCycle ∧
      g ∈ (Gal.galActionHom (serreAnOverFrac n) (serreAnOverFrac n).SplittingField).range := by
  sorry

/-- **[monodromy core — geometric, proved from three inputs]** The image of the permutation
representation of the geometric Galois group of `serreAnFamily n` over `ℚ̄(T)` is **exactly the
alternating group** on the roots.

`Aₙ`-analogue of `ResolventFamily.morse_geometric_galois_surjective`, now assembled from
`Equiv.Perm.eq_alternatingGroup_of_isPreprimitive_of_isThreeCycle`: preprimitivity
(`an_geometric_isPreprimitive`), a 3-cycle in the group (`an_geometric_isThreeCycle_mem` — the
analytic Newton–Puiseux content), and containment in the alternating group
(`an_geometric_le_alternating`, proved from the square-discriminant certificate). -/
theorem an_geometric_galois_alternating (n : ℕ) (hn : 3 ≤ n) (heven : Even n) :
    (Gal.galActionHom (serreAnOverFrac n) (serreAnOverFrac n).SplittingField).range
      = alternatingGroup ((serreAnOverFrac n).rootSet (serreAnOverFrac n).SplittingField) := by
  obtain ⟨g, h3g, hg⟩ := an_geometric_isThreeCycle_mem n (by omega) heven
  exact Equiv.Perm.eq_alternatingGroup_of_isPreprimitive_of_isThreeCycle
    (an_geometric_isPreprimitive n hn heven) h3g hg
    (an_geometric_le_alternating n (by omega) heven)

/-! ## Assembly: absolute irreducibility of the descended resolvent -/

/-- **[assembly, proved from Steps 6 + 7]** The descended resolvent `G` of `serreAnFamily n` is
absolutely irreducible.  This has exactly the statement of
`AlternatingFamily.anResolvent_abs_irreducible` (the target `sorry`), reconstructed here from the
decomposition: `abs_irreducible_of_geometric_galois_alternating` fed the deep geometric input
`an_geometric_galois_alternating`.  Mirror of `ResolventFamily.fullResolvent_abs_irreducible`. -/
theorem anResolvent_abs_irreducible' (n : ℕ) (hn : 3 ≤ n) (heven : Even n)
    (G : Polynomial (Polynomial ℚ)) (hGmonic : G.Monic)
    (hG : IsAltResolvent n (serreAnFamily n) G) :
    Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :=
  abs_irreducible_of_geometric_galois_alternating n (by omega) heven G hGmonic hG
    (an_geometric_galois_alternating n hn heven)

end AlternatingFamily

end
