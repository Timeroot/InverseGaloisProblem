/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.AlternatingFamilyOdd
import InverseGalois.Hilbert.AlternatingFamilyOddDescent
import InverseGalois.Hilbert.AlternatingFamilyMonodromy

/-!
# The explicit `Aₙ`-family (Serre §4.5) — **odd-`n`** geometric monodromy descent

This file is the **odd mirror** of `Hilbert/AlternatingFamilyMonodromy.lean`.  It decomposes the
odd-`n` absolute-irreducibility input `anResolvent_abs_irreducible_odd` into the same chain of
precise intermediate lemmas
used for even `n`, with `serreAnFamily ↦ serreAnFamilyOdd`, `Even n ↦ Odd n`, and the second
critical point `1 ↦ (k − U²)` (`k = (−1)^{(n−1)/2}·n`).

The family-agnostic representation-theory lemmas
(`orbit_genForm_eq_alternating_range`, `genForm_alternating_injective`) are reused verbatim from the
even monodromy file; only the family-specific inputs (base change to `ℚ̄(U)`, separability,
square-discriminant certificate, root enumeration, and the deep geometric-monodromy `= Aₙ` input)
are re-derived here for the odd family.
-/

open Polynomial

noncomputable section

namespace AlternatingFamily

open ResolventFamily AlternatingResolvent SerreBaseCover

open scoped Classical

/-- `Fact` instance: any polynomial splits in its own splitting field.  Re-declared `local` (as in
`ResolventFamily`) so that `galActionHom` statements over the splitting field typecheck. -/
local instance splitsInSplittingFieldOdd (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

/-! ## The base-changed odd family over `ℚ̄(U)` -/

/-- Serre's explicit odd-`n` `Aₙ`-family `serreAnFamilyOdd n` base-changed to the geometric base
field `ℚ̄(U)`.  Odd mirror of `serreAnOverFrac`. -/
def serreAnOverFracOdd (n : ℕ) : Polynomial (FractionRing (Polynomial (AlgebraicClosure ℚ))) :=
  (serreAnFamilyOdd n).map toClosureFrac

/-- `serreAnOverFracOdd n` is monic.  Odd mirror of `serreAnOverFrac_monic`. -/
theorem serreAnOverFracOdd_monic (n : ℕ) (hn : 2 ≤ n) : (serreAnOverFracOdd n).Monic :=
  (serreAnFamilyOdd_monic n hn).map _

/-- `serreAnOverFracOdd n` has degree `n`.  Odd mirror of `serreAnOverFrac_natDegree`. -/
theorem serreAnOverFracOdd_natDegree (n : ℕ) (hn : 2 ≤ n) :
    (serreAnOverFracOdd n).natDegree = n := by
  rw [serreAnOverFracOdd, natDegree_map_eq_of_injective toClosureFrac_injective]
  exact serreAnFamilyOdd_natDegree n hn

/-! ## Critical-point values of `serreAnFamilyOdd` (for separability) -/

/-- **[algebraic leaf]** The value of `serreAnFamilyOdd n` at `Y = 0` (its constant-in-`Y`
coefficient) is `(k/(n−1))·(k−U²)^{n−1} ∈ ℚ[U]`, with `k = (−1)^{(n−1)/2}·n`. -/
theorem serreAnFamilyOdd_eval_zero (n : ℕ) (hn : 2 ≤ n) :
    (serreAnFamilyOdd n).eval 0
      = C (((-1 : ℚ) ^ ((n - 1) / 2) * n) / ((n : ℚ) - 1))
        * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2) ^ (n - 1) := by
  unfold serreAnFamilyOdd
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  rw [zero_pow (by omega : n ≠ 0), zero_pow (by omega : n - 1 ≠ 0)]
  ring

/-- **[algebraic leaf]** The value of `serreAnFamilyOdd n` at its second critical point
`Y = (k−U²)` is `(1/(n−1))·U²·(k−U²)^{n−1} ∈ ℚ[U]`. -/
theorem serreAnFamilyOdd_eval_kappa (n : ℕ) (hn : 2 ≤ n) :
    (serreAnFamilyOdd n).eval (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2)
      = C (1 / ((n : ℚ) - 1)) * X ^ 2
        * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2) ^ (n - 1) := by
  have hne : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  set kq : ℚ := (-1 : ℚ) ^ ((n - 1) / 2) * n with hkq
  set κ : Polynomial ℚ := C kq - X ^ 2 with hκ
  have hpow : κ ^ n = κ * κ ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  -- Scalar identities lifted to `ℚ[U]`.
  have hkey : κ - C ((n : ℚ) / ((n : ℚ) - 1)) * κ + C (kq / ((n : ℚ) - 1))
      = C (1 / ((n : ℚ) - 1)) * X ^ 2 := by
    have hc : kq - (n : ℚ) / ((n : ℚ) - 1) * kq + kq / ((n : ℚ) - 1) = 0 := by
      field_simp
      ring
    have hx : (1 : ℚ) - (n : ℚ) / ((n : ℚ) - 1) = -(1 / ((n : ℚ) - 1)) := by
      field_simp
      ring
    rw [hκ]
    have : (C kq - X ^ 2) - C ((n : ℚ) / ((n : ℚ) - 1)) * (C kq - X ^ 2) + C (kq / ((n : ℚ) - 1))
        = C (kq - (n : ℚ) / ((n : ℚ) - 1) * kq + kq / ((n : ℚ) - 1))
          + C ((1 : ℚ) - (n : ℚ) / ((n : ℚ) - 1)) * (-(X ^ 2)) := by
      simp only [map_add, map_sub, map_mul, map_one]
      ring
    rw [this, hc, hx]
    simp only [map_zero, map_neg]
    ring
  unfold serreAnFamilyOdd
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, ← hkq, ← hκ]
  rw [hpow]
  linear_combination (κ ^ (n - 1)) * hkey

/-- **[algebraic leaf]** `serreAnFamilyOdd n |_{Y=0}` is a nonzero element of `ℚ[U]`. -/
theorem serreAnFamilyOdd_eval_zero_ne (n : ℕ) (hn : 2 ≤ n) :
    (serreAnFamilyOdd n).eval 0 ≠ 0 := by
  have hne : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  rw [serreAnFamilyOdd_eval_zero n hn]
  apply mul_ne_zero
  · rw [Ne, C_eq_zero]
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hn0) hne
  · apply pow_ne_zero
    intro h
    have hc := congr_arg (fun p ↦ Polynomial.coeff p 2) h
    simp only [coeff_sub, coeff_C, coeff_X_pow, coeff_zero] at hc
    norm_num at hc

/-- **[algebraic leaf]** `serreAnFamilyOdd n |_{Y=(k−U²)}` is a nonzero element of `ℚ[U]`. -/
theorem serreAnFamilyOdd_eval_kappa_ne (n : ℕ) (hn : 2 ≤ n) :
    (serreAnFamilyOdd n).eval (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2) ≠ 0 := by
  have hne : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  rw [serreAnFamilyOdd_eval_kappa n hn]
  apply mul_ne_zero
  · apply mul_ne_zero
    · rw [Ne, C_eq_zero]
      exact div_ne_zero one_ne_zero hne
    · exact pow_ne_zero 2 X_ne_zero
  · apply pow_ne_zero
    intro h
    have hc := congr_arg (fun p ↦ Polynomial.coeff p 2) h
    simp only [coeff_sub, coeff_C, coeff_X_pow, coeff_zero] at hc
    norm_num at hc

/-! ## Separability of the base-changed odd family -/

/-- **[separability leaf — proved]** The base-changed odd family is separable over `ℚ̄(U)`.

Odd mirror of `serreAnOverFrac_separable`: a common root `α` of `serreAnOverFracOdd n` and its
derivative in `L = AlgebraicClosure ℚ̄(U)` must, by `serreAnFamilyOdd_derivative`
(`f' = n·Y^{n-2}·(Y − (k−U²))`), satisfy `α ∈ {0, χ(k−U²)}`.  Both `f(0)` and `f(k−U²)` are images
under the injective `χ = (ℚ[U] → ℚ̄(U) → L)` of the *nonzero* polynomials
`serreAnFamilyOdd_eval_zero/kappa`, so `f(α) ≠ 0` — contradiction. -/
theorem serreAnOverFracOdd_separable (n : ℕ) (hn : 2 ≤ n) (_hodd : Odd n) :
    (serreAnOverFracOdd n).Separable := by
  apply IsCoprime.symm
  by_contra h_not_coprime
  set K := FractionRing (Polynomial (AlgebraicClosure ℚ)) with hK
  set L := AlgebraicClosure K with hL
  set χ : Polynomial ℚ →+* L := (algebraMap K L).comp toClosureFrac with hχ
  obtain ⟨α, hf, hf'⟩ : ∃ α : L,
      eval α ((serreAnOverFracOdd n).map (algebraMap K L)) = 0 ∧
      eval α ((derivative (serreAnOverFracOdd n)).map (algebraMap K L)) = 0 := by
    contrapose! h_not_coprime
    apply isCoprime_of_irreducible_dvd
    · intro h
      have := serreAnOverFracOdd_natDegree n hn
      aesop
    · intro z hz hz' hz''
      obtain ⟨α, hα⟩ : ∃ α : L, eval α (z.map (algebraMap K L)) = 0 := by
        apply IsAlgClosed.exists_root
        rw [degree_map]
        exact ne_of_gt (degree_pos_of_irreducible hz)
      apply h_not_coprime α
      · simpa [hα] using eval_eq_zero_of_dvd_of_eval_eq_zero
          (Polynomial.map_dvd (algebraMap K L) hz'') hα
      · simpa [hα] using eval_eq_zero_of_dvd_of_eval_eq_zero
          (Polynomial.map_dvd (algebraMap K L) hz') hα
  have hmap_f : (serreAnOverFracOdd n).map (algebraMap K L) = (serreAnFamilyOdd n).map χ := by
    rw [serreAnOverFracOdd, Polynomial.map_map, ← hχ]
  have hmap_f' : (derivative (serreAnOverFracOdd n)).map (algebraMap K L)
      = (derivative (serreAnFamilyOdd n)).map χ := by
    rw [serreAnOverFracOdd, derivative_map, Polynomial.map_map, ← hχ]
  rw [hmap_f] at hf
  rw [hmap_f', serreAnFamilyOdd_derivative n hn] at hf'
  -- `f'(α) = 0`: `n·α^{n-2}·(α − χ(k−U²)) = 0`, hence `α = 0` or `α = χ(k−U²)`.
  set κ : Polynomial ℚ := C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2 with hκ
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_natCast, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    Polynomial.eval_natCast, map_natCast, map_mul] at hf'
  -- Now `hf' : (n:L) * α^{n-1} - (n:L) * χ κ * α^{n-2} = 0`.
  have hn0 : (n : L) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  have hfact : (n : L) * α ^ (n - 2) * (α - χ κ) = 0 := by
    have hm : n - 1 = (n - 2) + 1 := by omega
    rw [hm, pow_succ] at hf'
    linear_combination hf'
  have hr0κ : α = 0 ∨ α = χ κ := by
    rcases mul_eq_zero.mp hfact with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hn0
      · rcases eq_or_ne (n - 2) 0 with he | he
        · rw [he, pow_zero] at h'
          exact absurd h' one_ne_zero
        · exact Or.inl ((pow_eq_zero_iff he).mp h')
    · exact Or.inr (by linear_combination h)
  have hχinj : Function.Injective χ := by
    rw [hχ, RingHom.coe_comp]
    exact (algebraMap K L).injective.comp toClosureFrac_injective
  rcases hr0κ with h0 | hκα
  · subst h0
    rw [eval_map, show (0 : L) = χ 0 from (map_zero χ).symm,
      eval₂_at_apply] at hf
    exact serreAnFamilyOdd_eval_zero_ne n hn (hχinj hf)
  · subst hκα
    rw [eval_map, eval₂_at_apply, hκ] at hf
    exact serreAnFamilyOdd_eval_kappa_ne n hn (hχinj (hf.trans (map_zero χ).symm))

/-! ## The square-discriminant certificate: geometric group `≤ Aₙ` -/

/-- **[parity half — proved]** The image of the permutation representation of the geometric Galois
group of `serreAnFamilyOdd n` over `ℚ̄(U)` is **contained in** the alternating group on the roots.

Odd mirror of `an_geometric_le_alternating`: the odd square-discriminant certificate
(`serreAnDeltaPolyOdd n` squares to `serreAnDiscValPolyOdd n`, `serreAnDeltaPolyOdd_sq`, valid for
`Odd n`) makes `√disc ∈ K`, so every `K`-automorphism permutes the roots evenly. -/
theorem an_geometric_le_alternating_odd (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) :
    (Gal.galActionHom (serreAnOverFracOdd n) (serreAnOverFracOdd n).SplittingField).range
      ≤ alternatingGroup ((serreAnOverFracOdd n).rootSet (serreAnOverFracOdd n).SplittingField) := by
  set K := FractionRing (Polynomial (AlgebraicClosure ℚ)) with hK
  set M := (serreAnOverFracOdd n).SplittingField with hM
  set ev := (algebraMap K M).comp toClosureFrac with hev_def
  have hmapev : (serreAnFamilyOdd n).map ev = (serreAnOverFracOdd n).map (algebraMap K M) := by
    rw [hev_def, ← Polynomial.map_map]
    rfl
  have hdeg : ((serreAnFamilyOdd n).map ev).natDegree = n := by
    rw [hmapev, natDegree_map_of_leadingCoeff_ne_zero]
    · exact serreAnOverFracOdd_natDegree n hn
    · rw [(serreAnOverFracOdd_monic n hn).leadingCoeff, map_one]
      exact one_ne_zero
  have hsplit_f : ((serreAnOverFracOdd n).map (algebraMap K M)).Splits :=
    SplittingField.splits (serreAnOverFracOdd n)
  have hsp_roots : ((serreAnFamilyOdd n).map ev).Splits := by rwa [hmapev]
  have hcard : Multiset.card ((serreAnFamilyOdd n).map ev).roots = n := by
    rw [splits_iff_card_roots.mp hsp_roots, hdeg]
  obtain ⟨x, hxroots⟩ : ∃ x : Fin n → M,
      ((serreAnFamilyOdd n).map ev).roots = Finset.univ.val.map x := by
    obtain ⟨x, hx⟩ := ResolventConstruction.exists_fin_map_eq _ n hcard
    exact ⟨x, hx.symm⟩
  have hsep : ((serreAnFamilyOdd n).map ev).Separable := by
    rw [hmapev]
    exact (serreAnOverFracOdd_separable n hn hodd).map
  have hxinj : Function.Injective x := by
    have hnd : ((serreAnFamilyOdd n).map ev).roots.Nodup := nodup_roots hsep
    rw [hxroots] at hnd
    intro i j hij
    exact Multiset.inj_on_of_nodup_map hnd i (by simp) j (by simp) hij
  have hxmem : ∀ i, x i ∈ (serreAnOverFracOdd n).rootSet M := by
    intro i
    rw [mem_rootSet]
    refine ⟨(serreAnOverFracOdd_monic n hn).ne_zero, ?_⟩
    have hmemroots : x i ∈ ((serreAnFamilyOdd n).map ev).roots := by
      rw [hxroots]
      exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    rw [aeval_def, ← eval_map, ← hmapev]
    exact (mem_roots'.mp hmemroots).2
  have hcardrs : Fintype.card ((serreAnOverFracOdd n).rootSet M) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree (serreAnOverFracOdd_separable n hn hodd) hsplit_f,
      serreAnOverFracOdd_natDegree n hn]
  have hbij : Function.Bijective
      (fun i ↦ (⟨x i, hxmem i⟩ : (serreAnOverFracOdd n).rootSet M)) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
    · intro i j hij
      exact hxinj (Subtype.ext_iff.mp hij)
    · rw [Fintype.card_fin, hcardrs]
  set v := Equiv.ofBijective _ hbij with hv_def
  have hvx : ∀ i, (v i : M) = x i := fun i ↦ rfl
  have h_ne : discElem (fun i ↦ (v i : M)) ≠ 0 := by
    unfold discElem
    rw [← Matrix.det_vandermonde, Ne, Matrix.det_vandermonde_eq_zero_iff]
    push_neg
    exact fun i j h ↦ (Subtype.val_injective.comp v.injective) h
  have h_sq : ∃ d : K, discSq (fun i ↦ (v i : M)) = (algebraMap K M d) ^ 2 := by
    refine ⟨toClosureFrac (serreAnDeltaPolyOdd n), ?_⟩
    have hvx' : (fun i ↦ (v i : M)) = x := funext hvx
    rw [discSq, hvx', serreAnFamilyOdd_discSq_general n hn hodd ev x hdeg hxroots,
      ← serreAnDeltaPolyOdd_sq n hn hodd, map_pow, hev_def, RingHom.comp_apply]
  have hpar := gal_le_alternating_of_disc_sq (serreAnOverFracOdd n)
    (serreAnOverFracOdd_monic n hn).ne_zero v h_sq h_ne
  intro y hy
  obtain ⟨ψ, rfl⟩ := MonoidHom.mem_range.mp hy
  obtain ⟨ϕ, hϕ⟩ := Gal.restrict_surjective (serreAnOverFracOdd n) M ψ
  obtain ⟨π, hπ, hsign⟩ := hpar ϕ
  rw [Equiv.Perm.mem_alternatingGroup]
  have hperm : Gal.galActionHom (serreAnOverFracOdd n) M ψ = v.permCongr π := by
    refine Equiv.ext (fun r ↦ ?_)
    obtain ⟨i, rfl⟩ := v.surjective r
    apply Subtype.ext
    have hr := Gal.galActionHom_restrict (p := serreAnOverFracOdd n) (E := M) ϕ (v i)
    rw [hϕ] at hr
    rw [hr, hπ i, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [hperm, Equiv.Perm.sign_permCongr]
  exact hsign

/-! ## Root enumeration with `Aₙ`-Galois transport -/

/-- **[root enumeration with `Aₙ`-Galois transport — proved]** Odd mirror of `an_root_enum`. -/
theorem an_root_enum_odd (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n)
    (G : Polynomial (Polynomial ℚ)) (_hGmonic : G.Monic)
    (hG : IsAltResolvent n (serreAnFamilyOdd n) G)
    (hAlt : (Gal.galActionHom (serreAnOverFracOdd n) (serreAnOverFracOdd n).SplittingField).range
      = alternatingGroup ((serreAnOverFracOdd n).rootSet (serreAnOverFracOdd n).SplittingField)) :
    ∃ x : Fin n → (serreAnOverFracOdd n).SplittingField, Function.Injective x ∧
      G.map ((algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ)))
          (serreAnOverFracOdd n).SplittingField).comp toClosureFrac)
        = altResolventProduct n x ∧
      (∀ γ : (serreAnOverFracOdd n).SplittingField
          ≃ₐ[FractionRing (Polynomial (AlgebraicClosure ℚ))] (serreAnOverFracOdd n).SplittingField,
        ∃ σ : alternatingGroup (Fin n), ∀ i, γ (x i) = x ((σ : Equiv.Perm (Fin n)) i)) ∧
      (∀ σ : alternatingGroup (Fin n),
        ∃ γ : (serreAnOverFracOdd n).SplittingField
          ≃ₐ[FractionRing (Polynomial (AlgebraicClosure ℚ))] (serreAnOverFracOdd n).SplittingField,
        ∀ i, γ (x i) = x ((σ : Equiv.Perm (Fin n)) i)) := by
  set K := FractionRing (Polynomial (AlgebraicClosure ℚ)) with hK
  set M := (serreAnOverFracOdd n).SplittingField with hM
  set ev := (algebraMap K M).comp toClosureFrac with hev_def
  have hmapev : (serreAnFamilyOdd n).map ev = (serreAnOverFracOdd n).map (algebraMap K M) := by
    rw [hev_def, ← Polynomial.map_map]
    rfl
  have hdeg : ((serreAnFamilyOdd n).map ev).natDegree = n := by
    rw [hmapev, natDegree_map_of_leadingCoeff_ne_zero]
    · exact serreAnOverFracOdd_natDegree n hn
    · rw [(serreAnOverFracOdd_monic n hn).leadingCoeff, map_one]
      exact one_ne_zero
  have hsplit_f : ((serreAnOverFracOdd n).map (algebraMap K M)).Splits :=
    SplittingField.splits (serreAnOverFracOdd n)
  have hsp_roots : ((serreAnFamilyOdd n).map ev).Splits := by rwa [hmapev]
  have hcard : Multiset.card ((serreAnFamilyOdd n).map ev).roots = n := by
    rw [splits_iff_card_roots.mp hsp_roots, hdeg]
  obtain ⟨x0, hx0⟩ : ∃ x0 : Fin n → M,
      ((serreAnFamilyOdd n).map ev).roots = Finset.univ.val.map x0 := by
    obtain ⟨x0, hx0⟩ := ResolventConstruction.exists_fin_map_eq _ n hcard
    exact ⟨x0, hx0.symm⟩
  obtain ⟨x, hxroots, hGx⟩ := hG ev x0 hdeg hx0
  have hsep : ((serreAnFamilyOdd n).map ev).Separable := by
    rw [hmapev]
    exact (serreAnOverFracOdd_separable n hn hodd).map
  have hxinj : Function.Injective x := by
    have hnd : ((serreAnFamilyOdd n).map ev).roots.Nodup := nodup_roots hsep
    rw [hxroots] at hnd
    intro i j hij
    exact Multiset.inj_on_of_nodup_map hnd i (by simp) j (by simp) hij
  have hxmem : ∀ i, x i ∈ (serreAnOverFracOdd n).rootSet M := by
    intro i
    rw [mem_rootSet]
    refine ⟨(serreAnOverFracOdd_monic n hn).ne_zero, ?_⟩
    have hmemroots : x i ∈ ((serreAnFamilyOdd n).map ev).roots := by
      rw [hxroots]
      exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    rw [aeval_def, ← eval_map, ← hmapev]
    exact (mem_roots'.mp hmemroots).2
  have hcardrs : Fintype.card ((serreAnOverFracOdd n).rootSet M) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree (serreAnOverFracOdd_separable n hn hodd) hsplit_f,
      serreAnOverFracOdd_natDegree n hn]
  have hbij : Function.Bijective
      (fun i ↦ (⟨x i, hxmem i⟩ : (serreAnOverFracOdd n).rootSet M)) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
    · intro i j hij
      exact hxinj (Subtype.ext_iff.mp hij)
    · rw [Fintype.card_fin, hcardrs]
  set v := Equiv.ofBijective _ hbij with hv_def
  have hvx : ∀ i, (v i : M) = x i := fun i ↦ rfl
  have h_ne : discElem (fun i ↦ (v i : M)) ≠ 0 := by
    unfold discElem
    rw [← Matrix.det_vandermonde, Ne, Matrix.det_vandermonde_eq_zero_iff]
    push_neg
    exact fun i j h ↦ (Subtype.val_injective.comp v.injective) h
  have h_sq : ∃ d : K, discSq (fun i ↦ (v i : M)) = (algebraMap K M d) ^ 2 := by
    refine ⟨toClosureFrac (serreAnDeltaPolyOdd n), ?_⟩
    have hvx' : (fun i ↦ (v i : M)) = x := funext hvx
    rw [discSq, hvx', serreAnFamilyOdd_discSq_general n hn hodd ev x hdeg hxroots,
      ← serreAnDeltaPolyOdd_sq n hn hodd, map_pow, hev_def, RingHom.comp_apply]
  have hgal_alt := gal_le_alternating_of_disc_sq (serreAnOverFracOdd n)
    (serreAnOverFracOdd_monic n hn).ne_zero v h_sq h_ne
  refine ⟨x, hxinj, hGx, ?_, ?_⟩
  · intro γ
    obtain ⟨π, hπ, hsign⟩ := hgal_alt γ
    refine ⟨⟨π, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, fun i ↦ ?_⟩
    show γ (x i) = x (π i)
    rw [← hvx i, ← hvx (π i)]
    exact hπ i
  · intro σ
    set πrs : Equiv.Perm ((serreAnOverFracOdd n).rootSet M) :=
      v.permCongr (σ : Equiv.Perm (Fin n)) with hπrs
    have hπrs_sign : Equiv.Perm.sign πrs = 1 := by
      rw [hπrs, Equiv.Perm.sign_permCongr]
      exact Equiv.Perm.mem_alternatingGroup.mp σ.2
    have hmem : πrs ∈ (Gal.galActionHom (serreAnOverFracOdd n) M).range := by
      rw [hAlt]
      exact Equiv.Perm.mem_alternatingGroup.mpr hπrs_sign
    obtain ⟨φ, hφ⟩ := MonoidHom.mem_range.mp hmem
    obtain ⟨ϕ, hϕ⟩ := Gal.restrict_surjective (serreAnOverFracOdd n) M φ
    have key : ∀ i, (πrs (v i) : M) = x ((σ : Equiv.Perm (Fin n)) i) := by
      intro i
      rw [hπrs, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      exact hvx _
    refine ⟨ϕ, fun i ↦ ?_⟩
    have hr := Gal.galActionHom_restrict (p := serreAnOverFracOdd n) (E := M) ϕ (v i)
    rw [hϕ, hφ] at hr
    rw [hvx i, key i] at hr
    exact hr.symm

/-! ## The resolvent is irreducible over `ℚ̄(U)` given the geometric group is `Aₙ` -/

/-- **[monodromy core — geometric algebra, proved]** Odd mirror of `anResolventFrac_irreducible`. -/
theorem anResolventFrac_irreducible_odd (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n)
    (G : Polynomial (Polynomial ℚ)) (hGmonic : G.Monic)
    (hG : IsAltResolvent n (serreAnFamilyOdd n) G)
    (hAlt : (Gal.galActionHom (serreAnOverFracOdd n) (serreAnOverFracOdd n).SplittingField).range
      = alternatingGroup ((serreAnOverFracOdd n).rootSet (serreAnOverFracOdd n).SplittingField)) :
    Irreducible (G.map toClosureFrac) := by
  obtain ⟨x, hxinj, hGx, hgal, hsurj2⟩ := an_root_enum_odd n hn hodd G hGmonic hG hAlt
  set ev := (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ)))
    (serreAnOverFracOdd n).SplittingField).comp toClosureFrac with hev_def
  have : IsGalois (FractionRing (Polynomial (AlgebraicClosure ℚ)))
      (serreAnOverFracOdd n).SplittingField :=
    IsGalois.of_separable_splitting_field (serreAnOverFracOdd_separable n hn hodd)
  have hev_deg : (G.map ev).natDegree = G.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _
      (by
        rw [hGmonic.leadingCoeff, map_one]
        exact one_ne_zero)
  have hdegG : (G.map toClosureFrac).natDegree = n.factorial / 2 := by
    have e1 : (G.map toClosureFrac).natDegree = G.natDegree :=
      natDegree_map_of_leadingCoeff_ne_zero _
        (by
          rw [hGmonic.leadingCoeff, map_one]
          exact one_ne_zero)
    rw [e1, ← hev_deg, hGx, altResolventProduct_natDegree n hn]
  have hw : (aeval (genForm n x 1)) (G.map toClosureFrac) = 0 := by
    have h1 : (G.map toClosureFrac).map
        (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ)))
          (serreAnOverFracOdd n).SplittingField) = altResolventProduct n x := by
      rw [Polynomial.map_map]
      exact hGx
    rw [aeval_def, ← eval_map, h1]
    exact altResolventProduct_isRoot_genForm_one n x
  have hNT : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  apply Monic.irreducible_of_galois_orbit_card (hGmonic.map toClosureFrac) hw
  rw [orbit_genForm_eq_alternating_range x hgal hsurj2,
      Nat.card_range_of_injective (genForm_alternating_injective x hxinj hsurj2),
      Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin, hdegG]

/-! ## Reduction to absolute (geometric) irreducibility over `ℚ̄` -/

/-- **[reduction — Gauss, proved]** Odd mirror of
`abs_irreducible_of_geometric_galois_alternating`. -/
theorem abs_irreducible_of_geometric_galois_alternating_odd (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n)
    (G : Polynomial (Polynomial ℚ)) (hGmonic : G.Monic)
    (hG : IsAltResolvent n (serreAnFamilyOdd n) G)
    (hAlt : (Gal.galActionHom (serreAnOverFracOdd n) (serreAnOverFracOdd n).SplittingField).range
      = alternatingGroup ((serreAnOverFracOdd n).rootSet (serreAnOverFracOdd n).SplittingField)) :
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
  exact anResolventFrac_irreducible_odd n hn hodd G hGmonic hG hAlt

/-! ## The odd base-change/descent machinery -/

namespace OddDescent

open EvenDescent

/-- `k̄ = (−1)^{(n−1)/2}·n ∈ ℚ̄`, the second-critical-point scalar. -/
def kbConst (n : ℕ) : AlgebraicClosure ℚ := (-1) ^ ((n - 1) / 2) * n

/-- `κ = k̄ − t² ∈ GeomBase` (with `t = algebraMap R GeomBase X`), the base scalar by which the
descent rescales the roots. -/
def kappaOdd (n : ℕ) : GeomBase :=
  algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C (kbConst n) - X ^ 2)

/-- The odd **rational** substitution value `S ↦ −k̄ / ((n−1)·κ) ∈ GeomBase`. -/
def substValOdd (n : ℕ) : GeomBase :=
  - algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C (kbConst n))
    / (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C ((n : AlgebraicClosure ℚ) - 1))
        * kappaOdd n)

theorem kbConst_ne_zero (n : ℕ) (hn : 1 ≤ n) : kbConst n ≠ 0 := by
  rw [kbConst]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  exact_mod_cast (by omega : n ≠ 0)

theorem nm1_ne_zero (n : ℕ) (hn : 2 ≤ n) : (n : AlgebraicClosure ℚ) - 1 ≠ 0 := by
  have h : (n : AlgebraicClosure ℚ) ≠ 1 := by exact_mod_cast (show (n : ℕ) ≠ 1 by omega)
  exact sub_ne_zero.mpr h

theorem kappaOdd_ne_zero (n : ℕ) : kappaOdd n ≠ 0 := by
  rw [kappaOdd, Ne,
    map_eq_zero_iff _ (IsFractionRing.injective (Polynomial (AlgebraicClosure ℚ)) GeomBase)]
  intro h
  have hc := congrArg (fun p ↦ Polynomial.coeff p 2) h
  norm_num [coeff_sub, coeff_C, coeff_X_pow] at hc

theorem kbConstG_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C (kbConst n)) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (Polynomial (AlgebraicClosure ℚ)) GeomBase),
    Polynomial.C_eq_zero]
  exact kbConst_ne_zero n hn

theorem nm1G_ne_zero (n : ℕ) (hn : 2 ≤ n) :
    algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C ((n : AlgebraicClosure ℚ) - 1)) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (Polynomial (AlgebraicClosure ℚ)) GeomBase),
    Polynomial.C_eq_zero]
  exact nm1_ne_zero n hn

theorem substValOdd_ne_zero (n : ℕ) (hn : 2 ≤ n) : substValOdd n ≠ 0 := by
  rw [substValOdd]
  apply div_ne_zero
  · exact neg_ne_zero.mpr (kbConstG_ne_zero n (by omega))
  · exact mul_ne_zero (nm1G_ne_zero n hn) (kappaOdd_ne_zero n)

/-- `κ · substValOdd = −k̄/(n−1)`: the core scalar identity behind the scaling. -/
theorem kappaOdd_mul_substValOdd (n : ℕ) (hn : 2 ≤ n) :
    kappaOdd n * substValOdd n
      = - algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C (kbConst n))
          / algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C ((n : AlgebraicClosure ℚ) - 1)) := by
  have hk := kappaOdd_ne_zero n
  have hnm := nm1G_ne_zero n hn
  rw [substValOdd]
  field_simp

/-- The substitution value is transcendental over `ℚ̄` (needed for `IsFractionRing.lift`). -/
theorem substValOdd_transcendental (n : ℕ) (hn : 2 ≤ n) :
    Transcendental (AlgebraicClosure ℚ) (substValOdd n) := by
  intro halg
  set F := algebraicClosure (AlgebraicClosure ℚ) GeomBase with hF
  have hsv : substValOdd n ∈ F := (mem_algebraicClosure_iff).mpr halg
  have hconst : ∀ c : AlgebraicClosure ℚ,
      algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c) ∈ F := by
    intro c
    rw [hF, mem_algebraicClosure_iff]
    have : algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c)
        = algebraMap (AlgebraicClosure ℚ) GeomBase c := by
      rw [IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) (Polynomial (AlgebraicClosure ℚ))
        GeomBase c, Polynomial.algebraMap_eq]
    rw [this]
    exact isAlgebraic_algebraMap c
  -- κ ∈ F, from κ · substValOdd = −k̄/(n−1) and substValOdd ≠ 0.
  have hkappa : kappaOdd n ∈ F := by
    have hid := kappaOdd_mul_substValOdd n hn
    have hsvne := substValOdd_ne_zero n hn
    have : kappaOdd n
        = (- algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C (kbConst n))
            / algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C ((n : AlgebraicClosure ℚ) - 1)))
          / substValOdd n := by
      rw [← hid, mul_div_assoc, div_self hsvne, mul_one]
    rw [this]
    exact div_mem (div_mem (neg_mem (hconst _)) (hconst _)) hsv
  -- t² = k̄ − κ ∈ F, hence t algebraic — contradiction.
  have ht2 : (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X) ^ 2 ∈ F := by
    have : (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X) ^ 2
        = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C (kbConst n)) - kappaOdd n := by
      rw [kappaOdd, ← map_pow, ← map_sub]
      congr 1
      ring
    rw [this]
    exact sub_mem (hconst _) hkappa
  have htalg : IsAlgebraic (AlgebraicClosure ℚ)
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X) :=
    IsAlgebraic.of_pow (by norm_num) ((mem_algebraicClosure_iff).mp ht2)
  exact geomBase_gen_transcendental htalg

/-- The odd substitution ring hom `R →+* GeomBase`, `X ↦ substValOdd n`. -/
noncomputable def substRingHomOdd (n : ℕ) :
    Polynomial (AlgebraicClosure ℚ) →+* GeomBase :=
  (Polynomial.aeval (substValOdd n)).toRingHom

theorem substRingHomOdd_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (substRingHomOdd n) := by
  rw [substRingHomOdd]
  exact transcendental_iff_injective.mp (substValOdd_transcendental n hn)

theorem substRingHomOdd_C (n : ℕ) (c : AlgebraicClosure ℚ) :
    substRingHomOdd n (C c) = algebraMap (AlgebraicClosure ℚ) GeomBase c := by
  simp [substRingHomOdd]

theorem substRingHomOdd_X (n : ℕ) : substRingHomOdd n X = substValOdd n := by
  simp [substRingHomOdd]

/-- The odd substitution field hom `BaseT →+* GeomBase` via `IsFractionRing.lift`. -/
noncomputable def substFieldHomOdd (n : ℕ) (hn : 2 ≤ n) : BaseT →+* GeomBase :=
  IsFractionRing.lift (A := Polynomial (AlgebraicClosure ℚ)) (K := BaseT)
    (substRingHomOdd_injective n hn)

theorem substFieldHomOdd_algebraMap (n : ℕ) (hn : 2 ≤ n)
    (x : Polynomial (AlgebraicClosure ℚ)) :
    substFieldHomOdd n hn (algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT x)
      = substRingHomOdd n x := by
  rw [substFieldHomOdd, IsFractionRing.lift_algebraMap]

/-- The algebra structure on `GeomBase` over `BaseT` carried by the odd substitution. -/
noncomputable def algBaseTOdd (n : ℕ) (hn : 2 ≤ n) : Algebra BaseT GeomBase :=
  (substFieldHomOdd n hn).toAlgebra

theorem algebraMap_baseTOdd_eq (n : ℕ) (hn : 2 ≤ n) :
    letI := algBaseTOdd n hn
    algebraMap BaseT GeomBase = substFieldHomOdd n hn := rfl

/-- `algebraMap ℚ̄ GeomBase c = algebraMap R GeomBase (C c)`. -/
theorem algQbarGeom_eq_C (c : AlgebraicClosure ℚ) :
    algebraMap (AlgebraicClosure ℚ) GeomBase c
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c) := by
  rw [IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) (Polynomial (AlgebraicClosure ℚ))
    GeomBase c, Polynomial.algebraMap_eq]

/-- `substFieldHomOdd` fixes the `ℚ̄`-constants. -/
theorem substFieldHomOdd_C (n : ℕ) (hn : 2 ≤ n) (c : AlgebraicClosure ℚ) :
    substFieldHomOdd n hn
        (algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT (C c))
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c) := by
  rw [substFieldHomOdd_algebraMap, substRingHomOdd_C, algQbarGeom_eq_C]

/-- `substFieldHomOdd` sends `t` to `substValOdd`. -/
theorem substFieldHomOdd_X (n : ℕ) (hn : 2 ≤ n) :
    substFieldHomOdd n hn (algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT X)
      = substValOdd n := by
  rw [substFieldHomOdd_algebraMap, substRingHomOdd_X]

theorem kappaOdd_eq (n : ℕ) :
    kappaOdd n = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C (kbConst n))
      - (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X) ^ 2 := by
  rw [kappaOdd, map_sub, map_pow]

set_option synthInstance.maxHeartbeats 800000 in
/-- The square of the transcendental generator `t` lies in the image of `BaseT`, explicitly
`t² = k̄ − κ` and `κ = −k̄/((n−1)·substValOdd)` is in the base. -/
theorem gen_sq_mem_range (n : ℕ) (hn : 2 ≤ n) :
    letI := algBaseTOdd n hn
    ∃ β : BaseT, algebraMap BaseT GeomBase β
      = (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X) ^ 2 := by
  let _ := algBaseTOdd n hn
  have hk := kappaOdd_ne_zero n
  have hnm := nm1G_ne_zero n hn
  have hkb := kbConstG_ne_zero n (by omega)
  refine ⟨algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT (C (kbConst n))
      + algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT (C (kbConst n))
        * (algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT (C ((n : AlgebraicClosure ℚ) - 1))
            * algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT X)⁻¹, ?_⟩
  show substFieldHomOdd n hn _ = _
  rw [map_add, map_mul, map_inv₀, map_mul, substFieldHomOdd_C, substFieldHomOdd_C,
    substFieldHomOdd_X]
  have ht2 : (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X) ^ 2
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C (kbConst n)) - kappaOdd n := by
    rw [kappaOdd_eq]
    ring
  rw [ht2, substValOdd]
  field_simp
  ring

/-- The `X ↦ -X` ring endomorphism of `ℚ̄[X]` (re-declared for the odd branch). -/
noncomputable def signPolyHom :
    Polynomial (AlgebraicClosure ℚ) →+* Polynomial (AlgebraicClosure ℚ) :=
  (Polynomial.aeval (-X : Polynomial (AlgebraicClosure ℚ))).toRingHom

theorem signPolyHom_apply (p : Polynomial (AlgebraicClosure ℚ)) :
    signPolyHom p = p.comp (-X) := by
  rw [signPolyHom, comp_eq_aeval]
  rfl

theorem signPolyHom_involutive : Function.Involutive signPolyHom := by
  intro p
  rw [signPolyHom_apply, signPolyHom_apply, comp_assoc]
  simp [neg_comp, X_comp, comp_X]

/-- The `X ↦ -X` field automorphism of `GeomBase = ℚ̄(X)`. -/
noncomputable def signFieldHom : GeomBase →+* GeomBase :=
  IsFractionRing.map (A := Polynomial (AlgebraicClosure ℚ))
    (B := Polynomial (AlgebraicClosure ℚ)) signPolyHom_involutive.injective

theorem signFieldHom_algebraMap (x : Polynomial (AlgebraicClosure ℚ)) :
    signFieldHom (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase x)
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (signPolyHom x) := by
  simp only [signFieldHom, IsFractionRing.map]
  exact IsLocalization.map_eq _ _

theorem signFieldHom_algMapC (c : AlgebraicClosure ℚ) :
    signFieldHom (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c))
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c) := by
  rw [signFieldHom_algebraMap, signPolyHom_apply, C_comp]

theorem signFieldHom_kappaOdd (n : ℕ) : signFieldHom (kappaOdd n) = kappaOdd n := by
  rw [kappaOdd, signFieldHom_algebraMap]
  congr 1
  rw [signPolyHom_apply]
  simp [sub_comp, C_comp, pow_comp, X_comp]

theorem signFieldHom_substValOdd (n : ℕ) : signFieldHom (substValOdd n) = substValOdd n := by
  rw [substValOdd, map_div₀, map_neg, map_mul, signFieldHom_algMapC, signFieldHom_algMapC,
    signFieldHom_kappaOdd]

theorem signFieldHom_comp_substRingHomOdd (n : ℕ) :
    signFieldHom.comp (substRingHomOdd n) = substRingHomOdd n := by
  apply Polynomial.ringHom_ext
  · intro c
    rw [RingHom.comp_apply, substRingHomOdd_C, algQbarGeom_eq_C, signFieldHom_algMapC]
  · rw [RingHom.comp_apply, substRingHomOdd_X, signFieldHom_substValOdd]

theorem signFieldHom_comp_substFieldHomOdd (n : ℕ) (hn : 2 ≤ n) :
    signFieldHom.comp (substFieldHomOdd n hn) = substFieldHomOdd n hn := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial (AlgebraicClosure ℚ)))
  refine RingHom.ext fun x ↦ ?_
  simp only [RingHom.comp_apply]
  rw [substFieldHomOdd_algebraMap]
  exact RingHom.congr_fun (signFieldHom_comp_substRingHomOdd n) x

/-- `t` is integral over `BaseT`: a root of the monic `X² − C β`. -/
theorem isIntegral_t (n : ℕ) (hn : 2 ≤ n) :
    letI := algBaseTOdd n hn
    IsIntegral BaseT (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X) := by
  let _ := algBaseTOdd n hn
  obtain ⟨β, hβ⟩ := gen_sq_mem_range n hn
  refine ⟨X ^ 2 - C β, monic_X_pow_sub_C β (by norm_num), ?_⟩
  show Polynomial.eval₂ (algebraMap BaseT GeomBase) _ _ = 0
  rw [← aeval_def]
  simp only [map_sub, map_pow, aeval_X, aeval_C, hβ, sub_self]

theorem minpoly_natDegree_le_two (n : ℕ) (hn : 2 ≤ n) :
    letI := algBaseTOdd n hn
    (minpoly BaseT (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)).natDegree ≤ 2 := by
  let _ := algBaseTOdd n hn
  obtain ⟨β, hβ⟩ := gen_sq_mem_range n hn
  have hmonic : (X ^ 2 - C β : BaseT[X]).Monic := monic_X_pow_sub_C β (by norm_num)
  have haeval : (Polynomial.aeval
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)) (X ^ 2 - C β : BaseT[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, hβ, sub_self]
  have hdvd := minpoly.dvd BaseT _ haeval
  calc (minpoly BaseT (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)).natDegree
        ≤ (X ^ 2 - C β : BaseT[X]).natDegree :=
          natDegree_le_of_dvd hdvd hmonic.ne_zero
    _ = 2 := natDegree_X_pow_sub_C

theorem adjoin_t_eq_top (n : ℕ) (hn : 2 ≤ n) :
    letI := algBaseTOdd n hn
    IntermediateField.adjoin BaseT
      {algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X} = ⊤ := by
  let _ := algBaseTOdd n hn
  set t := algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X with ht
  set M := IntermediateField.adjoin BaseT {t} with hM
  have htM : t ∈ M := IntermediateField.mem_adjoin_simple_self BaseT t
  have hconst : ∀ c : AlgebraicClosure ℚ,
      algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c) ∈ M := by
    intro c
    have hc : algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c)
        = algebraMap BaseT GeomBase
            (algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT (C c)) := by
      rw [algebraMap_baseTOdd_eq]
      exact (substFieldHomOdd_C n hn c).symm
    rw [hc]
    exact M.algebraMap_mem _
  have hrange : ∀ q : Polynomial (AlgebraicClosure ℚ),
      algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase q ∈ M := by
    intro q
    refine Polynomial.induction_on' q ?_ ?_
    · intro p q hp hq
      rw [map_add]
      exact add_mem hp hq
    · intro k c
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact mul_mem (hconst c) (pow_mem htM k)
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, d, -, rfl⟩ :=
    IsFractionRing.div_surjective (A := Polynomial (AlgebraicClosure ℚ)) (K := GeomBase) y
  exact div_mem (hrange a) (hrange d)

theorem t_not_mem_range (n : ℕ) (hn : 2 ≤ n) :
    letI := algBaseTOdd n hn
    algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X
      ∉ Set.range (algebraMap BaseT GeomBase) := by
  let _ := algBaseTOdd n hn
  rintro ⟨b, hb⟩
  rw [algebraMap_baseTOdd_eq] at hb
  have h1 : signFieldHom (substFieldHomOdd n hn b) = substFieldHomOdd n hn b :=
    RingHom.congr_fun (signFieldHom_comp_substFieldHomOdd n hn) b
  have h2 : signFieldHom (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)
      = - algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X := by
    rw [signFieldHom_algebraMap, signPolyHom_apply, X_comp, map_neg]
  rw [hb, h2] at h1
  have htne : algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact X_ne_zero
  have h6 : (2 : GeomBase) * algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X = 0 := by
    linear_combination -h1
  rcases mul_eq_zero.mp h6 with h | h
  · exact two_ne_zero h
  · exact htne h

set_option synthInstance.maxHeartbeats 800000 in
set_option linter.unusedVariables false in
theorem finiteDimensional_baseT_geomBaseOdd (n : ℕ) (hn : 2 ≤ n) :
    letI := algBaseTOdd n hn
    FiniteDimensional BaseT GeomBase := by
  let _ := algBaseTOdd n hn
  have hfd : FiniteDimensional BaseT
      (IntermediateField.adjoin BaseT
        {algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X}) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_t n hn)
  rw [adjoin_t_eq_top n hn] at hfd
  have := hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

set_option synthInstance.maxHeartbeats 800000 in
set_option linter.unusedVariables false in
theorem finrank_baseT_geomBaseOdd (n : ℕ) (hn : 2 ≤ n) :
    letI := algBaseTOdd n hn
    Module.finrank BaseT GeomBase = 2 := by
  let _ := algBaseTOdd n hn
  have hInt := isIntegral_t n hn
  have hfr : Module.finrank BaseT
      (IntermediateField.adjoin BaseT
        {algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X})
      = (minpoly BaseT (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)).natDegree :=
    IntermediateField.adjoin.finrank hInt
  rw [adjoin_t_eq_top n hn, IntermediateField.finrank_top'] at hfr
  rw [hfr]
  have hle := minpoly_natDegree_le_two n hn
  have hpos := minpoly.natDegree_pos hInt
  have hne1 : (minpoly BaseT
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)).natDegree ≠ 1 := by
    intro h1
    have hbot : Module.finrank BaseT
        (IntermediateField.adjoin BaseT
          {algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X}) = 1 := by
      rw [IntermediateField.adjoin.finrank hInt, h1]
    rw [IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff,
      IntermediateField.mem_bot] at hbot
    exact t_not_mem_range n hn hbot
  omega

/-- **Abstract lower bound.**  If `f` is separable of degree `n` with symmetric geometric monodromy
over `K`, `K'/K` is quadratic, and `E ⊇ K'` is a finite extension in which `f` splits, then
`n! ≤ 2·[E:K']`.  (The upper `hle` half of the quadratic descent is *not* needed here.)  This is the
lower-bound block of `QuadraticDescent.card_gal_descent_of_quadratic`, abstracted over the splitting
target `E` so that the odd descent can compare against `serreAnOverFracOdd`'s own splitting field. -/
theorem factorial_le_two_finrank {K K' E : Type*} [Field K] [Field K'] [Field E]
    [Algebra K K'] [Algebra K' E] [Algebra K E] [IsScalarTower K K' E] [CharZero K]
    (f : K[X]) (hf_sep : f.Separable) {n : ℕ} (hf_deg : f.natDegree = n)
    (hSn : Function.Surjective (Gal.galActionHom f f.SplittingField))
    [FiniteDimensional K K'] (hK'_deg : Module.finrank K K' = 2)
    [FiniteDimensional K' E]
    (hfsplitE : (f.map (algebraMap K E)).Splits) :
    n.factorial ≤ 2 * Module.finrank K' E := by
  have : FiniteDimensional K E := Module.Finite.trans K' E
  have hfGal : Nat.card f.Gal = n.factorial := by
    have hinj := Gal.galActionHom_injective f f.SplittingField
    have hbij : Function.Bijective (Gal.galActionHom f f.SplittingField) := ⟨hinj, hSn⟩
    have hcardRootf : Fintype.card (f.rootSet f.SplittingField) = n := by
      rw [Polynomial.card_rootSet_eq_natDegree hf_sep (SplittingField.splits f), hf_deg]
    calc Nat.card f.Gal
        = Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
          Nat.card_congr (Equiv.ofBijective _ hbij)
      _ = n.factorial := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcardRootf]
  have hlift_inj : Function.Injective (Polynomial.SplittingField.lift f hfsplitE) :=
    (Polynomial.SplittingField.lift f hfsplitE).toRingHom.injective
  have hfr_le : Module.finrank K f.SplittingField ≤ Module.finrank K E :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (Polynomial.SplittingField.lift f hfsplitE).toLinearMap) hlift_inj
  calc n.factorial
      = Nat.card f.Gal := hfGal.symm
    _ = Module.finrank K f.SplittingField := Gal.card_of_separable hf_sep
    _ ≤ Module.finrank K E := hfr_le
    _ = Module.finrank K K' * Module.finrank K' E := (Module.finrank_mul_finrank K K' E).symm
    _ = 2 * Module.finrank K' E := by rw [hK'_deg]

end OddDescent

/-! ## The deep geometric monodromy input -/

/-- **[monodromy core — the residual cardinality, now proved]** The geometric Galois group of
`serreAnFamilyOdd n` over `ℚ̄(U)` has order `n!/2`, i.e. `2 · |(serreAnOverFracOdd n).Gal| = n!`.

This is the single deep input of the odd geometric-monodromy branch, isolated from the group
theory (which is discharged by `QuadraticDescent.galActionHom_range_eq_alternating_of_card`).
Proof by `le_antisymm`:

* **Upper bound** `2·|Gal| ≤ n!`: the geometric monodromy is even
  (`an_geometric_le_alternating_odd`), and `2·|Aₙ| = |Sₙ| = n!`.
* **Lower bound** `n! ≤ 2·|Gal|`: odd descent from the shared Serre base cover.  The base cover
  `serreBaseGeomPoly n` over `BaseT ≅ ℚ̄(S)` has full symmetric geometric monodromy
  (`serreBaseGeomPoly_galActionHom_surjective`), and the **odd rational** substitution
  `S ↦ −k̄/((n−1)·κ)` (with `κ = k̄ − U²`, `OddDescent.algBaseTOdd`) base-changes it to
  `g := (serreBaseGeomPoly n).map substFieldHomOdd`.  The (now-formalised) scaling identity
  `(serreAnOverFracOdd n).comp (C κ · X) = C(κⁿ) · g` (`hcompeq`) shows `g` splits in the splitting
  field of `serreAnOverFracOdd n`, so `serreBaseGeomPoly n` splits there too.  With
  `finrank BaseT GeomBase = 2` (`OddDescent.finrank_baseT_geomBaseOdd`), the abstract tower bound
  `OddDescent.factorial_le_two_finrank` yields `n! ≤ 2·[SF_a : GeomBase] = 2·|Gal|`. -/
theorem an_geometric_card_gal_odd (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    2 * Nat.card (serreAnOverFracOdd n).Gal = n.factorial := by
  have hn2 : 2 ≤ n := by omega
  apply le_antisymm
  · -- **Upper bound** `2·|Gal| ≤ n!`: the geometric monodromy is even
    -- (`an_geometric_le_alternating_odd`), and `2·|Aₙ| = |Sₙ| = n!`.
    set M := (serreAnOverFracOdd n).SplittingField with hM
    have hsep := serreAnOverFracOdd_separable n hn2 hodd
    have hcardRoot : Fintype.card ((serreAnOverFracOdd n).rootSet M) = n := by
      rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits _),
        serreAnOverFracOdd_natDegree n hn2]
    have hinjg := Gal.galActionHom_injective (serreAnOverFracOdd n) M
    have hcardRange : Nat.card (Gal.galActionHom (serreAnOverFracOdd n) M).range
        = Nat.card (serreAnOverFracOdd n).Gal :=
      (Nat.card_congr (MonoidHom.ofInjective hinjg).toEquiv).symm
    have hcardle : Nat.card (Gal.galActionHom (serreAnOverFracOdd n) M).range
        ≤ Nat.card (alternatingGroup ((serreAnOverFracOdd n).rootSet M)) :=
      Subgroup.card_le_of_le (an_geometric_le_alternating_odd n hn2 hodd)
    have : Nontrivial ((serreAnOverFracOdd n).rootSet M) := by
      rw [← Fintype.one_lt_card_iff_nontrivial, hcardRoot]
      omega
    calc 2 * Nat.card (serreAnOverFracOdd n).Gal
        = 2 * Nat.card (Gal.galActionHom (serreAnOverFracOdd n) M).range := by rw [hcardRange]
      _ ≤ 2 * Nat.card (alternatingGroup ((serreAnOverFracOdd n).rootSet M)) := by gcongr
      _ = Nat.card (Equiv.Perm ((serreAnOverFracOdd n).rootSet M)) :=
          two_mul_nat_card_alternatingGroup
      _ = n.factorial := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcardRoot]
  · -- **Lower bound** `n! ≤ 2·|Gal|`: descend from the Serre base cover along the odd
    -- rational substitution and use `OddDescent.factorial_le_two_finrank`.
    let _ := OddDescent.algBaseTOdd n hn2
    have := OddDescent.finiteDimensional_baseT_geomBaseOdd n hn2
    -- Abbreviations for the two constant coefficients (over `ℚ̄`).
    set c1 : GeomBase := algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase
        (C ((n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1))) with hc1def
    set c0 : GeomBase := algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase
        (C (OddDescent.kbConst n / ((n : AlgebraicClosure ℚ) - 1))) with hc0def
    set g : GeomBase[X] := (serreBaseGeomPoly n).map
        (algebraMap EvenDescent.BaseT GeomBase) with hgdef
    -- `toClosureFrac` on the two atomic coefficients.
    have htcC : ∀ q : ℚ, toClosureFrac (C q)
        = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase
            (C (algebraMap ℚ (AlgebraicClosure ℚ) q)) := by
      intro q
      rw [toClosureFrac, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C]
    have htcX : toClosureFrac X
        = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X := by
      rw [toClosureFrac, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X]
    have hφdiv : algebraMap ℚ (AlgebraicClosure ℚ) ((n : ℚ) / ((n : ℚ) - 1))
        = (n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1) := by
      rw [map_div₀, map_sub, map_one, map_natCast]
    have hφkq : algebraMap ℚ (AlgebraicClosure ℚ) ((-1 : ℚ) ^ ((n - 1) / 2) * n)
        = OddDescent.kbConst n := by
      rw [OddDescent.kbConst, map_mul, map_pow, map_neg, map_one, map_natCast]
    have hφkqdiv : algebraMap ℚ (AlgebraicClosure ℚ)
          (((-1 : ℚ) ^ ((n - 1) / 2) * n) / ((n : ℚ) - 1))
        = OddDescent.kbConst n / ((n : AlgebraicClosure ℚ) - 1) := by
      rw [map_div₀, map_sub, map_one, map_natCast, hφkq]
    -- Normal form of the two families.
    have htcoeff1 : toClosureFrac
          (C ((n : ℚ) / ((n : ℚ) - 1))
            * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2))
        = c1 * OddDescent.kappaOdd n := by
      rw [map_mul, map_sub, map_pow, htcC, htcC, htcX, hφdiv, hφkq,
        OddDescent.kappaOdd_eq, hc1def]
    have htcoeff0 : toClosureFrac
          (C (((-1 : ℚ) ^ ((n - 1) / 2) * n) / ((n : ℚ) - 1))
            * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2) ^ (n - 1))
        = c0 * OddDescent.kappaOdd n ^ (n - 1) := by
      rw [map_mul, map_pow, map_sub, map_pow, htcC, htcC, htcX, hφkqdiv, hφkq,
        OddDescent.kappaOdd_eq, hc0def]
    have hf_norm : serreAnOverFracOdd n
        = X ^ n - C (c1 * OddDescent.kappaOdd n) * X ^ (n - 1)
          + C (c0 * OddDescent.kappaOdd n ^ (n - 1)) := by
      rw [serreAnOverFracOdd, serreAnFamilyOdd]
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C]
      rw [htcoeff1, htcoeff0]
    -- Normal form of the base cover after the odd substitution.
    have hcomp : (OddDescent.substFieldHomOdd n hn2).comp
          (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase)
        = OddDescent.substRingHomOdd n := by
      refine RingHom.ext fun x ↦ ?_
      exact OddDescent.substFieldHomOdd_algebraMap n hn2 x
    have hkey : (linearCoverC (serreBaseP n)).map (OddDescent.substRingHomOdd n)
        = X ^ n - C c1 * X ^ (n - 1) - C (OddDescent.substValOdd n) := by
      rw [linearCoverC, serreBaseP]
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C, OddDescent.substRingHomOdd_C, OddDescent.substRingHomOdd_X]
      rw [OddDescent.algQbarGeom_eq_C, ← hc1def]
    have hg_norm : g = X ^ n - C c1 * X ^ (n - 1) - C (OddDescent.substValOdd n) := by
      rw [hgdef, serreBaseGeomPoly, linearCoverGeom, OddDescent.algebraMap_baseTOdd_eq n hn2,
        Polynomial.map_map, hcomp, hkey]
    -- Core scalar identity for the constant term.
    have hc0' : c0 = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C (OddDescent.kbConst n))
        / algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C ((n : AlgebraicClosure ℚ) - 1)) := by
      rw [hc0def, ← OddDescent.algQbarGeom_eq_C, ← OddDescent.algQbarGeom_eq_C,
        ← OddDescent.algQbarGeom_eq_C, map_div₀]
    have hκsv : OddDescent.kappaOdd n * OddDescent.substValOdd n = -c0 := by
      rw [OddDescent.kappaOdd_mul_substValOdd n hn2, hc0', neg_div]
    have hpow : OddDescent.kappaOdd n ^ n
        = OddDescent.kappaOdd n * OddDescent.kappaOdd n ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hconst : c0 * OddDescent.kappaOdd n ^ (n - 1)
        = -(OddDescent.kappaOdd n ^ n * OddDescent.substValOdd n) := by
      rw [hpow]
      linear_combination (OddDescent.kappaOdd n ^ (n - 1)) * hκsv
    have hmid : c1 * OddDescent.kappaOdd n * OddDescent.kappaOdd n ^ (n - 1)
        = OddDescent.kappaOdd n ^ n * c1 := by
      rw [hpow]
      ring
    -- The scaling identity `serreAnOverFracOdd.comp (Cκ·X) = C(κⁿ)·g`.
    have hcompeq : (serreAnOverFracOdd n).comp (C (OddDescent.kappaOdd n) * X)
        = C (OddDescent.kappaOdd n ^ n) * g := by
      rw [hf_norm, hg_norm]
      simp only [add_comp, sub_comp, mul_comp, pow_comp, C_comp, X_comp]
      rw [mul_pow, mul_pow, ← C_pow, ← C_pow, mul_sub, mul_sub,
        ← mul_assoc (C (c1 * OddDescent.kappaOdd n)), ← C_mul, hmid,
        ← mul_assoc (C (OddDescent.kappaOdd n ^ n)) (C c1), ← C_mul, ← C_mul, hconst, map_neg]
      ring
    -- `serreBaseGeomPoly` splits in the splitting field of `serreAnOverFracOdd`.
    set φ := algebraMap GeomBase (serreAnOverFracOdd n).SplittingField with hφ
    have hinjφ : Function.Injective φ :=
      FaithfulSMul.algebraMap_injective GeomBase _
    have hφκn : φ (OddDescent.kappaOdd n ^ n) ≠ 0 :=
      (map_ne_zero_iff φ hinjφ).mpr (pow_ne_zero _ (OddDescent.kappaOdd_ne_zero n))
    have key := congrArg (Polynomial.map φ) hcompeq
    simp only [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X] at key
    have hRHSsplit : (((serreAnOverFracOdd n).map φ).comp
        (C (φ (OddDescent.kappaOdd n)) * X)).Splits := by
      let _ : Invertible (φ (OddDescent.kappaOdd n)) :=
        invertibleOfNonzero ((map_ne_zero_iff φ hinjφ).mpr (OddDescent.kappaOdd_ne_zero n))
      exact (SplittingField.splits (serreAnOverFracOdd n)).comp_of_natDegree_le_one_of_invertible
        ((natDegree_C_mul_le _ _).trans (le_of_eq natDegree_X))
        (by
          rw [leadingCoeff_C_mul_X]
          infer_instance)
    have hg_split_scaled : (C (φ (OddDescent.kappaOdd n ^ n)) * (g.map φ)).Splits :=
      key ▸ hRHSsplit
    have hunit : g.map φ = C ((φ (OddDescent.kappaOdd n ^ n))⁻¹)
        * (C (φ (OddDescent.kappaOdd n ^ n)) * (g.map φ)) := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hφκn, C_1, one_mul]
    have hsplit_g : (g.map φ).Splits := by
      rw [hunit]
      exact hg_split_scaled.C_mul _
    have htower : (serreBaseGeomPoly n).map
          (algebraMap EvenDescent.BaseT (serreAnOverFracOdd n).SplittingField)
        = g.map φ := by
      rw [hgdef, Polynomial.map_map, hφ,
        ← IsScalarTower.algebraMap_eq EvenDescent.BaseT GeomBase]
    have hfsplitE : ((serreBaseGeomPoly n).map
        (algebraMap EvenDescent.BaseT (serreAnOverFracOdd n).SplittingField)).Splits := by
      rw [htower]
      exact hsplit_g
    -- Assemble via the abstract lower bound.
    have hlow := OddDescent.factorial_le_two_finrank
      (K := EvenDescent.BaseT) (K' := GeomBase)
      (E := (serreAnOverFracOdd n).SplittingField)
      (serreBaseGeomPoly n) (serreBaseGeomPoly_separable n hn2)
      (serreBaseGeomPoly_natDegree n hn2)
      (serreBaseGeomPoly_galActionHom_surjective n hn)
      (OddDescent.finrank_baseT_geomBaseOdd n hn2) hfsplitE
    rw [Gal.card_of_separable (serreAnOverFracOdd_separable n hn2 hodd)]
    exact hlow

/-- **[monodromy core — geometric, proved from the cardinality input]** The image of the permutation
representation of the
geometric Galois group of `serreAnFamilyOdd n` over `ℚ̄(U)` is **exactly the alternating group** on
the roots.

Odd mirror of `an_geometric_galois_alternating`.  This follows from the group-theoretic core
`QuadraticDescent.galActionHom_range_eq_alternating_of_card` once the root count (`n`) and the
single cardinality fact `an_geometric_card_gal_odd` (`2 · |(serreAnOverFracOdd n).Gal| = n!`) are
supplied.  The cardinality comes from odd descent along the shared Serre base cover: the base
cover `serreBaseGeomPoly n` over `BaseT ≅ ℚ̄(S)` has full symmetric geometric monodromy
(`serreBaseGeomPoly_galActionHom_surjective`), and the **odd rational** substitution
`S ↦ −k/((n−1)(k−U²))` base-changes it, after clearing denominators and rescaling the root by
`c = k − U²`, to `serreAnOverFracOdd n`; with the degree-`2` extension `GeomBase / BaseT`
(`OddDescent.finrank_baseT_geomBaseOdd`) and the even-permutation certificate
`an_geometric_le_alternating_odd`, the tower bound pins the group to `Aₙ`. -/
theorem an_geometric_galois_alternating_odd (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    (Gal.galActionHom (serreAnOverFracOdd n) (serreAnOverFracOdd n).SplittingField).range
      = alternatingGroup ((serreAnOverFracOdd n).rootSet (serreAnOverFracOdd n).SplittingField) := by
  refine QuadraticDescent.galActionHom_range_eq_alternating_of_card (serreAnOverFracOdd n)
    ?_ (an_geometric_card_gal_odd n hn hodd)
  rw [Polynomial.card_rootSet_eq_natDegree (serreAnOverFracOdd_separable n (by omega) hodd)
      (SplittingField.splits _), serreAnOverFracOdd_natDegree n (by omega)]

/-! ## Assembly: absolute irreducibility of the descended resolvent -/

/-- **[assembly, proved from the reduction + deep geometric input]** The descended resolvent `G` of
`serreAnFamilyOdd n` is absolutely irreducible.  This has exactly the statement of
`AlternatingFamily.anResolvent_abs_irreducible_odd`.  Odd mirror of
`anResolvent_abs_irreducible'`.

For odd `n`, `Odd n ∧ 2 ≤ n ⟹ 3 ≤ n` (via `omega`), supplying the `3 ≤ n` needed by the deep
geometric input. -/
theorem anResolvent_abs_irreducible_odd' (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n)
    (G : Polynomial (Polynomial ℚ)) (hGmonic : G.Monic)
    (hG : IsAltResolvent n (serreAnFamilyOdd n) G) :
    Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) := by
  have hn3 : 3 ≤ n := by
    rcases hodd with ⟨m, rfl⟩
    omega
  exact abs_irreducible_of_geometric_galois_alternating_odd n hn hodd G hGmonic hG
    (an_geometric_galois_alternating_odd n hn3 hodd)

end AlternatingFamily

end
