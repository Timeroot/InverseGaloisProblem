/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.DorgeBauer
import InverseGalois.Hilbert.Analytic.RittComposition

/-!
# Newton–Puiseux monodromy input for the Morse family

This file isolates the deep **geometric monodromy** fact needed to prove that the geometric
Galois group of the Morse trinomial family `Xⁿ − X − T` over the geometric base field
`ℚ̄(T)` is the full symmetric group `Sₙ`.

It sits *between* `InverseGalois.Hilbert.Analytic.DorgeBauer` (which develops the analytic Newton–Puiseux /
branch theory used for Hilbert's Irreducibility Theorem) and
`InverseGalois.Resolvent.ResolventFamily` (which consumes the result here to prove
`morse_gal_generated_by_swaps`).

## Overview of the mathematics

Let `g(X) = Xⁿ − X ∈ ℚ̄[X]`.  This is a **Morse polynomial**: its critical points (the roots
of `g′ = nXⁿ⁻¹ − 1`) are simple and have pairwise distinct critical values.  Consider the
one-parameter family `g(X) = T`, i.e. the polynomial `familyPoly = Xⁿ − X − T ∈ ℚ̄(T)[X]`
(`morseGeomPoly`).  Its splitting field over `ℚ̄(T)` is the function field of the cover
`X ↦ g(X)` of the affine `T`-line, branched over the finitely many critical values of `g`
(and `∞`).

The **classical monodromy computation** says:

* over each simple finite branch point (critical value of `g`) exactly two sheets come
  together as a square-root (Puiseux) branch, so the local monodromy / inertia generator is a
  **transposition** of the corresponding two roots;
* the affine line is simply connected, so these local inertia groups **generate** the whole
  geometric Galois group; and since a Morse polynomial has `n − 1` distinct critical values
  whose transpositions form a connected (tree) graph on the `n` sheets, they generate `Sₙ`.

* `morseGeomPoly_range_contains_generating_swaps` — the range of the permutation
  representation `galActionHom` contains a set of transpositions of the roots that generates
  the full symmetric group.

The isolated input is *equivalent* to the geometric surjectivity result it is used to prove
(if the group is `Sₙ` then all swaps lie in the range and generate; conversely the transfer
lemma recovers surjectivity), so it faithfully captures the genuine mathematical crux without
weakening the statement. -/

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

/-- The abstract geometric base field `ℚ̄(T)`. -/
abbrev GeomBase : Type := FractionRing (Polynomial (AlgebraicClosure ℚ))

/-- The polynomial `g(X) − T = Xⁿ − X − T` viewed over `ℚ̄[T]` (with the coefficient variable
`C X` playing the role of `T`). -/
noncomputable def genPolyC (n : ℕ) : (Polynomial (AlgebraicClosure ℚ))[X] :=
  X ^ n - X - C X

/-- The Morse family `Xⁿ − X − T` base-changed to the geometric base field `ℚ̄(T)`.  This is
definitionally the same polynomial as `ResolventFamily.morseOverFrac n`, re-expressed with the
coefficient field already extended to `ℚ̄` (see `ResolventFamily.morseOverFrac_eq_morseGeomPoly`). -/
noncomputable def morseGeomPoly (n : ℕ) : GeomBase[X] :=
  (genPolyC n).map (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase)

/-- `genPolyC n = Xⁿ − X − C X` is monic for `n ≥ 2`. -/
theorem genPolyC_monic (n : ℕ) (hn : 2 ≤ n) : (genPolyC n).Monic := by
  have h : genPolyC n = X ^ n - (X + C X) := by
    unfold genPolyC
    ring
  rw [h]
  apply Polynomial.monic_X_pow_sub
  have hle : (X + C X : (Polynomial (AlgebraicClosure ℚ))[X]).degree ≤ 1 := by
    refine le_trans (degree_add_le _ _) ?_
    rw [degree_X]
    refine max_le le_rfl (le_trans degree_C_le ?_)
    norm_num
  refine lt_of_le_of_lt hle ?_
  have hlt : (1 : ℕ) < n := by omega
  exact_mod_cast hlt

/-- `morseGeomPoly n` is monic for `n ≥ 2`. -/
theorem morseGeomPoly_monic (n : ℕ) (hn : 2 ≤ n) : (morseGeomPoly n).Monic :=
  (genPolyC_monic n hn).map _

/-- `genPolyC n = Xⁿ − X − C X` is irreducible over `ℚ̄[T]`.

The polynomial is *linear* in the coefficient variable `T` (written `C X` here): applying the
variable-swap automorphism `Polynomial.Bivariate.swap` turns it into (a unit multiple of)
`X − C (Xⁿ − X)`, which is irreducible by `Polynomial.irreducible_X_sub_C`.  Irreducibility is
transported back along the algebra automorphism.  (No lower bound on `n` is needed.) -/
theorem genPolyC_irreducible (n : ℕ) : Irreducible (genPolyC n) := by
  have hswap : Polynomial.Bivariate.swap (genPolyC n) = -(Polynomial.X - C (X ^ n - X)) := by
    unfold genPolyC
    simp
  have hirr : Irreducible (Polynomial.Bivariate.swap (genPolyC n)) := by
    rw [hswap]
    have h := irreducible_X_sub_C (R := (Polynomial (AlgebraicClosure ℚ))) (X ^ n - X)
    have hassoc : Associated (X - C (X ^ n - X) : (Polynomial (AlgebraicClosure ℚ))[X])
        (-(X - C (X ^ n - X))) := ⟨-1, by simp⟩
    exact hassoc.irreducible h
  exact (MulEquiv.irreducible_iff
    (Polynomial.Bivariate.swap (R := AlgebraicClosure ℚ)).toMulEquiv).mp hirr

/-- `morseGeomPoly n = Xⁿ − X − T` is irreducible over the geometric base field `ℚ̄(T)`.

This follows from irreducibility over `ℚ̄[T]` (`genPolyC_irreducible`) by Gauss's lemma
(`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`), since the polynomial is
monic. -/
theorem morseGeomPoly_irreducible (n : ℕ) (hn : 2 ≤ n) : Irreducible (morseGeomPoly n) := by
  rw [morseGeomPoly]
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (genPolyC_monic n hn)).mp (genPolyC_irreducible n)

/-- The polynomial always splits in its own splitting field (local `Fact` instance so that the
permutation representation `galActionHom` is well-formed). -/
local instance splitsInSplittingField' (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

open scoped Classical in
/--

For a polynomial `p` that splits in `E`, if the range of the permutation representation
`galActionHom p E` contains a set `S` of transpositions of the roots that generates the full
symmetric group, then the Galois group `p.Gal` itself admits a generating set each of whose
elements acts on the roots as a transposition. -/
theorem gal_swaps_of_range_swaps
    {F E : Type} [Field F] [Field E] [Algebra F E] (p : F[X])
    [Fact ((p.map (algebraMap F E)).Splits)]
    (hex : ∃ S : Set (Equiv.Perm (p.rootSet E)),
        (∀ t ∈ S, t.IsSwap) ∧ (∀ t ∈ S, t ∈ (Gal.galActionHom p E).range) ∧
        Subgroup.closure S = ⊤) :
    ∃ S' : Set p.Gal,
      (∀ σ ∈ S', (Gal.galActionHom p E σ).IsSwap) ∧ Subgroup.closure S' = ⊤ := by
  have hinj := Gal.galActionHom_injective p E
  set φ := Gal.galActionHom p E
  obtain ⟨S, hP, hrange, hgen⟩ := hex
  refine ⟨φ ⁻¹' S, fun σ hσ ↦ hP _ hσ, ?_⟩
  have himg : φ '' (φ ⁻¹' S) = S := by
    rw [Set.image_preimage_eq_inter_range]
    exact Set.inter_eq_left.mpr (fun t ht ↦ hrange t ht)
  have hmap : Subgroup.map φ (Subgroup.closure (φ ⁻¹' S)) = ⊤ := by
    rw [MonoidHom.map_closure, himg, hgen]
  have h2 := Subgroup.comap_map_eq_self_of_injective hinj (Subgroup.closure (φ ⁻¹' S))
  rw [hmap] at h2
  simpa using h2.symm

/-- **Transfer of preprimitivity to the range subgroup.**

For a polynomial `p` splitting in `E`, if the Galois group `p.Gal` acts preprimitively on the
roots (via `galAction`), then the *range* subgroup of the permutation representation
`galActionHom p E` also acts preprimitively.  The corestriction `p.Gal → range` is surjective
and the identity on the roots is equivariant along it, so `MulAction.isPreprimitive_congr`
applies. -/
theorem isPreprimitive_range_of_isPreprimitive
    {F E : Type} [Field F] [Field E] [Algebra F E] (p : F[X])
    [Fact ((p.map (algebraMap F E)).Splits)]
    (h : MulAction.IsPreprimitive p.Gal (p.rootSet E)) :
    MulAction.IsPreprimitive (Gal.galActionHom p E).range (p.rootSet E) := by
  set φ := (Gal.galActionHom p E).rangeRestrict with hφdef
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective _
  let f : p.rootSet E →ₑ[φ] p.rootSet E :=
    { toFun := id
      map_smul' := by
        intro m a
        show m • a = (φ m) • a
        rfl }
  exact (MulAction.isPreprimitive_congr (f := f) hφ Function.bijective_id).mp h

/-
`genPolyC n = Xⁿ − X − C X` has degree `n` for `n ≥ 2`.
-/
theorem genPolyC_natDegree (n : ℕ) (hn : 2 ≤ n) : (genPolyC n).natDegree = n := by
  unfold genPolyC
  rw [Polynomial.natDegree_sub_C]
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num [hn]
  grind

/-
`morseGeomPoly n = Xⁿ − X − T` has degree `n` for `n ≥ 2`.
-/
theorem morseGeomPoly_natDegree (n : ℕ) (hn : 2 ≤ n) : (morseGeomPoly n).natDegree = n := by
  convert Polynomial.natDegree_map_eq_of_injective _ _
  · rw [genPolyC_natDegree n hn]
  · exact IsFractionRing.injective _ _

/-
`morseGeomPoly n = Xⁿ − X − T` is separable over `ℚ̄(T)` for `n ≥ 2`.

A common root `α` of the polynomial and its derivative `nXⁿ⁻¹ − 1` would force, from
`nαⁿ⁻¹ = 1` and `αⁿ − α = T`, a polynomial relation over `ℚ̄` satisfied by the transcendental
`T`, which is impossible.
-/
theorem morseGeomPoly_separable (n : ℕ) (hn : 2 ≤ n) : (morseGeomPoly n).Separable := by
  grind only [Irreducible.separable, morseGeomPoly_irreducible]

/-- The root set of `morseGeomPoly n` in its splitting field has exactly `n` elements: the
polynomial is separable (`morseGeomPoly_separable`) of degree `n` (`morseGeomPoly_natDegree`)
and splits in its own splitting field. -/
theorem morseGeomPoly_card_rootSet (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) = n := by
  rw [Polynomial.card_rootSet_eq_natDegree (morseGeomPoly_separable n hn)
      (SplittingField.splits (morseGeomPoly n)), morseGeomPoly_natDegree n hn]

/--

When the degree `n` is *prime*, primitivity — the first half of the deep monodromy input
`morseGeomPoly_monodromy_input` — requires no geometric input at all: the action is transitive
(`Gal.galAction_isPretransitive` from `morseGeomPoly_irreducible`) on a set of prime
cardinality `n` (`morseGeomPoly_card_rootSet`), and by `MulAction.IsBlock.ncard_dvd_card` the
cardinality of any nonempty block divides `n`, hence is `1` or `n`; that is, every block is
trivial.

**Scope.** This prime-degree argument is *not* enough for the intended application
`IsInverseGalois.perm_fin`, which realises `Sₙ` for **every** `n` (composite `n` included).
For composite `n`, primitivity is genuinely the indecomposability of `Xⁿ − X`, whose algebraic
core is proved below in `xnSubX_indecomposable`. -/
theorem morseGeomPoly_block_ncard_dvd (n : ℕ) (hn : 2 ≤ n)
    {B : Set ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField)}
    (hB : MulAction.IsBlock (morseGeomPoly n).Gal B) (hBne : B.Nonempty) : B.ncard ∣ n := by
  have htrans : MulAction.IsPretransitive (morseGeomPoly n).Gal
      ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :=
    Gal.galAction_isPretransitive _ _ (morseGeomPoly_irreducible n hn)
  have hdvd := @MulAction.IsBlock.ncard_dvd_card _ _ _
    (Gal.galAction (morseGeomPoly n) (morseGeomPoly n).SplittingField) htrans B hB hBne
  rwa [Nat.card_eq_fintype_card, morseGeomPoly_card_rootSet n hn] at hdvd

theorem morseGeomPoly_blocks_trivial_of_prime (n : ℕ) (hn : n.Prime)
    {B : Set ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField)}
    (hB : MulAction.IsBlock (morseGeomPoly n).Gal B) : MulAction.IsTrivialBlock B := by
  rcases B.eq_empty_or_nonempty with hB0 | hBne
  · refine Or.inl ?_
    rw [hB0]
    exact Set.subsingleton_empty
  · have hdvd := morseGeomPoly_block_ncard_dvd n hn.two_le hB hBne
    rcases (Nat.dvd_prime hn).mp hdvd with h1 | hn'
    · obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp h1
      exact Or.inl (Set.subsingleton_singleton)
    · refine Or.inr ?_
      have hfin : (Set.univ : Set ((morseGeomPoly n).rootSet
          (morseGeomPoly n).SplittingField)).Finite := Set.finite_univ
      have hcu : (Set.univ : Set ((morseGeomPoly n).rootSet
          (morseGeomPoly n).SplittingField)).ncard = n := by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card, morseGeomPoly_card_rootSet n hn.two_le]
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ B) ?_ hfin
      rw [hcu, hn']

/-!
### The algebraic core of primitivity for **all** degrees `n`

The prime-degree primitivity above (`morseGeomPoly_blocks_trivial_of_prime`) is **not**
enough for the intended application `IsInverseGalois.perm_fin`, which needs the geometric
Galois group to be `Sₙ` for *every* `n` (composite `n` included).  For composite `n` the
transitive-action-on-a-prime-set trick fails, and primitivity of the monodromy action is
equivalent — via the Galois correspondence between blocks and intermediate fields, together
with Lüroth's theorem and the total ramification of `g(X) = Xⁿ − X` at `∞` — to the
**indecomposability of the polynomial `Xⁿ − X`**: there is no factorisation
`Xⁿ − X = h ∘ g` with `deg h, deg g ≥ 2`.

We prove that indecomposability here (`xnSubX_indecomposable`) as the concrete, reusable
algebraic content of the primitivity half.  The proof is the classical Morse argument via a
**critical-point count**.  Write `a = deg h ≥ 2`, `b = deg g ≥ 2`, so `n = a·b`.
Differentiating `Xⁿ − X = h ∘ g` gives `g₀′ := n·Xⁿ⁻¹ − 1 = g′ · (h′ ∘ g)`, so every root of
the separable polynomial `g₀′` (`xnSubX_deriv_separable`, hence `n − 1 = a·b − 1` *distinct*
roots) is a root of `g′` or of `h′ ∘ g`.  There are at most `b − 1` roots of `g′`, and the
map `x ↦ g(x)` sends the roots of `h′ ∘ g` into the `≤ a − 1` roots of `h′` **injectively**:
two roots `x₁, x₂` of `h′ ∘ g` with `g(x₁) = g(x₂) = β` are both critical points of `Xⁿ − X`
(being roots of `g₀′`) with the same critical value `h(β)`, so `x₁ = x₂` by
`xnSubX_crit_value_inj`.  Hence `a·b − 1 ≤ (b − 1) + (a − 1)`, i.e. `(a − 1)(b − 1) ≤ 0`,
contradicting `a, b ≥ 2`.
-/

/-- The critical points of `g(X) = Xⁿ − X` (the roots of `g′ = n·Xⁿ⁻¹ − 1`) have pairwise
distinct critical values: if `a, b` satisfy `n·aⁿ⁻¹ = 1 = n·bⁿ⁻¹` and `aⁿ − a = bⁿ − b`, then
`a = b`.  (Because `aⁿ⁻¹ = 1/n` gives the critical value `aⁿ − a = a·(1/n − 1)`, a nonzero
multiple of `a`.) -/
theorem xnSubX_crit_value_inj (n : ℕ) (hn : 2 ≤ n) {a b : AlgebraicClosure ℚ}
    (ha : (n : AlgebraicClosure ℚ) * a ^ (n - 1) = 1)
    (hb : (n : AlgebraicClosure ℚ) * b ^ (n - 1) = 1)
    (hval : a ^ n - a = b ^ n - b) : a = b := by
  have hn0 : (n : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hae : a ^ n = a * a ^ (n-1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hbe : b ^ n = b * b ^ (n-1) := by
    rw [← pow_succ']
    congr 1
    omega
  have han : a ^ n = a * (n:AlgebraicClosure ℚ)⁻¹ := by
    rw [hae]
    field_simp
    linear_combination a * ha
  have hbn : b ^ n = b * (n:AlgebraicClosure ℚ)⁻¹ := by
    rw [hbe]
    field_simp
    linear_combination b * hb
  rw [han, hbn] at hval
  have hfac : (a - b) * ((n:AlgebraicClosure ℚ)⁻¹ - 1) = 0 := by linear_combination hval
  have hne : (n:AlgebraicClosure ℚ)⁻¹ - 1 ≠ 0 := by
    intro h
    have h1 : (n:AlgebraicClosure ℚ)⁻¹ = 1 := by linear_combination h
    rw [inv_eq_one] at h1
    have : (n:ℕ) = 1 := by exact_mod_cast h1
    omega
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hne

/-- The derivative `g′ = n·Xⁿ⁻¹ − 1` of `g(X) = Xⁿ − X` is separable over `ℚ̄` for `n ≥ 2`:
it is (a unit multiple of) the binomial `Xⁿ⁻¹ − (1/n)`, which is separable in characteristic
zero. -/
theorem xnSubX_deriv_separable (n : ℕ) (hn : 2 ≤ n) :
    (C (n : AlgebraicClosure ℚ) * X ^ (n - 1) - 1 : (AlgebraicClosure ℚ)[X]).Separable := by
  have hn0 : (n : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (C (n : AlgebraicClosure ℚ) * X ^ (n - 1) - 1 : (AlgebraicClosure ℚ)[X])
      = C (n:AlgebraicClosure ℚ) * (X ^ (n-1) - C ((n:AlgebraicClosure ℚ)⁻¹)) := by
    rw [mul_sub, ← C_mul, mul_inv_cancel₀ hn0]
    simp
  rw [key]
  have hsep : (X ^ (n-1) - C ((n:AlgebraicClosure ℚ)⁻¹) : (AlgebraicClosure ℚ)[X]).Separable := by
    apply Polynomial.separable_X_pow_sub_C
    · exact Nat.cast_ne_zero.mpr (by omega)
    · exact inv_ne_zero hn0
  exact Separable.unit_mul (isUnit_C.mpr (Ne.isUnit hn0)) hsep

open scoped Classical in
/-- **The Morse injectivity bound.**  The number of *distinct* roots of `h′ ∘ g` is at most
the number of distinct roots of `h′`.  This is the crux of the Morse argument: the map
`x ↦ g(x)` sends distinct roots of `h′ ∘ g` injectively into the roots of `h′`, because two
roots `x₁, x₂` with `g(x₁) = g(x₂)` are critical points of `Xⁿ − X` (they are roots of
`g₀′ = g′ · (h′ ∘ g)`) with the same critical value, forcing `x₁ = x₂` via
`xnSubX_crit_value_inj`. -/
theorem xnSubX_comp_deriv_distinct_roots_le (n : ℕ) (hn : 2 ≤ n)
    {h g : (AlgebraicClosure ℚ)[X]} (_hh : 2 ≤ h.natDegree) (_hg : 2 ≤ g.natDegree)
    (h_eq : (X ^ n - X : (AlgebraicClosure ℚ)[X]) = h.comp g) :
    ((derivative h).comp g).roots.toFinset.card ≤ (derivative h).roots.toFinset.card := by
  -- Let `D := C (n:F) * X^(n-1) - 1`. Then `D = derivative g * dh.comp g`.
  set D : (AlgebraicClosure ℚ)[X] := C (n : AlgebraicClosure ℚ) * X ^ (n - 1) - 1
  have hD : D = derivative g * (derivative h).comp g := by
    convert congr_arg Polynomial.derivative h_eq using 1
    · simp +zetaDelta at *
      norm_num [Polynomial.derivative_pow]
    · rw [Polynomial.derivative_comp]
  apply Finset.card_le_card_of_injOn (f := fun x ↦ g.eval x)
  · intro x hx
    simp_all [Polynomial.eval_comp]
    intro H
    simp_all
  · intro x hx y hy
    have := congr_arg (Polynomial.eval x) hD
    have := congr_arg (Polynomial.eval y) hD
    norm_num at *
    have h_critical : ∀ x : AlgebraicClosure ℚ,
        (derivative h).eval (g.eval x) = 0 → (n : AlgebraicClosure ℚ) * x ^ (n - 1) = 1 := by
      intro x hx
      replace hD := congr_arg (Polynomial.eval x) hD
      simp_all [Polynomial.eval_comp]
      simp +zetaDelta at *
      exact eq_of_sub_eq_zero hD
    have h_critical_value : ∀ x : AlgebraicClosure ℚ,
        (derivative h).eval (g.eval x) = 0 → x ^ n - x = h.eval (g.eval x) := by
      intro x hx
      replace h_eq := congr_arg (Polynomial.eval x) h_eq
      simp_all
    intro h
    refine xnSubX_crit_value_inj n hn (h_critical x hx.2) (h_critical y hy.2) ?_
    rw [h_critical_value x hx.2, h_critical_value y hy.2, h]

/-- **Indecomposability of `Xⁿ − X` (all `n ≥ 2`).**

There is no factorisation `Xⁿ − X = h ∘ g` of the Morse polynomial `g₀(X) = Xⁿ − X` over
`ℚ̄` into a composite of two polynomials each of degree `≥ 2`.  This is the algebraic heart of
the primitivity of the geometric monodromy action of `Xⁿ − X − T` for *composite* `n`
(prime `n` being handled directly by `morseGeomPoly_blocks_trivial_of_prime`).

The proof is the classical Morse critical-point count (see the section note above), using
`xnSubX_crit_value_inj` (distinct critical values) and `xnSubX_deriv_separable` (separability
of `g₀′ = n·Xⁿ⁻¹ − 1`). -/
theorem xnSubX_indecomposable (n : ℕ) (hn : 2 ≤ n)
    {h g : (AlgebraicClosure ℚ)[X]} (hh : 2 ≤ h.natDegree) (hg : 2 ≤ g.natDegree) :
    (X ^ n - X : (AlgebraicClosure ℚ)[X]) ≠ h.comp g := by
  classical
  intro h_eq
  set a := h.natDegree with ha_def
  set b := g.natDegree with hb_def
  have hCne : (n : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdegXnX : (X ^ n - X : (AlgebraicClosure ℚ)[X]).natDegree = n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp
    omega
  have hab : a * b = n := by
    have h2 := congrArg Polynomial.natDegree h_eq
    rw [hdegXnX, natDegree_comp] at h2
    rw [← ha_def, ← hb_def] at h2
    exact h2.symm
  set D : (AlgebraicClosure ℚ)[X] := C (n : AlgebraicClosure ℚ) * X ^ (n - 1) - 1 with hD_def
  have hDeq : D = derivative g * (derivative h).comp g := by
    have h1 : derivative (X ^ n - X : (AlgebraicClosure ℚ)[X]) = D := by
      simp [hD_def, derivative_X_pow]
    rw [← h1, h_eq, derivative_comp]
  have hDsep : D.Separable := xnSubX_deriv_separable n hn
  have hDdeg : D.natDegree = n - 1 := by
    have hstep : D.natDegree = (C (n:AlgebraicClosure ℚ) * X^(n-1)).natDegree := by
      rw [hD_def]
      refine natDegree_sub_eq_left_of_natDegree_lt ?_
      rw [natDegree_C_mul_X_pow _ _ hCne, natDegree_one]
      omega
    rw [hstep, natDegree_C_mul_X_pow _ _ hCne]
  have hDne : D ≠ 0 := by
    intro h0
    rw [h0] at hDdeg
    simp at hDdeg
    omega
  have hsplit : D.Splits := IsAlgClosed.splits D
  have hcardD : D.roots.toFinset.card = n - 1 := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hDsep),
        (splits_iff_card_roots.mp hsplit), hDdeg]
  have hprodne : derivative g * (derivative h).comp g ≠ 0 := hDeq ▸ hDne
  have hrootseq : D.roots = (derivative g).roots + ((derivative h).comp g).roots := by
    rw [hDeq]
    exact roots_mul hprodne
  have hsub : D.roots.toFinset =
      (derivative g).roots.toFinset ∪ ((derivative h).comp g).roots.toFinset := by
    rw [hrootseq, Multiset.toFinset_add]
  have hcardA : (derivative g).roots.toFinset.card ≤ b - 1 :=
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_derivative_le _))
  have hcardB : ((derivative h).comp g).roots.toFinset.card ≤ a - 1 :=
    (xnSubX_comp_deriv_distinct_roots_le n hn hh hg h_eq).trans
      ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_derivative_le _)))
  have hmain : n - 1 ≤ (b - 1) + (a - 1) := by
    rw [← hcardD, hsub]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add hcardA hcardB)
  have hprod : a + b ≤ a * b := by nlinarith [hh, hg]
  rw [hab] at hprod
  omega

/-
**Maximality of the root stabiliser** — the sharp field-theoretic core of primitivity.

The stabiliser in `G = (morseGeomPoly n).Gal` of any root `a` is a *coatom* (a maximal proper
subgroup).  Under the Galois correspondence for the splitting field `L / ℚ̄(T)`, the
intermediate group `stabilizer G a ≤ H ≤ ⊤` corresponds to an intermediate field
`ℚ̄(T) ⊆ M ⊆ fixedField (stabilizer G a) = ℚ̄(T)(a) = ℚ̄(a)` (a rational function field, since
`a` is a root, `T = aⁿ − a`).  Maximality of the stabiliser is therefore exactly the statement
that there is *no* intermediate field strictly between `ℚ̄(aⁿ − a)` and `ℚ̄(a)`; by Lüroth's
theorem such a field would be `ℚ̄(w)`, yielding a nontrivial polynomial decomposition
`Xⁿ − X = h ∘ g` (`deg h, deg g ≥ 2`), impossible by `xnSubX_indecomposable`.

**Galois-correspondence transfer.**  For a finite Galois extension `E / F`, the fixing
subgroup of an intermediate field `M` is a coatom (a maximal proper subgroup) if and only if
`M` is an atom (covers the base field `F`).  This is the order-reversing Galois correspondence
`IsGalois.intermediateFieldEquivSubgroup` combined with the fact that an order isomorphism onto
an order dual turns atoms into coatoms. -/
theorem isCoatom_fixingSubgroup_iff_isAtom {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (M : IntermediateField F E) :
    IsCoatom M.fixingSubgroup ↔ IsAtom M := by
  exact OrderIso.isAtom_iff (IsGalois.intermediateFieldEquivSubgroup) M

/-- The restriction endomorphism `Gal.restrict p SF : p.Gal →* p.Gal` (to the splitting field
itself) is bijective: it is surjective (`Gal.restrict_surjective`, `SF` normal) on a finite
group. -/
theorem morseGeomPoly_restrict_bijective (n : ℕ) (_hn : 2 ≤ n) :
    Function.Bijective
      (Gal.restrict (morseGeomPoly n) (morseGeomPoly n).SplittingField) := by
  refine ⟨?_, Gal.restrict_surjective _ _⟩
  exact Finite.injective_iff_surjective.mpr (Gal.restrict_surjective _ _)

/-
The stabiliser of the root `a` under the Galois action is the image, under the (bijective)
restriction endomorphism `Gal.restrict p SF`, of the fixing subgroup of the intermediate field
`ℚ̄(T)(a)` it generates.

(For `E = SF`, Mathlib's `Gal.galAction` is defined through the conjugating bijection
`rootsEquivRoots`, so the stabiliser is a `Gal.restrict`-image of the fixing subgroup rather
than the fixing subgroup itself; since `Gal.restrict p SF` is a group automorphism this does
not affect `IsCoatom`.)
-/
theorem morseGeomPoly_stabilizer_eq_map_fixingSubgroup (n : ℕ) (hn : 2 ≤ n)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    (@MulAction.stabilizer (morseGeomPoly n).Gal
      (↑((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField)) _
      (Gal.galAction (morseGeomPoly n) (morseGeomPoly n).SplittingField) a)
      = Subgroup.map (Gal.restrict (morseGeomPoly n) (morseGeomPoly n).SplittingField)
          (IntermediateField.fixingSubgroup
            (IntermediateField.adjoin GeomBase
              {(↑a : (morseGeomPoly n).SplittingField)})) := by
  refine le_antisymm ?_ ?_ <;> intro x hx <;> simp_all [Subgroup.mem_map]
  · obtain ⟨y, hy⟩ := (morseGeomPoly_restrict_bijective n hn).surjective x
    refine ⟨y, ?_, hy⟩
    intro x hx
    induction hx using IntermediateField.adjoin_induction
    · replace hx := congr_arg Subtype.val hx
      subst hy
      simp_all only [Set.mem_singleton_iff, Gal.restrict_smul]
    · exact y.commutes _
    · simp_all
    · rw [map_inv₀, ‹y _ = _›]
    · simp_all
  · obtain ⟨y, hy, rfl⟩ := hx
    rw [← Subtype.coe_inj]
    simp [Gal.restrict_smul]
    exact hy _ <| IntermediateField.subset_adjoin GeomBase _ <| Set.mem_singleton _

/-

Via the `ℚ̄`-algebra hom `ℚ̄(X) = RatFunc ℚ̄ →ₐ[ℚ̄] L` (`morseLift`, sending `X ↦ a`, and hence
`ℚ̄(Xⁿ−X) ↦ ℚ̄(aⁿ−a)`), this atom statement follows from the coatom statement
`RatFunc.isCoatom_adjoin_of_indecomposable` applied to `Xⁿ − X` (whose indecomposability is
`xnSubX_indecomposable`).  See `morseGeomPoly_no_intermediate`. -/
theorem morseGeomPoly_adjoin_root_ne_bot (n : ℕ) (hn : 2 ≤ n)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    IntermediateField.adjoin GeomBase {(↑a : (morseGeomPoly n).SplittingField)} ≠ ⊥ := by
  -- Since $a$ is a root of $morseGeomPoly n$, which is irreducible over $GeomBase$, the minimal polynomial of $a$ over $GeomBase$ is $morseGeomPoly n$.
  have h_min_poly : minpoly GeomBase (a : (morseGeomPoly n).SplittingField) = morseGeomPoly n := by
    refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_) <;>
      norm_num [morseGeomPoly_irreducible n hn, morseGeomPoly_monic n hn]
    exact Polynomial.mem_rootSet.mp a.2 |>.2
  intro h
  have h_deg : (minpoly GeomBase (a : (morseGeomPoly n).SplittingField)).natDegree ≤ 1 := by
    have h_deg : ∃ c : GeomBase, (algebraMap GeomBase (morseGeomPoly n).SplittingField) c = a := by
      exact IntermediateField.mem_bot.mp (h ▸ IntermediateField.mem_adjoin_simple_self GeomBase _)
    obtain ⟨c, hc⟩ := h_deg
    have hac : (a : (morseGeomPoly n).SplittingField)
        = (algebraMap GeomBase (morseGeomPoly n).SplittingField) c := hc.symm
    rw [hac]
    simp [minpoly.eq_X_sub_C]
  refine absurd h_deg ?_
  rw [h_min_poly, morseGeomPoly_natDegree n hn]
  linarith

/-!
### The `ℚ̄(a) ≅ ℚ̄(X)` transport for `morseGeomPoly_no_intermediate`

We now prove `morseGeomPoly_no_intermediate` outright.  Writing `x := ↑a ∈ L` and
`tL := xⁿ − x ∈ L`, the root relation gives `tL = algebraMap GeomBase L T` (the image of the
base transcendental `T`).  Since `T` is transcendental over `ℚ̄`, so is `tL`, and hence so is
`x` (an algebraic `x` would make `tL` algebraic).  The `ℚ̄`-algebra hom
`Ψ := RatFunc.liftAlgHom (aeval x) : RatFunc ℚ̄ →ₐ[ℚ̄] L` (well-defined and injective because
`x` is transcendental) sends `RatFunc.X ↦ x` and `algebraMap (Xⁿ − X) ↦ tL`, and its range is
`ℚ̄(x) = adjoin GeomBase {x}` (as a `ℚ̄`-intermediate field).  Pulling an intermediate field
`b < adjoin GeomBase {x}` back along `Ψ` produces an intermediate field of `RatFunc ℚ̄`
containing `ℚ̄(Xⁿ − X)` and `≠ ⊤`, which by `RatFunc.isCoatom_adjoin_of_indecomposable`
(indecomposability being `xnSubX_indecomposable`) must equal `ℚ̄(Xⁿ − X)`; transporting back
gives `b = ⊥`.
-/

open Polynomial in
/-- The root relation: `aeval x (Xⁿ − X) = algebraMap GeomBase L T`, where `x = ↑a` and
`T = algebraMap ℚ̄[X] GeomBase X` is the base transcendental. -/
theorem morse_aeval_gsub (n : ℕ)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    aeval (↑a : (morseGeomPoly n).SplittingField) (X ^ n - X : (AlgebraicClosure ℚ)[X])
      = algebraMap GeomBase (morseGeomPoly n).SplittingField
          (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) := by
  obtain ⟨a_val, ha⟩ := a
  rw [Polynomial.mem_rootSet] at ha
  unfold morseGeomPoly at ha
  unfold genPolyC at ha
  simp_all
  exact eq_of_sub_eq_zero ha.2

/-
The base transcendental `T = algebraMap ℚ̄[X] GeomBase X` is transcendental over `ℚ̄`.
-/
theorem geomBase_gen_transcendental :
    Transcendental (AlgebraicClosure ℚ)
      (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) := by
  rw [transcendental_iff_injective]
  have h_aeval_eq_algebraMap :
      (aeval (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) :
        (AlgebraicClosure ℚ)[X] →ₐ[AlgebraicClosure ℚ] GeomBase)
        = IsScalarTower.toAlgHom (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)[X] GeomBase := by
    ext
    simp [IsScalarTower.toAlgHom]
  rw [h_aeval_eq_algebraMap]
  exact IsFractionRing.injective _ _

/-
A root `x = ↑a` of `morseGeomPoly n` is transcendental over `ℚ̄`.
-/
theorem morse_root_transcendental (n : ℕ)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    Transcendental (AlgebraicClosure ℚ) (↑a : (morseGeomPoly n).SplittingField) := by
  -- By `morse_aeval_gsub n a`, `aeval x (X^n - X) = algebraMap GeomBase L t₀` with t₀ := algebraMap (AlgebraicClosure ℚ)[X] GeomBase X.
  have h_tL : (↑a : (morseGeomPoly n).SplittingField) ^ n
        - (↑a : (morseGeomPoly n).SplittingField)
      = algebraMap GeomBase (morseGeomPoly n).SplittingField
          (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) := by
    convert morse_aeval_gsub n a using 1
    norm_num
  -- Since $t₀$ is transcendental over $\mathbb{Q}$, and $algebraMap GeomBase L$ is injective, $algebraMap GeomBase L t₀$ is also transcendental over $\mathbb{Q}$.
  have h_tL_transcendental : Transcendental (AlgebraicClosure ℚ)
      (algebraMap GeomBase (morseGeomPoly n).SplittingField
        (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X)) := by
    intro h
    convert geomBase_gen_transcendental using 1
    constructor <;> intro h <;> rw [Transcendental] at * <;> simp_all [IsAlgebraic]
  contrapose! h_tL_transcendental
  simp_all [Transcendental]
  rw [← h_tL]
  exact IsAlgebraic.sub (h_tL_transcendental.pow _) h_tL_transcendental

/-- The `ℚ̄`-algebra hom `Ψ : RatFunc ℚ̄ →ₐ[ℚ̄] L` sending `X ↦ ↑a`, well-defined and injective
because `↑a` is transcendental over `ℚ̄`. -/
noncomputable def morseLift (n : ℕ)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    RatFunc (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ] (morseGeomPoly n).SplittingField :=
  RatFunc.liftAlgHom (Polynomial.aeval (↑a : (morseGeomPoly n).SplittingField))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp (morse_root_transcendental n a)))

theorem morseLift_apply_poly (n : ℕ)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) (p : (AlgebraicClosure ℚ)[X]) :
    morseLift n a (algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ)) p)
      = aeval (↑a : (morseGeomPoly n).SplittingField) p := by
  have h := @RatFunc.liftAlgHom_apply_div
  have hnz := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (transcendental_iff_injective.mp (morse_root_transcendental n a))
  convert h (Polynomial.aeval (a : (morseGeomPoly n).SplittingField)) hnz p 1 using 1 <;>
    simp [morseLift]

theorem morseLift_injective (n : ℕ)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    Function.Injective (morseLift n a) := by
  convert RatFunc.liftAlgHom_injective _ _
  exact transcendental_iff_injective.mp (morse_root_transcendental n a)

/-
The range of `Ψ` is `ℚ̄(↑a)`.
-/
theorem morseLift_fieldRange (n : ℕ)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    (morseLift n a).fieldRange
      = IntermediateField.adjoin (AlgebraicClosure ℚ) {(↑a : (morseGeomPoly n).SplittingField)} := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨p, hp⟩ := hx
    simp at hp
    have h_image : p ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) {RatFunc.X} := by
      rw [RatFunc.adjoin_X_top] at *
      trivial
    rw [← hp, IntermediateField.mem_adjoin_simple_iff] at *
    obtain ⟨r, s, rfl⟩ := h_image
    use r, s
    simp [morseLift_apply_poly]
  · simp [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    use RatFunc.X
    convert morseLift_apply_poly n a Polynomial.X using 1
    norm_num

/-
Every element of the base `GeomBase`, mapped into `L`, lies in `ℚ̄(↑aⁿ − ↑a)`.
-/
theorem geomBase_image_mem_adjoin (n : ℕ)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) (y : GeomBase) :
    algebraMap GeomBase (morseGeomPoly n).SplittingField y
      ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
          {(↑a : (morseGeomPoly n).SplittingField) ^ n - ↑a} := by
  -- By `IsFractionRing.div_surjective y` (GeomBase = FractionRing Qbar[X]), obtain num den with den ∈ nonZeroDivisors and `algebraMap Qbar[X] GeomBase num / algebraMap Qbar[X] GeomBase den = y`.
  obtain ⟨num, den, hden, hy⟩ :
      ∃ num den : Polynomial (AlgebraicClosure ℚ),
        den ∈ nonZeroDivisors (Polynomial (AlgebraicClosure ℚ)) ∧
          y = (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase num)
            / (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase den) := by
    have := IsFractionRing.div_surjective (A := Polynomial (AlgebraicClosure ℚ)) y
    tauto
  -- By `IsScalarTower.algebraMap_apply`, we have `algebraMap GeomBase L (algebraMap Qbar[X] GeomBase p) = algebraMap Qbar[X] L p`.
  have h_algebraMap : ∀ p : Polynomial (AlgebraicClosure ℚ),
      algebraMap GeomBase (morseGeomPoly n).SplittingField
          (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase p)
        = aeval (↑a ^ n - ↑a : (morseGeomPoly n).SplittingField) p := by
    intro p
    induction p using Polynomial.induction_on <;> simp_all [Polynomial.aeval_def]
    · rfl
    · have := morse_aeval_gsub n a
      simp_all [pow_succ]
  simp_all [IntermediateField.mem_adjoin_simple_iff]
  exact ⟨num, den, rfl⟩

/-
The base subfield `GeomBase`, restricted to `ℚ̄`, equals `ℚ̄(↑aⁿ − ↑a)`.
-/
theorem geomBase_bot_restrict (n : ℕ)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    (⊥ : IntermediateField GeomBase (morseGeomPoly n).SplittingField).restrictScalars
        (AlgebraicClosure ℚ)
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
          {(↑a : (morseGeomPoly n).SplittingField) ^ n - ↑a} := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨y, rfl⟩ := hz
    exact geomBase_image_mem_adjoin n a y
  · simp [IntermediateField.mem_bot]
    use algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (Polynomial.X)
    rw [← morse_aeval_gsub n a]
    simp [Polynomial.aeval_def]

/-
`ℚ̄(T)(↑a) = ℚ̄(↑a)`: the base-restriction of `adjoin GeomBase {↑a}` is `ℚ̄(↑a)`.
-/
theorem adjoin_geomBase_restrict (n : ℕ)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    (IntermediateField.adjoin GeomBase {(↑a : (morseGeomPoly n).SplittingField)}).restrictScalars
        (AlgebraicClosure ℚ)
      = IntermediateField.adjoin (AlgebraicClosure ℚ) {(↑a : (morseGeomPoly n).SplittingField)} := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have := geomBase_bot_restrict n a
    have h_adjoin : IntermediateField.adjoin (AlgebraicClosure ℚ)
          {(↑a : (morseGeomPoly n).SplittingField) ^ n - ↑a}
        ≤ IntermediateField.adjoin (AlgebraicClosure ℚ)
            {(↑a : (morseGeomPoly n).SplittingField)} :=
      IntermediateField.adjoin_simple_le_iff.mpr
        (sub_mem (pow_mem (IntermediateField.mem_adjoin_simple_self _ _) n)
          (IntermediateField.mem_adjoin_simple_self _ _))
    rw [← this] at *
    simp_all [IntermediateField.restrictScalars]
    rw [Subsemiring.mem_closure] at hx
    refine hx _ fun y hy ↦ ?_
    rcases hy with (rfl | ⟨y, rfl⟩)
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    · exact h_adjoin (Set.mem_range_self _)
  · simp

/- -/
theorem morseGeomPoly_no_intermediate (n : ℕ) (hn : 2 ≤ n)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField)
    (b : IntermediateField GeomBase (morseGeomPoly n).SplittingField)
    (hb : b < IntermediateField.adjoin GeomBase {(↑a : (morseGeomPoly n).SplittingField)}) :
    b = ⊥ := by
  by_contra h
  -- Let $M := \text{comap}(\Psi)(b.restrictScalars(\mathbb{Q}))$.
  set M := IntermediateField.comap (morseLift n a) (b.restrictScalars (AlgebraicClosure ℚ))
  -- By `IsCoatom`, we have `M = ⊤` or `M = adjoin (AlgebraicClosure ℚ) {w₀}`.
  have hM : M = ⊤ ∨ M = IntermediateField.adjoin (AlgebraicClosure ℚ)
      {(algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ))
        (X ^ n - X : (AlgebraicClosure ℚ)[X]))} := by
    have hCoatom : IsCoatom (IntermediateField.adjoin (AlgebraicClosure ℚ)
        {(algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ))
          (X ^ n - X : (AlgebraicClosure ℚ)[X]))}) := by
      apply RatFunc.isCoatom_adjoin_of_indecomposable
      · rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num <;> linarith
      · exact fun h g hh hg ↦ xnSubX_indecomposable n hn hh hg
    have hle : IntermediateField.adjoin (AlgebraicClosure ℚ)
          {(algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ))
            (X ^ n - X : (AlgebraicClosure ℚ)[X]))} ≤ M := by
      rw [IntermediateField.adjoin_simple_le_iff]
      have hmem : (morseLift n a) (algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ))
          (X ^ n - X : (AlgebraicClosure ℚ)[X])) ∈ b := by
        convert b.algebraMap_mem (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) using 1
        convert morse_aeval_gsub n a using 1
        exact morseLift_apply_poly n a _
      exact hmem
    cases eq_or_lt_of_le hle <;> simp_all [IsCoatom]
    grind
  cases' hM with hM hM
  · -- If `M = ⊤`, then `b.restrictScalars (AlgebraicClosure ℚ)` contains the image of `Ψ`,
    -- which is `adjoin (AlgebraicClosure ℚ) {a}`.
    have h_image : IntermediateField.adjoin (AlgebraicClosure ℚ)
          {(↑a : (morseGeomPoly n).SplittingField)}
        ≤ b.restrictScalars (AlgebraicClosure ℚ) := by
      have h_map_le : IntermediateField.map (morseLift n a) ⊤
          ≤ b.restrictScalars (AlgebraicClosure ℚ) := by
        rw [IntermediateField.map_le_iff_le_comap]
        simp_all only [le_refl, M]
      convert h_map_le using 1
      rw [← morseLift_fieldRange]
      ext
      simp [AlgHom.fieldRange_eq_map]
    apply hb.not_ge
    simpa [adjoin_geomBase_restrict] using h_image
  · -- By `IntermediateField.map_comap_eq`, we have `map Ψ M = b.restrictScalars (AlgebraicClosure ℚ)`.
    have h_map : IntermediateField.map (morseLift n a) M = b.restrictScalars (AlgebraicClosure ℚ) := by
      rw [IntermediateField.map_comap_eq]
      apply inf_eq_left.mpr
      rw [morseLift_fieldRange]
      refine le_trans (IntermediateField.restrictScalars_le_iff _ |>.2 hb.le) ?_
      simp [adjoin_geomBase_restrict]
    -- By `IntermediateField.adjoin_map`, we have `map Ψ M = adjoin (AlgebraicClosure ℚ) {Ψ w₀}`.
    have h_map_adjoin : IntermediateField.map (morseLift n a) M
        = IntermediateField.adjoin (AlgebraicClosure ℚ)
            {(↑a : (morseGeomPoly n).SplittingField) ^ n - ↑a} := by
      rw [hM, IntermediateField.adjoin_map]
      rw [Set.image_singleton]
      rw [morseLift_apply_poly]
      norm_num
    have h_contra : b.restrictScalars (AlgebraicClosure ℚ)
        = (⊥ : IntermediateField GeomBase (morseGeomPoly n).SplittingField).restrictScalars
            (AlgebraicClosure ℚ) := by
      rw [← h_map, h_map_adjoin, ← geomBase_bot_restrict n a]
    apply h
    simpa using congr_arg (fun x ↦ x) h_contra

theorem morseGeomPoly_adjoin_root_isAtom (n : ℕ) (hn : 2 ≤ n)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    IsAtom (IntermediateField.adjoin GeomBase
      {(↑a : (morseGeomPoly n).SplittingField)}) :=
  ⟨morseGeomPoly_adjoin_root_ne_bot n hn a, morseGeomPoly_no_intermediate n hn a⟩

theorem morseGeomPoly_stabilizer_isCoatom (n : ℕ) (hn : 2 ≤ n)
    (a : (morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :
    IsCoatom (@MulAction.stabilizer (morseGeomPoly n).Gal
      (↑((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField)) _
      (Gal.galAction (morseGeomPoly n) (morseGeomPoly n).SplittingField) a) := by
  have : IsGalois GeomBase (morseGeomPoly n).SplittingField :=
    IsGalois.of_separable_splitting_field (morseGeomPoly_separable n hn)
  rw [morseGeomPoly_stabilizer_eq_map_fixingSubgroup n hn a]
  -- `Gal.restrict` is a bijective group endomorphism, so `Subgroup.map` by it is an order
  -- isomorphism of the subgroup lattice, preserving `IsCoatom`.
  let Re : (morseGeomPoly n).Gal ≃* (morseGeomPoly n).Gal :=
    MulEquiv.ofBijective _ (morseGeomPoly_restrict_bijective n hn)
  have key : IsCoatom (Subgroup.map (Re : (morseGeomPoly n).Gal →* (morseGeomPoly n).Gal)
        (IntermediateField.fixingSubgroup
          (IntermediateField.adjoin GeomBase {(↑a : (morseGeomPoly n).SplittingField)})))
      ↔ IsAtom (IntermediateField.adjoin GeomBase
          {(↑a : (morseGeomPoly n).SplittingField)}) := by
    rw [← MulEquiv.mapSubgroup_apply, (Re.mapSubgroup).isCoatom_iff,
        isCoatom_fixingSubgroup_iff_isAtom]
  exact key.mpr (morseGeomPoly_adjoin_root_isAtom n hn a)

/-- **Primitivity of the geometric monodromy action** (the first conjunct of the deep input
`morseGeomPoly_monodromy_input`).  Every block of the `p.Gal`-action on the roots is trivial.

Proved from the maximality of a root stabiliser (`morseGeomPoly_stabilizer_isCoatom`) via
Mathlib's `MulAction.isCoatom_stabilizer_iff_preprimitive`: the action is pretransitive
(`Gal.galAction_isPretransitive` from `morseGeomPoly_irreducible`) on a nontrivial set
(`morseGeomPoly_card_rootSet`, `n ≥ 2`), so a maximal stabiliser makes the action preprimitive,
whence every block is trivial. -/
theorem morseGeomPoly_primitive (n : ℕ) (hn : 2 ≤ n) :
    ∀ B : Set ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField),
        MulAction.IsBlock (morseGeomPoly n).Gal B → MulAction.IsTrivialBlock B := by
  classical
  have htrans : MulAction.IsPretransitive (morseGeomPoly n).Gal
      ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) :=
    Gal.galAction_isPretransitive (morseGeomPoly n) (morseGeomPoly n).SplittingField
      (morseGeomPoly_irreducible n hn)
  have hnt : Nontrivial ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, morseGeomPoly_card_rootSet n hn]
    omega
  obtain ⟨a⟩ := (inferInstance : Nonempty
    ((morseGeomPoly n).rootSet (morseGeomPoly n).SplittingField))
  have hco := morseGeomPoly_stabilizer_isCoatom n hn a
  rw [MulAction.isCoatom_stabilizer_iff_preprimitive] at hco
  intro B hB
  exact hco.isTrivialBlock_of_isBlock hB

end
