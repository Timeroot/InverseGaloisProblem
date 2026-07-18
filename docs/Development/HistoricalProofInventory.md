# Historical Proof Inventory

> Historical note: this document records an earlier stage of the development and is not a
> current inventory. The Lean sources now contain no `sorry` or `admit`.

## Overview

The project has **4 `sorry` statements** across 2 files, in two independent chains.
(In Chain 3, both `int_factor_locus_sublinear` and `int_root_locus_sublinear` are now
sorry-free; the chain is reduced to two isolated inputs, `resolvent_exists` and
`int_root_locus_large_sublinear` — Sorry 4a/4b below.)

Chain 1 (D₅) is now **fully sorry-free**: `Groups/D5.lean` directly defines the unique
headline theorem `IsInverseGalois.dihedral_five`, and `D5.lean` is only a compatibility import.
The whole resolvent pipeline
(`Groups/D5Polynomial`, `Groups/D5GroupFacts`, `PentagonalSum*`,
`Resolvent/PolynomialGaloisTheory`) is now built as part of the default target and is sorry-free.

---

## Chain 1: D₅ (Dihedral Group of Order 10)

**Files:** `Groups/D5.lean` → `D5.lean` → `Groups/SmallGroups.lean` → `InverseGalois.lean` (main)

### Former Sorry 1: `IsInverseGalois.dihedral_five` — RESOLVED
```lean
theorem IsInverseGalois.dihedral_five : IsInverseGalois (DihedralGroup 5)
```
**What it says:** `D₅` is an inverse Galois group (witnessed by `X⁵ − 5X + 12`).

**Status:** ✅ **Proved (sorry-free).** The theorem is proved directly in `Groups/D5.lean`;
there is no duplicate wiring declaration. `#print axioms` on the result
reports only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`,
`Lean.ofReduceBool`, `Lean.trustCompiler`). The whole resolvent pipeline is now part of the
default build target.

---

## Chain 2: Hilbert's Theorem via Dedekind (Sₙ for all n)

**File:** `Polynomial/DedekindFacts.lean` → `Hilbert/GaloisAction.lean` → `Hilbert/Symmetric.lean` → `Groups/SmallGroups.lean`

The `hilbert_symmetric` assembly is sorry-free but rests on these two number-theoretic
inputs about `Xⁿ − X − 1`.

### Sorry 2: `xnSubXSubOne_has_swap_prime` (`Polynomial/DedekindFacts.lean:213`)
```lean
theorem xnSubXSubOne_has_swap_prime (n : ℕ) (hn : 3 ≤ n) :
    ∃ (p : ℕ), ∃ (_ : Fact (Nat.Prime p)),
      Squarefree ((xnSubXSubOneZ n).map (Int.castRingHom (ZMod p))) ∧
      factorizationType (...) = {2}
```
**What it says:** For every `n ≥ 3` there is a prime `p` with `Xⁿ − X − 1 mod p` of
factorization type `{2}` (one quadratic factor, the rest linear).

**Difficulty:** ★★★★★ (universal `∀ n` statement in analytic/algebraic number theory).

### Sorry 3: `xnSubXSubOne_has_cycle_prime` (`Polynomial/DedekindFacts.lean:222`)
```lean
theorem xnSubXSubOne_has_cycle_prime (n : ℕ) (hn : 3 ≤ n) :
    ∃ (p : ℕ), ∃ (_ : Fact (Nat.Prime p)),
      Squarefree ((xnSubXSubOneZ n).map (Int.castRingHom (ZMod p))) ∧
      factorizationType (...) = {n - 1}
```
**What it says:** For every `n ≥ 3` there is a prime `p` with `Xⁿ − X − 1 mod p` of
factorization type `{n − 1}` (one linear factor, one irreducible of degree `n − 1`).

**Difficulty:** ★★★★★ (same as Sorry 2).

---

## Chain 3: Hilbert's Irreducibility Theorem (elementary Dörge–Bauer route)

**Files:** `Hilbert/Analytic/IntegralModelExists.lean` → `Hilbert/Analytic/DorgeBauer.lean` → `Hilbert/HilbertIrreducibility.lean`

This route is not imported by the main project target. `Hilbert/HilbertIrreducibility.lean` and
`DorgeBauer.dorge_density_estimate` are sorry-free; they reduce to the single counting
core below. The route uses **only** elementary (≈1900) tools: **no** reduction mod `p`
and no deep analytic number theory.

### `int_factor_locus_sublinear` (`Hilbert/Analytic/DorgeBauer.lean`) — now PROVED from two isolated inputs
```lean
lemma int_factor_locus_sublinear (F : Polynomial (Polynomial ℤ))
    (hF_monic : F.Monic) (hF_irr : Irreducible F) (hF_abs_irr : ...)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < F.natDegree) :
    ∃ C α, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N, 0 < N →
      (Set.ncard ({t | F(t,X) has a monic degree-k ℤ-factor} ∩ Icc (-N) N) : ℝ)
        ≤ C * N ^ α
```
**What it says:** the integer reducible locus of `F` grows sublinearly in `[-N, N]`.

**Status:** the body of `int_factor_locus_sublinear` is now **sorry-free**. Following the
elementary outline (Steps 1–4 in the lemma docstring), it is reduced to exactly two
self-contained inputs, which are the only remaining `sorry`s in this chain:

### Sorry 4a: `resolvent_exists` (`Hilbert/Analytic/DorgeBauer.lean`)
Steps 1–3 of the outline (the `k`-subset resolvent). Produces `P ∈ ℤ[T][Y]` monic in
`Y` of `Y`-degree `≥ 2`, with no root in `ℚ(T)`, such that whenever `F(t,X)` has a monic
degree-`k` factor, `P(t,Y)` has *some* integer root.
**Difficulty:** ★★★★ (symmetric-function construction + integral descent + a
permutation-representation fixed-space argument; not currently packaged in Mathlib).

**Correction (important).** The docstring in `Hilbert/Analytic/DorgeBauer.lean` previously claimed the
resolvent could be taken to be the **subset-sum / trace** resolvent, with the specific
root `y = -g.coeff (k-1)` (the sum of the roots of the factor `g`). This is **false**:
for `F = X⁴ - T` and `k = 2` the trace of every monic degree-2 factor of `X⁴ - t` lies on
a branch forcing the value `0` for infinitely many `t` (e.g. `X⁴ - a² = (X²-a)(X²+a)` has
factors of trace `0`), so any resolvent required to have those traces as roots would have
the rational-function root `0 ∈ ℚ(T)`, contradicting "no root in `ℚ(T)`". The *formal
statement* of `resolvent_exists` only asks for **some** integer root of `P(t,Y)` (not the
trace), and is **true** — but only via the corrected construction: a resolvent
`∏_S (Y - w_S)` where `w_S = ∑_{j=1}^k λ_j e_j(S)` is a *generic* integer linear
combination of the elementary symmetric functions of each `k`-subset `S`. Irreducibility of
`F` over `ℚ(T)` (no degree-`k` factor there) makes each tuple `(e_j(S))_j` non-Galois-fixed,
so a `λ` avoiding a finite union of proper `ℚ`-subspaces yields a resolvent with no root in
`ℚ(T)`, while each `w_S` remains a symmetric function of a factor's roots, hence an integer.
The `Hilbert/Analytic/DorgeBauer.lean` docstring has been updated to describe this correct construction.

### Sorry 4b: `int_root_locus_large_sublinear` (`Hilbert/Analytic/DorgeBauer.lean`)
Step 4 of the outline (the elementary analytic core). `int_root_locus_sublinear` itself is
now **proved** by splitting the integer roots `y` of `P(t, Y)` by size:

* the *small* roots (`y² ≤ N`, i.e. `|y| ≤ √N`) are handled by the fully-proved,
  elementary `int_root_locus_small_sublinear` (`O(N^{1/2})`): for each fixed `y` the value
  polynomial `P(T, y) ∈ ℤ[T]` is nonzero (`eval_C_ne_zero_of_no_root`) so it has at most
  `deg_T P` roots `t`, and there are only `O(√N)` admissible `y`;
* the *large* roots (`y² > N`) are the sole remaining gap, isolated as
  `int_root_locus_large_sublinear`: for `P ∈ ℤ[T][Y]` monic in `Y` of `Y`-degree `≥ 2`
  with no root in `ℚ(T)`, the set of `t ∈ [-N,N]` for which `P(t,Y)` has an integer root
  `y` with `|y| > √N` is `O(N^α)` with `α < 1` — an algebraic function that is not
  rational takes (large) integer values on a density-zero set of integers (Dörge 1927;
  Serre, *Topics in Galois Theory*, Ch. 3).

**Difficulty:** ★★★★★ (the substantial analytic heart of HIT; a Bombieri–Pila /
integer-points-on-curves sparsity bound, absent from Mathlib).

**Supporting code (already proved in `Hilbert/Analytic/DorgeBauer.lean`):** the reduction of
`int_factor_locus_sublinear` to `resolvent_exists` + `int_root_locus_sublinear`; the
size-split reduction of `int_root_locus_sublinear` to
`int_root_locus_small_sublinear` (proved) + `int_root_locus_large_sublinear`; the helpers
`eval_map_evalRingHom_eq`, `eval_C_ne_zero_of_no_root`; `cauchy_root_bound`,
`cauchy_root_bound_max`, `factor_coeff_bound`, `finite_specializations_for_fixed_factor`,
`boundedMonicPolys` / `finite_boundedMonicPolys`, `infinite_complement_of_sublinear_ncard`.

---

## Priority Ranking

1. `IsInverseGalois.dihedral_five` — only a wiring step; the underlying proof exists.
2. `xnSubXSubOne_has_swap_prime`, `xnSubXSubOne_has_cycle_prime` — would complete the
   Dedekind route to all `Sₙ`.
3. `int_factor_locus_sublinear` — the elementary counting heart of the HIT route.
