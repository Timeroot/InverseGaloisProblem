# Hilbert's Irreducibility Theorem — Formalization Plan

## Goal

Prove **Hilbert's Irreducibility Theorem** (HIT): if `f(T, X) ∈ ℚ[T, X]` is irreducible
with `deg_X f ≥ 1`, then `f(t₀, X) ∈ ℚ[X]` is irreducible for infinitely many `t₀ ∈ ℤ`.
HIT is one of the two routes in this project towards showing that every symmetric group
`Sₙ` is an inverse Galois group over `ℚ` (the other being the Dedekind/specialization
route in `Polynomial/DedekindFacts.lean` / `Hilbert/GaloisAction.lean`).

## Route: the elementary Dörge–Bauer proof (1927)

This project follows the classical **elementary** proof of HIT. It uses only tools
available around 1900 and, in particular, uses **no** reduction modulo `p` and no deep
analytic number theory.

Top-level assembly (all sorry-free bodies):

```
Hilbert/HilbertIrreducibility.lean
  theorem hilbert_irreducibility_theorem   -- main HIT statement
  theorem hilbert_irreducibility_monic     -- monic case
        |
   Hilbert/Analytic/DorgeBauerPuiseux.lean
     lemma dorge_density_estimate          -- ℚ-reducible locus is sublinear
        |
     lemma int_factor_locus_sublinear      -- assembled counting core
        |
   Hilbert/Analytic/DorgeBauerAnalytic.lean / Hilbert/Analytic/DorgeBauerBranches.lean
     finite Puiseux computations / real root branches
        |
   Hilbert/Analytic/DorgeBauer.lean
     algebraic bounds and elementary counting infrastructure
        |
   Hilbert/Analytic/IntegralModelExists.lean
     lemma integral_model_exists           -- Tschirnhaus scaling to ℤ[T][X]
```

`hilbert_irreducibility_theorem` reduces (via `dorge_density_estimate` and the elementary
integral model `integral_model_exists`) to the elementary counting core
`int_factor_locus_sublinear`.

## Proof sketch of the counting core (`int_factor_locus_sublinear`)

For `F ∈ ℤ[T][X]` monic in `X`, irreducible over `ℚ(T)`, of degree `d ≥ 2`, and
`1 ≤ k < d`, the number of integers `t ∈ [-N, N]` for which `F(t, X)` has a monic
degree-`k` factor in `ℤ[X]` is `O(N^α)` with `α < 1`.

1. **Root bound** (`cauchy_root_bound`, `cauchy_root_bound_max`): every complex root of
   `F(t, X)` has absolute value `≤ 1 + d·max_i |a_i(t)| = O(N^M)` for `|t| ≤ N`.
2. **Coefficient bound** (`factor_coeff_bound`): coefficients of a monic degree-`k`
   factor are elementary symmetric functions of `k` roots, hence `O(N^{Mk})`.
3. **Resolvent / trace**: a monic degree-`k` factor has an integer "trace" (sum of its
   roots), a root of an integer resolvent whose roots are the `k`-subset sums of the roots
   of `F`. Because `F` is irreducible over `ℚ(T)` with `0 < k < d`, the Galois group is
   transitive on the roots, so no `k`-subset is Galois-stable and (for a suitably generic
   resolvent) every irreducible factor has `Y`-degree `≥ 2`.
4. **Sparsity of integer points on a curve** (the one substantial *elementary* input):
   for `P(T, Y) ∈ ℤ[T][Y]` monic in `Y`, of `Y`-degree `≥ 2`, with no root in `ℚ(T)`, the
   set of integers `t` for which `P(t, Y)` has a rational root is sublinear in `[-N, N]`
   — an algebraic function that is not a rational function takes rational values on a
   density-zero set of integers.

The supporting bounds (steps 1–2) are proved in `Hilbert/Analytic/DorgeBauer.lean`; real branch construction is
separated into `Hilbert/Analytic/DorgeBauerBranches.lean`, while finite Puiseux and local complex-analytic tools
are in `Hilbert/Analytic/DorgeBauerAnalytic.lean`. Step 4 is the classical
elementary analytic heart of the theorem (Dörge 1927; Serre, *Topics in Galois Theory*,
Ch. 3).

## Dependencies on Mathlib

- `Polynomial.IsPrimitive` / Gauss's lemma infrastructure.
- Elementary symmetric functions (`Polynomial.coeff` of products, `Multiset.esymm`).
- `MvPolynomial.esymmAlgHom_surjective` (fundamental theorem of symmetric polynomials)
  for the generic-polynomial argument towards `Sₙ`.
