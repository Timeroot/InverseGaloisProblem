# Simple cases of the Inverse Galois Problem (over ℚ)

This project formalizes, in Lean 4 with Mathlib, progress on the Inverse Galois Problem: that
particular groups occur as Galois groups of extensions of `ℚ` — i.e. that they are *inverse Galois groups*.

The central definition is `IsInverseGalois G` (in `InverseGalois/Core/Basic.lean`): there exists a
finite Galois extension of `ℚ` whose Galois group is isomorphic to `G`.

## Results

* Show `IsInverseGalois` for all cyclic groups (`Cyclic.lean`)
* `IsInverseGalois` for a concrete finite groups, all transitive permutation groups up to 5.
  (`S₃`, `S₄`, `A₄`, `A₅`, `V₄`, `D₄`, `D₅`). Currently these are all done by "bespoke" computation.
  (`Groups/SmallGroups.lean`)
* If `G1` and `G2` are inverse Galois groups of coprime order, then their direct product is as well.
  (`Core/Product.lean`)
* Hilbert's theorem that every symmetric group `Sₙ` is an inverse Galois group, via
  Hilbert-irreducibility route.

## Next Goals

In no particular order:

* Extend the Hilbert-irreducibility results to show that all alternating groups are inverse Galois.
* If `G` is an inverse Galois group, then so are any quotients of `Q`.
* All Abelian groups are inverse Galois groups
* All _solvable_ groups are inverse Galois groups (a theorem [of Shafarevich](https://arxiv.org/pdf/math/9809211)).
* Formalize the _rigidity_ method, which is used for many sporadic simple groups.
* Apply the rigidity method to show IGP for all sporadic simple groups it is known for
* Formalize a more refined problem, the _Regular Inverse Galois Problem_; many of the constructions are regular,
  and these are closed under e.g. direct products.
* Develop the computational machinery to do efficient computational checks of a given polynomial,
  a-la how MAGMA or Maple does it, but with a certified Lean proof. Probably wants a computational
  algebra library.

## Layout

The project follows a directory-oriented module hierarchy. Each directory has a matching
umbrella module (for example, `InverseGalois/Groups.lean`).

* `InverseGalois/Core/` — `IsInverseGalois`, cyclic groups, and product constructions.
* `InverseGalois/Polynomial/` — general Galois-action, discriminant, Dedekind, and Frobenius
  infrastructure.
* `InverseGalois/Resolvent/` — quintic resolvents, pentagonal sums, certificate identities,
  and general resolvent families.
* `InverseGalois/Groups/` — concrete realizations of `S₃`, `S₄`, `A₄`, `A₅`, `D₄`, and `D₅`.
  The complete `D₅` result is in `Groups/D5.lean`; its witness-polynomial calculations and
  finite-group lemmas are in `Groups/D5Polynomial.lean` and `Groups/D5GroupFacts.lean`.
* `InverseGalois/Hilbert/` — symmetric groups and Hilbert irreducibility. The more extensive
  continuation, Puiseux, and Dörge–Bauer development is isolated in `Hilbert/Analytic/`.
* `InverseGalois/Reflection/` — the verified polynomial normal-form evaluator and its demo.
* `InverseGalois/NumberTheory/` — auxiliary counting and prime-distribution estimates.
* `InverseGalois/Experimental/` — preserved exploratory modules that are not part of the
  supported import graph.

`InverseGalois.lean` is the public entry point. The directory umbrella modules make it possible
to import one coherent layer without listing its implementation files individually.

## Cyclic groups

`InverseGalois/Core/Cyclic.lean` proves `IsInverseGalois.of_isCyclic`: every finite cyclic group
occurs as a Galois group over `ℚ`. For a cyclic group of order `n`, Dirichlet's theorem supplies
a prime `p ≡ 1 (mod n)`. The cyclotomic extension `ℚ(ζₚ)/ℚ` has Galois group
`(ZMod p)ˣ`, a cyclic group of order `p - 1`; reduction modulo `n` gives a surjection onto the
cyclic group of order `n`. Closure of `IsInverseGalois` under quotients then gives the result.

## D₅ and the sextic resolvent

The D₅ case (`X⁵ − 5X + 12`) is handled through the sextic resolvent `R₆` of a general
trinomial quintic `X⁵ + pX + q`.  The six roots of `R₆` are the squares `Ψ(v∘σ)²` of the
pentagonal sums of the quintic's roots `v`, indexed by the six left cosets of `F₂₀` in `S₅`.

A recurring difficulty is that the underlying coefficient identities (`psSq_esymm*` in the
`PSIdent*` files) are high-degree polynomial identities whose direct `ring`/`decide`
normalization is extremely expensive.  They are proved with precomputed Gröbner cofactor
certificates that are now discharged by a **direct normal-form computation** (`PolyReflect` +
`native_decide`) instead of `ring`; see "Performance of the resolvent identities" below.
This brought the degree-20 `e₅` identity down from ~an hour to ~2 minutes and made the whole
resolvent chain (including `Groups/D5.lean`) compile end-to-end in the default build.

### How the `D₅` proof is assembled

The end-to-end argument for `IsInverseGalois (DihedralGroup 5)` (`X⁵ − 5X + 12`) lives in
`Groups/D5.lean`, which now compiles in the default build (the resolvent identities are no
longer a bottleneck).  Its ingredients:

* `Groups/D5GroupFacts.lean` — `perm_fin5_no_order_ten` (no element of order 10 in `S₅`) and
  `iso_dihedral_five_of_card_ten` (a non-cyclic group of order 10 is `≅ D₅`).
* `Groups/D5Polynomial.lean` — `f_d5_nonreal_root` (`X⁵ − 5X + 12` has a non-real complex root, via
  `Polynomial.card_rootSet_le_derivative`), giving `2 ∣ |Gal|`.
* `Groups/D5.lean` — combines these with the resolvent pipeline
  (`card_gal_dvd_20_of_resolvent_root` using the rational root `25` of `R₆`, the
  discriminant-square embedding `Gal ↪ A₅`, and `A5_no_subgroup_order_20`) to pin
  `|Gal| = 10` and conclude `Gal ≅ D₅`.  The two glue lemmas `card_gal_d5` and
  `gal_iso_d5`, and the `IsInverseGalois.dihedral_five` assembly, are written out in full
  (no `sorry`).  With the reflection-based resolvent identities this file now **compiles
  end-to-end**: `IsInverseGalois.dihedral_five : IsInverseGalois (DihedralGroup 5)`
  is sorry-free and uses only the standard axioms (plus `native_decide`'s
  `Lean.ofReduceBool`/`Lean.trustCompiler`).

For the *separability* of `R₆` (distinctness of its six roots), `Resolvent/PentagonalSum.lean` uses a
small explicit **Bézout certificate**

```
A·R₆ + B·R₆′ = 5⁶ · q⁴ · (256 p⁵ + 3125 q⁴)
```

with low-degree cofactors `A, B`.  The right-hand side is a nonzero constant for an
irreducible quintic (`q ≠ 0` and the discriminant `256 p⁵ + 3125 q⁴ ≠ 0`), so `R₆` is coprime
to its derivative, hence separable; separability ⇒ squarefree then gives that the six roots are
pairwise distinct.  This replaces the heavy discriminant computation with a fast `ring` check.

## Performance of the resolvent identities (`PolyReflect`)

The single biggest pain point in the D₅ development used to be the family of high-degree
polynomial identities `psSq_esymm*` / `ps_prod`: dense degree-12/16/20 equations in four
variables.  Proving one with `ring`/`linear_combination` took anywhere from ~150 s (degree
12) to roughly **an hour** (degree 20).  They are now proved by a **direct normal-form
computation** built on the `PolyReflect` engine, and each compiles in seconds to a couple of
minutes.

### The `PolyReflect` engine (`InverseGalois/Reflection/PolyReflect.lean`)

This is a small, self-contained, **sorry-free** reflection library:

* `RE` reflects a ring expression (`atom`, `lit`, `add`, `sub`, `mul`, `neg`, `pow`);
  `RE.eval` evaluates it in any `CommRing`.
* `toNF : RE → NF` computes a **computable** multivariate-polynomial normal form (a sorted
  association list of monomials), and `eval_toNF` proves `e.eval ρ = evalNF ρ (toNF e)`.
* `eval_eq_of_toNF` reduces an identity `e₁.eval ρ = e₂.eval ρ` to the *decidable* check
  `toNF e₁ = toNF e₂`, which `native_decide` runs as compiled code.

### How the heavy identities are proved (the cofactor-certificate pattern)

The naïve route — reflect both sides and bridge `RE.eval` back to the surface — is defeated
by the **surface term**: a degree-20 identity's right-hand side is a 15–70 kB explicit
polynomial, and even *elaborating* or defeq-checking such a literal is prohibitively slow,
regardless of how the equality is proved.

The working pattern (see `Resolvent/PentagonalSumCertificates.lean`) sidesteps the giant literal entirely.  After
eliminating `v₄` via `e₁`, each identity is an ideal-membership statement modulo `(e₂, e₃)`,
so there are Gröbner cofactors `c₂, c₃` with `LHS − RHS − c₂·e₂ − c₃·e₃ = 0` as a *pure*
polynomial identity.  We then:

1. reflect `LHS`, `RHS`, `e₂`, `e₃`, `c₂`, `c₃` into named `RE` constants and check
   `toNF (LHS − RHS − c₂·e₂ − c₃·e₃) = []` by `native_decide` (the only heavy step, a
   compiled normal-form computation taking seconds–minutes);
2. peel only the *outer* structure of the reflected expression with `rfl`, keeping the
   dense cofactors as **opaque** `reC2.eval ρ` / `reC3.eval ρ` terms — they are never
   expanded into a surface literal;
3. show `e₂.eval ρ = 0` and `e₃.eval ρ = 0` (a tiny `linear_combination` from the
   hypotheses) and use `mul_zero` to delete the cofactor terms, leaving
   `LHS.eval ρ − RHS.eval ρ = 0`;
4. bridge only the small `LHS`/`RHS` (product forms, no giant literal) back to the goal.

Because the only large objects are the cofactor `RE` *data* (which `native_decide` compiles)
and never appear as a surface polynomial, the hour-long `ring` cost is gone.  The deeply
cofactors are stored as compact strings and parsed into normal forms, avoiding deeply nested surface terms.

### Three further optimisations (current state)

The certificate pattern above was subsequently sped up by ~3-6× more, so that every identity
file now compiles essentially at the `import Mathlib` floor (well under a minute each):

1. **Linear-merge `nfAdd`.**  Normal-form addition was an `O(|f|·|g|)` repeated insertion
   (`nfInsert` folded over `f`); it is now an `O(|f|+|g|)` linear merge of the two sorted
   association lists.  This is what dominated the `native_decide` step, and the merge is what
   took the degree-20 normal-form computation from ~70 s to ~2 s.  Crucially the soundness
   lemma `evalNF_nfAdd` is *unconditional* (the merge emits one head term per step and only
   combines syntactically equal monomials), so no sortedness invariant has to be threaded
   through the proof — sortedness is only needed at *runtime* for the result to be canonical,
   which `native_decide` checks computationally.
2. **Length-aware `nfMul`.**  Multiplication now folds over the *longer* operand and multiplies
   each of its monomials into the *shorter* one, so the per-monomial cost (quadratic in the
   length of its argument) is always paid on the shorter list.
3. **String-literal cofactors (`parseNF`).**  After (1)-(2), the remaining cost was *elaborating*
   the 100+ kB `RE` constructor trees of the dense Gröbner cofactors.  Since the cofactors are
   opaque (killed by `mul_zero`), they are now stored as a single compact **string literal**
   (which the elaborator handles in one step) and decoded to a normal form at `native_decide`
   time by `PolyReflect.parseNF`.  No lemma about the parser is needed: if the string decoded
   the wrong polynomial the certificate would simply fail to reduce to `[]`.  This removed the
   ~35 s of literal elaboration that dominated the degree-20 file.

Measured results on this toolchain (each file, end to end, including `import Mathlib` ~15 s):
`psSq_esymm5` (degree 20) ~110 s → **~18 s**, `psSq_esymm4` (degree 16) ~48 s → **~16 s**,
`psSq_esymm3` (degree 12) ~19 s → **~15 s**, `ps_prod` (degree 12) **~11 s**, and
`Resolvent/PentagonalSumIdentities.lean` (the degree-8 `psSq_esymm2`, converted from a heavy
`linear_combination`) ~57 s → **~12 s**.  Relative to the original `ring`/`linear_combination`
proofs this is roughly an hour → ~18 s for the degree-20 identity.  All are sorry-free and use
only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`, plus
`Lean.ofReduceBool`/`Lean.trustCompiler` from `native_decide`).

The generated reflection data and compact cofactor strings are retained directly in
`Resolvent/PentagonalSumCertificates.lean`; obsolete one-off generators and intermediate certificate
dumps have been removed. `Reflection/PolyReflectDemo.lean` exercises the engine on small examples.

## Notes

* Additional design and historical notes are collected under `docs/Development/`.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
