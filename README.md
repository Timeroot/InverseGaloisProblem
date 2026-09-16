# The Inverse Galois Problem, in Lean 4

A formalization, in Lean 4 with Mathlib, of the Inverse Galois Problem: which finite groups occur
as Galois groups of extensions of `ℚ`.

Two predicates organize everything.

```lean
/-- Some finite Galois extension of `ℚ` has Galois group `G`. -/
def IsInverseGalois (G : Type*) [Group G] : Prop        -- InverseGalois/Core/Basic.lean

/-- Some finite Galois extension `L / ℚ(T)` has group `G`, with `ℚ`
    algebraically closed inside `L`. -/
def IsRegularInverseGalois (G : Type*) [Group G] : Prop -- InverseGalois/Rigidity/RET/Statement.lean
```

The regular statement is the stronger one: it implies the other by Hilbert irreducibility, it is
stable under base change, and it is what a geometric construction actually produces.

`InverseGalois/Catalogue.lean` is the index of everything realized, with the reasoning behind each
family. `docs/Development.md` records the non-obvious choices of approach.

## Headline results

**Shafarevich's theorem.** Every finite solvable group is a Galois group over `ℚ`.

```lean
theorem Shafarevich.isInverseGalois_of_isSolvable (G : Type) [Group G] [Finite G] [IsSolvable G] :
    IsInverseGalois G
```

It rests on `Shafarevich.splitPrimePowerEP` — every split embedding problem over `ℚ` whose kernel
has prime power order is solvable — which in turn rests on a class field theory layer built from
scratch in `InverseGalois/CFT/`: crossed products and the Brauer group, Tate cohomology and
Tate–Nakayama, the local invariant and the fundamental class, reciprocity over a number field,
Poitou–Tate duality, Grunwald–Wang, and Ikeda's theorem.

**The Riemann Existence Theorem, proved rather than assumed.**

```lean
theorem Rigidity.RET.geomRET {r : ℕ} (t : Fin r → k) (ht : Function.Injective t) : GeomRET t
```

Both directions of the branch-cycle correspondence over `ℚ̄` are theorems
(`InverseGalois/Rigidity/RET/Completeness.lean`), so the whole rigidity method here is
unconditional. The analytic half is a Hörmander `L²` solution of `∂̄` on the covering surface; the
descent from `ℂ` to `ℚ̄` is by specialization of a polynomial presentation. Seifert–van Kampen and
the fundamental group of the punctured plane were proved along the way, as was a Galois-category
treatment of the étale fundamental group.

**The rigidity method, with kernel-checked certificates.** A `Rigidity.RigidityCertificate` for a
finite group yields a regular realization over `ℚ(T)`; the weaker *orbit* rigidity yields one over
a number field. No certificate in the repository uses `native_decide`.

## What is realized

### Regularly over `ℚ(T)`

Closure properties: isomorphism, quotients, products of coprime order, and products of two groups
with no common nontrivial quotient (Goursat).

| Family | Theorem |
|---|---|
| every finite abelian group | `IsRegularInverseGalois.of_commGroup` |
| every finite **semiabelian** group (Dentzer–Stoll wreath construction) | `isRegularInverseGalois_of_isSemiabelian` |
| every finite group with cyclic Sylow subgroups; every group of squarefree order | `isRegularInverseGalois_of_isZGroup` |
| every finite group of nilpotency class `≤ 2` | `isRegularInverseGalois_of_nilpotencyClass_le_two` |
| every finite solvable group with abelian Sylow subgroups; every solvable group of cubefree order | `isRegularInverseGalois_of_forall_sylow_comm` |
| every finite group of order `< 48`, except orders `24` and `32` | `isRegularInverseGalois_of_card_lt_fortyeight` |
| the orders `p²q`, `p⁴`, `p²q²`, and unbounded families `m·q`, `m·q²` | `isRegularInverseGalois_of_card_eq_*` |
| Sylow `p`-subgroups of `S_{pⁿ}` | `isRegularInverseGalois_sylow_perm` |
| `Sₙ` for every `n` | `isRegularInverseGalois_perm_fin` |
| `Aₙ` for every `n` | `isRegularInverseGalois_alternatingGroup` |
| `Dₙ` for every `n ≠ 0` | `isRegularInverseGalois_dihedral` |
| every finite subgroup of `PGL₂(ℚ)` | `isRegularInverseGalois_of_isMobius` |
| `PGL₂(𝔽ₚ)` for `p = 7, 11, 13, 17, 19` | `Rigidity.PGL27.isRegularInverseGalois`, … |
| `GL₁(𝔽_q)` and `GL₂(𝔽₂)` | `Rigidity.isRegularInverseGalois_generalLinearGroup_*` |

### Regularly over a number field

By orbit rigidity (`Rigidity.RET.Descent.exists_regular_numberField_of_orbitRigid`): the Mathieu
groups `M₁₁`, `M₁₂`, `M₂₄`, and the simple groups `PSL₂(𝔽ₚ)` for every prime `7 ≤ p ≤ 37`. No
Mathieu group has a rationally rigid triple, and `M₂₂` and `M₂₃` have no rigid triple at all, so
rigidity provably stops there.

### Over `ℚ`

Every finite solvable group (`Shafarevich.isInverseGalois_of_isSolvable`), which subsumes the
earlier nilpotent results — `IsInverseGalois.of_isNilpotent`,
`isInverseGalois_of_isPGroup_odd` (Scholz–Reichardt) and `isInverseGalois_of_isPGroup_two` (the
dyadic induction) — and every regular realization above, by Hilbert irreducibility.

## Foundations

The default build has **no `sorry` and no added axioms**. The main theorems depend on
`propext`, `Classical.choice` and `Quot.sound` alone:

```
#print axioms Shafarevich.isInverseGalois_of_isSolvable
-- 'Shafarevich.isInverseGalois_of_isSolvable' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

`native_decide` is deliberately confined to the legacy quintic/`D₅` material in `Reflection/`,
`Groups/` and `Resolvent/`, and to parts of the vendored `Mathieu` library. It appears nowhere in
`Rigidity/`, `CFT/` or `Solvable/`.

Where a classical input was genuinely out of reach it was carried as a named `Prop`-valued
hypothesis, never as an axiom — which is how nine plausible-looking intermediate statements in the
Shafarevich development were discovered to be *false* rather than silently assumed. See
`docs/Development.md`.

## Layout

Each directory has a matching umbrella module (`InverseGalois/Rigidity.lean` for `Rigidity/`, and
so on); `InverseGalois.lean` is the public entry point and `InverseGalois/Catalogue.lean` the index
of results. About 1950 files and 433k lines.

* `InverseGalois/CFT/` — class field theory: Tate cohomology, local fields, Brauer groups, the
  class formation, reciprocity, Poitou–Tate duality, Kummer theory, Scholz–Reichardt.
* `InverseGalois/Rigidity/` — the Riemann Existence Theorem (`RET/`, including the topological and
  étale fundamental groups, the `∂̄` analysis and the `ℂ → ℚ̄` transfer), the rigidity criterion,
  the descent to `ℚ(T)` and to number fields, and the individual certificates (`Examples/`).
* `InverseGalois/Solvable/` — Ore's reduction, semiabelian group theory, and the Shafarevich
  endgame (`Solvable/Shafarevich/`).
* `InverseGalois/Hilbert/` — Hilbert irreducibility by the elementary Dörge–Bauer counting proof
  (`Hilbert/Analytic/`), and the symmetric and alternating families.
* `InverseGalois/Core/` — the basic predicate and the elementary cyclic and abelian realizations.
* `InverseGalois/Groups/`, `Resolvent/`, `Polynomial/`, `Reflection/` — the concrete small-group
  realizations, the quintic resolvent machinery and the `PolyReflect` normal-form evaluator.
* `InverseGalois/NumberTheory/` — auxiliary counting and prime-distribution estimates.
* `Mathieu/` — a vendored permutation-group library, kept out of `InverseGalois`'s import graph.
* `extras/comparator/` — a benchmark statement and its solution; deliberately not a default target.

## Building

```sh
lake exe cache get   # Mathlib oleans
lake build
```

The toolchain is pinned in `lean-toolchain` (Lean 4.28.0) and Mathlib in `lakefile.toml`. The
default targets are `InverseGalois` together with the vendored `Mathieu` library and the
certificate targets `MathieuRigidity`, `MathieuRigidityM22`, `MathieuRigidityM24`, `PGL2Large` and
`PSL2Large`, which exist only to raise the elaboration stack (`--tstack`). A full build is about
10000 jobs and takes hours on a many-core machine.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
