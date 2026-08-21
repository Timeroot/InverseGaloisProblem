# Hilbert irreducibility without absolute irreducibility

*Read-only assessment, 2026-08-21. Paths are relative to the repository root;
`$M` = `.lake/packages/mathlib` (pinned `v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
No Lean was written or built for this document.*

---

## 0. Headline

**The `hf_abs_irr` hypothesis of `hilbert_irreducibility_theorem` is a pure artifact.**
It is threaded through five lemmas and then *discarded*: the terminal consumer,
`resolvent_exists`, binds it as `_hF_abs_irr` — an underscore-prefixed, provably unused
binder (`InverseGalois/Hilbert/Analytic/DorgeBauerPuiseux.lean:1151`). Lean has already
type-checked the counting core without it. Removing the hypothesis is a mechanical binder
deletion across six files, not a mathematical project.

Consequently **Route A is the recommendation, at effort S (days, dominated by one full
`lake build`)**, and it delivers exactly the theorem the Ikeda / wreath-product programme
needs: `ℚ` is Hilbertian, full stop.

Routes B and C remain relevant for a *different* consumer — the
`exists_regular_numberField` family in `InverseGalois/Rigidity/RET/Descent/` — and are
assessed below, but they are not on the critical path for the stated target.

---

## 1. Where `hf_abs_irr` is actually used

### 1.1 The full call chain

```
hilbert_irreducibility_theorem                InverseGalois/Hilbert/HilbertIrreducibility.lean:423
  ├─ hilbert_irreducibility_monic             InverseGalois/Hilbert/HilbertIrreducibility.lean:255   (uses hf_abs_irr at :326)
  │    └─ dorge_density_estimate              InverseGalois/Hilbert/Analytic/DorgeBauerPuiseux.lean:1306
  │         ├─ integral_model_exists          InverseGalois/Hilbert/Analytic/IntegralModelExists.lean:51   (call at DorgeBauerPuiseux.lean:1318)
  │         │    └─ integral_model_absIrr     InverseGalois/Hilbert/Analytic/IntegralModelExists.lean:30   (call at IntegralModelExists.lean:134)
  │         └─ int_factor_locus_sublinear     InverseGalois/Hilbert/Analytic/DorgeBauerPuiseux.lean:1273   (call at :1322)
  │              └─ resolvent_exists          InverseGalois/Hilbert/Analytic/DorgeBauerPuiseux.lean:1148   (call at :1285)
  │                   └─ ***  binder is `_hF_abs_irr` at :1151 — NEVER USED  ***
  └─ monicAssociate_absIrr                    InverseGalois/Hilbert/HilbertIrreducibility.lean:188   (call at :459)
```

A second, parallel consumer with the same terminus:

```
reducibleLocus_not_univ                       InverseGalois/Hilbert/HilbertIrreducibility.lean:477   (uses hf_abs_irr at :484 → dorge_density_estimate)
```

An exhaustive `grep` for `abs_irr|absIrr` across `InverseGalois/Hilbert/` and
`InverseGalois/Resolvent/` confirms there are no other consumers on the HIT side. (The
`anResolvent_abs_irreducible*` / `fullResolvent_abs_irreducible` hits in
`AlternatingFamily*.lean` and `ResolventFamily.lean` are *producers*: they exist only to
manufacture the `hGabs` argument that callers hand to `hilbert_irreducibility_theorem`.)

### 1.2 What the counting core really needs

The quantitative heart is:

```lean
-- InverseGalois/Hilbert/Analytic/DorgeBauerPuiseux.lean:922
lemma int_root_locus_sublinear
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (C : ℝ) (α : ℝ), 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard ({t : ℤ | ∃ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
        Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ C * (N : ℝ) ^ α
```

Three hypotheses only: monic, `Y`-degree `≥ 2`, **no root in `ℚ(T)`**. The same three
propagate to its two halves, `int_root_locus_small_sublinear`
(`InverseGalois/Hilbert/Analytic/DorgeBauer.lean:588`) and
`int_root_locus_large_sublinear` (`.../DorgeBauerPuiseux.lean:894`). Absolute
irreducibility appears in neither.

So the only question is: what does it take to build a resolvent `P` with **no root in
`ℚ(T)`**? Answer, from the body of `resolvent_exists`
(`.../DorgeBauerPuiseux.lean:1148–1272`):

```lean
have hFK_irr : Irreducible f := FmapToRatFunc_irreducible F hF_monic hF_irr   -- :1170
obtain ⟨lam, hlam⟩ := exists_generic_lam f hFK_irr hf_monic hcardL k hk (hf_deg ▸ hk')  -- :1183
```

and the genericity lemma itself:

```lean
-- InverseGalois/Resolvent/ResolventConstruction.lean:393
lemma exists_generic_lam {K L : Type} [Field K] [Field L] [Algebra K L] [CharZero L]
    (f : Polynomial K) (hf_irr : Irreducible f) (hf_monic : f.Monic)
    (hsplit : (f.map (algebraMap K L)).roots.card = f.natDegree)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < f.natDegree) :
    ∃ lam : Fin k → ℤ, ∀ s ∈ (f.map (algebraMap K L)).roots.powersetCard k,
      wval k lam s ∉ Set.range (algebraMap K L)
```

resting on

```lean
-- InverseGalois/Resolvent/ResolventConstruction.lean:325
lemma exists_esymm_notMem ... (f : Polynomial K) (hf_irr : Irreducible f) (hf_monic : f.Monic)
    (hsplit : ...) (k : ℕ) (hk : 1 ≤ k) (hk' : k < f.natDegree)
    (s : Multiset L) (hs : s ∈ (f.map (algebraMap K L)).roots.powersetCard k) :
    ∃ j : Fin k, s.esymm (↑j + 1) ∉ Set.range (algebraMap K L)
```

**Mathematically**: if some `k`-subset `S` of the roots had *all* its elementary
symmetric functions in `K = ℚ(T)`, then `∏_{β ∈ S}(X - β)` would be a degree-`k` factor of
`f` in `K[X]` with `0 < k < deg f`, contradicting irreducibility **over `ℚ(T)`**. That is
the *arithmetic* monodromy group being transitive on the roots — which is exactly
`Irreducible f` over `ℚ(T)`, i.e. `Irreducible F` in `ℤ[T][X]` plus Gauss
(`FmapToRatFunc_irreducible`, `.../DorgeBauerPuiseux.lean:986`). Absolute irreducibility
is transitivity of the **geometric** monodromy group, a strictly stronger and strictly
unnecessary condition here.

This is also exactly what the project's own plan document says. From
`docs/Development/HilbertPlan.md`:

> **Goal.** Prove Hilbert's Irreducibility Theorem (HIT): if `f(T, X) ∈ ℚ[T, X]` is
> irreducible with `deg_X f ≥ 1`, then `f(t₀, X) ∈ ℚ[X]` is irreducible for infinitely
> many `t₀ ∈ ℤ`.

> 3. **Resolvent / trace**: … Because `F` is irreducible **over `ℚ(T)`** with `0 < k < d`,
>    the Galois group is transitive on the roots, so no `k`-subset is Galois-stable …

The plan never asked for absolute irreducibility. The hypothesis is legacy from the
`Sₙ`/`Aₙ` callers, which happen to have it lying around for free.

### 1.3 Sanity check that the general statement is true

`X² + 1 ∈ ℚ[T][X]` is irreducible but not absolutely irreducible (`= (X-i)(X+i)` over
`ℚ̄`), and every specialization is irreducible over `ℚ` — no contradiction. `X² + T²`
factors over `ℚ̄(T)` as `(X - iT)(X + iT)`, has no root in `ℚ(T)`, and `X² + t²` is
irreducible for every `t ≠ 0`. In the analytic core the geometrically-reducible branches
`y = ±iT` are simply *not real*, and the branch machinery
(`real_algebraic_branches`, `.../DorgeBauerPuiseux.lean:372`) only ever looks at real
branches, because integer roots are real. A real branch that is a polynomial in `T` and
integer-valued on infinitely many integers has rational coefficients by Lagrange
interpolation, hence gives a root of `P` in `ℚ(T)` — excluded by `hP_no_root`. The
argument is airtight without any geometric hypothesis.

---

## 2. Verdict: artifact, not essential

**Verdict: pure artifact.** It is not merely "probably removable" — Lean has *already
verified* that the counting core does not consume it. The evidence is the underscore
binder at `InverseGalois/Hilbert/Analytic/DorgeBauerPuiseux.lean:1151`, in a file that is
part of the green default build with zero `sorry`s (`grep -rn "sorry\|axiom "
InverseGalois/Hilbert/` returns nothing).

Precisely which lemmas must change, and how:

| # | Declaration | file:line | Change |
|---|---|---|---|
| 1 | `resolvent_exists` | `Hilbert/Analytic/DorgeBauerPuiseux.lean:1148` | delete the `_hF_abs_irr` binder (:1151–1152) |
| 2 | `int_factor_locus_sublinear` | `Hilbert/Analytic/DorgeBauerPuiseux.lean:1273` | delete the `hF_abs_irr` binder (:1276–1277); drop the argument at :1285 |
| 3 | `integral_model_exists` | `Hilbert/Analytic/IntegralModelExists.lean:51` | delete the `hf_abs_irr` binder (:54–55) **and** the `Irreducible (F.map …)` conjunct from the ∃-body (:59); delete `hF_abs_irr_out` (:132–134) and shrink the anonymous constructor at :135 |
| 4 | `dorge_density_estimate` | `Hilbert/Analytic/DorgeBauerPuiseux.lean:1306` | delete the binder (:1309–1310); adjust the `obtain` pattern at :1317 (5 components, not 6) and the two calls at :1318, :1322 |
| 5 | `hilbert_irreducibility_monic` | `Hilbert/HilbertIrreducibility.lean:255` | delete the binder (:257–258); drop the argument at :326 |
| 6 | `hilbert_irreducibility_theorem` | `Hilbert/HilbertIrreducibility.lean:423` | delete the binder (:425–426); drop the arguments at :431 and :459 |
| 7 | `reducibleLocus_not_univ` | `Hilbert/HilbertIrreducibility.lean:477` | delete the binder (:479–480); drop the argument at :484 |
| 8 | `monicAssociate_absIrr` | `Hilbert/HilbertIrreducibility.lean:188` | becomes dead (0 external references) — delete, ~70 lines |
| 9 | `integral_model_absIrr` | `Hilbert/Analytic/IntegralModelExists.lean:30` | becomes dead — delete, ~20 lines |
| 10 | `irreducible_comp_C_mul_X` | `Hilbert/HilbertIrreducibility.lean:139` | only used by `monicAssociate_absIrr`; becomes dead — delete, ~50 lines |

Net: **six signature edits, ~140 lines of now-dead proof deleted, zero new mathematics.**

There is no risk that item 1 is wrong: an underscore-prefixed binder cannot be referenced
in the body, and I confirmed by inspection of `.../DorgeBauerPuiseux.lean:1148–1272` that
neither `abs_irr` nor `AlgebraicClosure` occurs anywhere in it.

---

## 3. Route A — drop absolute irreducibility over `ℚ` directly

**Shape.** Exactly the table in §2. The resulting statement is

```lean
theorem hilbert_irreducibility_theorem (f : Polynomial (Polynomial ℚ))
    (hf : Irreducible f) (hf_deg : 1 ≤ f.natDegree) :
    Set.Infinite {t : ℤ | Irreducible (specialize f t)}
```

i.e. **`ℚ` is Hilbertian** in the concrete `ℤ`-specialization form. Note the hypothesis
`Irreducible f` is irreducibility in the ring `(ℚ[T])[X]`, which for non-monic `f` also
carries primitivity over `ℚ[T]`; that is the standard normalisation and costs the callers
nothing.

**Downstream, `of_regular_family` loses its `hGabs` hypothesis:**

```lean
-- InverseGalois/Hilbert/RegularExtension.lean:136
theorem of_regular_family {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (F G : Polynomial (Polynomial ℚ)) … (hGirr : Irreducible G)
    -- (hGabs : Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))))  ← delete
    …
```

That is the real payoff: `of_regular_family` becomes a *non-regular* realization seam, and
the phrase "regular" in its name/docstring becomes historical.

**Effort.** Files touched: 4 Lean files for the core (`DorgeBauerPuiseux.lean`,
`IntegralModelExists.lean`, `HilbertIrreducibility.lean`, `RegularExtension.lean`) plus 3
caller sites that become simpler (`SymmetricViaHIT.lean:191`, `Alternating.lean:201`,
`Rigidity/RET/Specialization.lean:1111`). Roughly 150 lines deleted, ~15 lines edited.
The dominant cost is one full `lake build` (≈8500 jobs; `RET/Product.lean` alone is ~80 min
per the project notes) plus fixing whatever `simp_all`/`grind` scripts drift when a
hypothesis disappears from context — the standard hazard in this repo, and the reason to
budget days rather than hours.

**Effort tag: S.** Call it 1–3 days including two full builds.

*Optional second step (do it in the same PR or not at all):* keep the strong-hypothesis
version around as a deprecated alias so the `Sₙ`/`Aₙ`/rigidity callers don't all need
touching at once. Not recommended — the callers already have `hGabs` in hand and simply
stop passing it.

---

## 4. Route B — "a finite extension of a Hilbertian field is Hilbertian"

Fried–Jarden, *Field Arithmetic*, Prop. 12.2.3; Lang, *FDG* ch. 9.

### 4.1 The proof, in the form best suited to Lean

Let `K` be Hilbertian, `L/K` finite (separable; automatic in char 0). Given
`f ∈ L[T][X]` monic, irreducible over `L(T)`, `d := deg_X f ≥ 1`, find infinitely many
`a` with `f(a,X)` irreducible over `L`. Write `e := [L:K]`.

1. Put `E := L(T)[X]/(f)`, a field, finite separable over `K(T)` of degree `e·d`.
2. Pick a primitive element `y` with `E = K(T)(y)`; let `h ∈ K[T][Y]` be (a cleared-
   denominator, monic-in-`Y` model of) its minimal polynomial over `K(T)`, so
   `deg_Y h = e·d` and `h` is irreducible over `K(T)`.
3. **Apply Hilbertianity of `K`** to `h`: infinitely many `a` with `h(a,Y)` irreducible
   over `K`. Put `E_a := K[Y]/(h(a,Y))`, a field with `[E_a : K] = e·d`.
4. **Transport the tower.** Since `L ⊆ E`, write `θ = R(T,y)` for a generator `θ` of `L/K`
   with minimal polynomial `p ∈ K[Y]`, `deg p = e`; and `x = S(T,y)` for the root of `f`;
   and `y = Q(T,θ,x)` (possible because `E = L(T)(x)`). Each of `R, S, Q` is a rational
   function in `T`; discard the finitely many `a` hitting a denominator or a discriminant.
   Then `θ_a := R(a, y_a)` satisfies `p(θ_a) = 0`, so `K(θ_a) ≅ L` sits inside `E_a` with
   `[K(θ_a):K] = e`; `x_a := S(a,y_a)` satisfies `f(a, x_a) = 0`; and
   `E_a = K(θ_a, x_a)` via `Q`.
5. **Count.** `[E_a : K(θ_a)] = e·d / e = d`, and `E_a = K(θ_a)(x_a)`, so `minpoly` of
   `x_a` over `K(θ_a) ≅ L` has degree exactly `d` and divides the degree-`d` polynomial
   `f(a,X)`. Hence `f(a,X)` is irreducible over `L`. ∎

Note that the `a` produced live in `K`, not merely in `L` — Hilbertian-ness of `L` is
witnessed by base-field points, which is the classical strengthening.

The alternative Fried–Jarden presentation replaces step 4 by valuation theory (the place
`T ↦ a` of `K(T)`, its extensions to `E`, and the fact that the residue field of the
constant subextension `L(T)` at a `K`-rational place is `L`). That is *shorter on paper*
and *much longer in Lean*, since it needs unramified-extension-of-places machinery that
Mathlib does not have for function fields. The rational-function bookkeeping of step 4 is
elementary and self-contained; recommend it.

### 4.2 Ingredient inventory

| Ingredient | Status | Name / note |
|---|---|---|
| Hilbertianity of the base `K = ℚ` | **available after Route A** | `hilbert_irreducibility_theorem`, `InverseGalois/Hilbert/HilbertIrreducibility.lean:423` |
| A `IsHilbertian` predicate / Hilbert sets | **absent everywhere** | grep for `hilbertian|IsHilbertian|HilbertSet` over `$M/Mathlib` → 0 hits. The repo has no abstract predicate either; HIT is stated concretely for `ℚ`/`ℤ`. Route B must either define one or be stated concretely for `L/ℚ`. |
| Primitive element | **Mathlib** | `Field.exists_primitive_element`, `$M/Mathlib/FieldTheory/PrimitiveElement.lean:213` |
| Degree multiplicativity in a tower | **Mathlib** | `Module.finrank_mul_finrank` (already used at `InverseGalois/Hilbert/RegularExtension.lean:86`) |
| `[K(α):K] = deg minpoly α` | **Mathlib** | `IntermediateField.adjoin.finrank` (used at `RegularExtension.lean:79`) |
| Identify a minimal polynomial | **Mathlib** | `minpoly.eq_of_irreducible_of_monic` (used at `RegularExtension.lean:62`) |
| Gauss lemma / clearing denominators | **Mathlib** | `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map` (`$M/Mathlib/RingTheory/Polynomial/GaussLemma.lean:240`); `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` (`:149`) |
| Newton–Puiseux / Krull input | **not needed** in this presentation | (Mathlib has *no* Puiseux series at all: grep `puiseux` over `$M/Mathlib` → 0 hits. The repo builds its own in `InverseGalois/Hilbert/Analytic/*Puiseux*`.) |
| "Hilbertian in 1 variable ⇒ in `n` variables" | **absent** | needed for Ikeda, *not* for Prop. 12.2.3 itself. Fried–Jarden §12.1 / ch. 13. |
| Places of function fields, residue fields of `L(T)` | **absent** | only the valuation-theoretic presentation needs it; avoid. |
| Bertini/Noether "specialization preserves irreducibility" | **absent** | `$M` has nothing; `Polynomial.Monic.irreducible_of_irreducible_map` (`$M/Mathlib/Algebra/Polynomial/Eval/Irreducible.lean:44`) is the only related tool and goes the wrong way. |

### 4.3 Judgement

Route B is genuinely formalizable on top of Route A, and needs **no** new analysis, **no**
Puiseux theory, and **no** number-theoretic input. What it does need is a large amount of
"write `θ` as a rational function of `y`, specialize, avoid finitely many bad `a`"
bookkeeping — the kind of thing that reliably triples in size in Lean. **Effort: L**
(1–3 months). It also requires deciding on an interface: either a concrete
`ℚ`-and-a-fixed-`L` statement, or a genuine `IsHilbertian` class, which Mathlib does not
supply and which would be the right thing to upstream.

**Route B is not needed for the Ikeda target.** It *is* needed for the other consumer, see
§6.3.

---

## 5. Route C — port the counting proof to `𝒪_K`

### 5.1 What is formal and what is not

**Formal (survives a base change with modest work):**

* `specialize`, `specialize_monic`, `specialize_monic_natDegree`, `reducibleLocus`,
  `irreducible_iff_not_in_reducibleLocus`, `irreducible_specialize_of_C_mul`,
  `hit_degree_one`, `union_sublinear_ncard` — pure `Polynomial`/`Set` algebra
  (`HilbertIrreducibility.lean:63, 70, 78, 471, 499, 399, 376, 94`).
* `resolvent_exists` and everything under `InverseGalois/Resolvent/ResolventConstruction.lean`
  (`exists_esymm_notMem:325`, `exists_generic_lam:393`) — already stated for *arbitrary*
  fields `K ⊆ L` in char 0. Nothing to do.
* `FmapToRatFunc_irreducible` (`DorgeBauerPuiseux.lean:986`) — the Gauss step. Over `𝒪_K`
  this **must** be redone: `𝒪_K` is Dedekind but generally not a UFD, so the content /
  `IsPrimitive` route is unavailable. The monic route survives:
  `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`
  (`$M/Mathlib/RingTheory/Polynomial/GaussLemma.lean:149`) needs only
  `[IsIntegrallyClosed R]`, and `𝒪_K[T]` is integrally closed. Since the whole pipeline
  is monic-normalized this is fine, but the current proof (a hand-rolled
  `FractionRing (Polynomial ℤ) ≃+* FractionRing (Polynomial ℚ)` isomorphism, ~180 lines)
  would need rewriting.

**Genuinely `ℚ`/`ℤ`-specific (must be reproved, not ported):**

* `cauchy_root_bound`, `cauchy_root_bound_max`, `factor_coeff_bound`
  (`DorgeBauer.lean:174, 197, 222`) — stated over `ℂ`, so *individually* they survive, but
  over `𝒪_K` one needs them **simultaneously at all `r₁ + r₂` archimedean places**, i.e.
  a Minkowski-embedding version. Mathlib now has `Polynomial.cauchyBound` and
  `Polynomial.IsRoot.norm_lt_cauchyBound`
  (`$M/Mathlib/Analysis/Polynomial/CauchyBound.lean:33, 74`), which would replace the
  hand-rolled versions.
* `int_roots_bounded`, `finite_specializations_for_fixed_factor`, `boundedMonicPolys`,
  `finite_boundedMonicPolys` (`DorgeBauer.lean:299, 317, 413, 420`) — "finitely many
  integers of bounded size", "finitely many monic integer polynomials with bounded
  coefficients". Over `𝒪_K` this is **Northcott**. Mathlib has the right engine —
  `NumberField.Embeddings.finite_of_norm_le`
  (`$M/Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean:109`) and
  `NumberField.Embeddings.coeff_bdd_of_norm_le` (`:94`) — but *not* the packaged
  statement.
* `infinite_complement_of_sublinear_ncard` (`DorgeBauer.lean:457`) — "`o(N)` bad points in
  `[-N,N]` ⇒ infinitely many good ones". Over `𝒪_K` the box `Set.Icc (-N) N` becomes a
  dilated fundamental domain, and one needs `#(𝒪_K ∩ N·B) ≍ N^{[K:ℚ]}`. Mathlib supplies
  the asymptotic: `ZLattice.covolume.tendsto_card_div_pow`
  (`$M/Mathlib/Algebra/Module/ZLattice/Covolume.lean:311`), plus
  `NumberField.mixedEmbedding.integerLattice` and its `IsZLattice` instance
  (`$M/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:676`). This part is
  workable.
* `int_root_locus_small_sublinear` (`DorgeBauer.lean:588`) — the `O(√N)` bound obtained by
  `Nat.sqrt` and counting integer roots of the coefficient polynomials. Needs a full
  rewrite in lattice-counting terms.
* **The entire real-branch machinery** — `int_root_locus_large_sublinear`
  (`DorgeBauerPuiseux.lean:894`), `int_root_locus_large_cover` (`:843`),
  `large_root_branch_data` (`:737`), `real_branches_puiseux` (`:309`),
  `real_algebraic_branches` (`:372`), `branch_leading_asymptotics` (`:426`),
  `real_branches_on_tail` (`:481`), `real_branches_sign_deriv_pos` (`:646`),
  `HasKDerivDecay` (`DorgeBauer.lean:1137`), `graph_integer_points_sublinear` (`:1141`),
  `pos_branches_cover_sublinear` (`:1249`), `neg_branches_cover_sublinear` (`:1279`),
  `rpow_mul_hasKDerivDecay` (`:1389`), and the entirety of
  `DorgeBauerBranches.lean` (1219 lines), `DorgeBauerAnalytic.lean` (610),
  `NewtonPuiseux.lean` (848), `PuiseuxTail.lean` (1214), `SmoothRootBranches.lean` (615),
  `BranchAnalytic.lean` (668). **This is the whole proof and it is one-real-dimensional
  by construction.** Over `𝒪_K` the analogue is: count lattice points of
  `𝒪_K × 𝒪_K ⊂ ℝ^{2n}` lying on a real-algebraic hypersurface in a dilated box, which is
  a different theorem with a different proof (Dörge's argument over number fields, as in
  Franz 1931 / Inaba, in practice reduces back to `ℚ` — i.e. to Route B).

### 5.2 Estimate

Roughly 6000 lines of the analytic tower would have to be rebuilt on a genuinely different
argument, on top of a lattice-point-counting layer Mathlib supplies only in asymptotic
form. **Effort: XL** (6–18 months). Do not do this. If the number-field statement is
wanted, Route B reaches it with a small fraction of the work by *reusing* the `ℚ` counting
proof as a black box.

---

## 6. Route D — can the general theorem be avoided?

### 6.1 The setup

`M/ℚ(T)` Galois with group `G`; constant field `L := algebraicClosure ℚ M`, a number
field, with `Gal(L/ℚ) ≅ G/N` where `N = Gal(M/L(T))`; `M/L(T)` is regular with group `N`.
Goal: a `G`-extension of `ℚ`.

For a good `t₀ ∈ ℤ` and a place of `M` above `T = t₀`, the decomposition group
`D ≤ G` is `Gal(M_{t₀}/ℚ)`. Because `L` is *constant*, the residue field of `L(T)` at a
`ℚ`-rational place is `L` itself, so `D` always surjects onto `Gal(L/ℚ) = G/N`, i.e.

> `D · N = G` for **every** good `t₀`, with no Hilbert irreducibility at all.

What HIT buys is `D ⊇ N`, hence `D = G`.

### 6.2 The one case where it works for free

If `N ≤ frattini G`, then `D · N = G` forces `D = G` outright, since a proper `D` lies in
a maximal subgroup which also contains `frattini G`. Mathlib has this:
`frattini_nongenerating` (`$M/Mathlib/GroupTheory/Frattini.lean:53`,
`K ⊔ frattini G = ⊤ → K = ⊤`) and `frattini` (`:24`). So:

> **Route D, restricted form.** If the constant-field kernel `N` is contained in
> `frattini G`, every good `ℚ`-rational specialization already realizes `G`, using only
> the "constants specialize to themselves" bookkeeping and no HIT whatsoever.

This is a real theorem and worth ~200 lines if a use arises. It is also exactly the case
of a **non-split, Frattini** embedding problem.

### 6.3 Why it does not help the target

Ikeda's theorem is a statement about **split** embedding problems: `G = A ⋊ H` with `A` the
kernel and `H` a complement. A complement is never inside the Frattini subgroup (unless
`A = 1`), so §6.2 is vacuous exactly where it is needed.

The other obvious dodge also fails. One could try to use only the *regular* extension
`M/L(T)` (group `N`, absolutely irreducible over `L̄(T) = ℚ̄(T)`) and specialize
`T ↦ t₀ ∈ ℚ`. But that is Hilbert irreducibility over `L`, a number field — Route B or C,
not the repo's `ℚ`-only theorem. And one cannot replace `M` by a regular `ℚ(T)`-model:
if `M₀/ℚ(T)` is regular with group `N` and `L/ℚ` has group `Q`, then `M₀` and `L(T)` are
linearly disjoint over `ℚ(T)` precisely *because* `M₀` is regular, so
`Gal(M₀L/ℚ(T)) ≅ N × Q` — a direct product. The whole point of the wreath-product /
Ikeda construction is to get a non-trivial semidirect product, and the twisting lives
exactly in the non-regularity.

**Honest verdict: no.** Route D cannot be made to work for the target application at any
price in extra hypotheses short of assuming the embedding problem is Frattini, which
contradicts Ikeda's split hypothesis. It is moot anyway, because Route A is free.

### 6.4 A *different* consumer that Route D also cannot help

`InverseGalois/Rigidity/RET/Descent/StableDescent.lean:226` produces

```lean
theorem GeomTower.exists_regular_numberField :
    ∃ K : IntermediateField ℚ tw.Ω, K ≤ algebraicClosure ℚ tw.Ω ∧
      IsRegularGaloisGroupOver ↥K G
```

and `Rigidity.RET.Descent.exists_regular_numberField_of_orbitRigid` (`:274`) packages it as
`∃ (K : Type) (_ : Field K) (_ : NumberField K), IsRegularGaloisGroupOver K G`. The
certificates `Rigidity.PSL27.exists_regular_numberField`
(`InverseGalois/Rigidity/Examples/PSL27.lean:355`),
`Rigidity.MathieuM24.exists_regular_numberField`
(`InverseGalois/Rigidity/Examples/MathieuM24.lean:695`),
`Rigidity.PSL2F23.exists_regular_numberField`
(`InverseGalois/Rigidity/Examples/PSL2F23.lean:538`) etc. all land here.

Here the situation is structurally different from §6.1: the surjection produced is
`ψ : tw.stab ↠ G` where `tw.stab ≤ tw.E ≅ Gal(Ω/ℚ(T))` is a *proper* subgroup cutting out
`K(T)`. There is in general **no** `G`-extension of `ℚ(T)` at all — only of `K(T)`. So
Route A does not touch these, and Route D's Frattini trick has nothing to bite on.
Converting them needs Hilbertianity of `K` (**Route B**), and even then it yields "`G` is a
Galois group over the number field `K`", *not* over `ℚ`. Getting these to `ℚ` is a
separate problem (rationality of the rigid class tuple), and should not be conflated with
the present one.

---

## 7. Recommendation

**Route A**, then optionally Route B as an independent, later project.

### 7.1 Route A, lemma by lemma

Each step is a signature edit plus proof-script repair; none introduces new mathematics.
Do them bottom-up so the build fails in one place at a time.

**A1 [S].** `InverseGalois/Hilbert/Analytic/DorgeBauerPuiseux.lean:1148`
```lean
lemma resolvent_exists (F : Polynomial (Polynomial ℤ))
    (hF_monic : F.Monic) (hF_irr : Irreducible F)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < F.natDegree) :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ 2 ≤ P.natDegree ∧
      (∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) ∧
      (∀ t : ℤ, (∃ g : Polynomial ℤ, g.natDegree = k ∧ g.Monic ∧
        g ∣ (F.map (Polynomial.evalRingHom t))) →
        ∃ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y)
```
Proof body **unchanged** (delete the binder only).

**A2 [S].** `.../DorgeBauerPuiseux.lean:1273` — same conclusion as now, binder
`hF_abs_irr` deleted, call at :1285 loses one argument.
```lean
lemma int_factor_locus_sublinear (F : Polynomial (Polynomial ℤ))
    (hF_monic : F.Monic) (hF_irr : Irreducible F)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < F.natDegree) :
    ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard ({t : ℤ | ∃ g : Polynomial ℤ, g.natDegree = k ∧ g.Monic ∧
        g ∣ (F.map (Polynomial.evalRingHom t))} ∩ Set.Icc (-(N:ℤ)) (N:ℤ)) : ℝ)
        ≤ C * (N : ℝ) ^ α
```

**A3 [S].** `InverseGalois/Hilbert/Analytic/IntegralModelExists.lean:51`
```lean
theorem integral_model_exists (f : Polynomial (Polynomial ℚ))
    (hf_irr : Irreducible f) (hf_monic : f.Monic) :
    ∃ F : Polynomial (Polynomial ℤ),
      F.Monic ∧ F.natDegree = f.natDegree ∧ Irreducible F ∧
      ∀ (t : ℤ) (k : ℕ), 1 ≤ k →
        (∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧ g ∣ f.map (evalRingHom (↑t : ℚ))) →
        (∃ g : Polynomial ℤ, g.natDegree = k ∧ g.Monic ∧ g ∣ F.map (evalRingHom t))
```
Delete `hF_abs_irr_out` (`:132–134`); shrink the final anonymous constructor (`:135`).
Then delete `integral_model_absIrr` (`:30`).

**A4 [S].** `.../DorgeBauerPuiseux.lean:1306`
```lean
lemma dorge_density_estimate (f : Polynomial (Polynomial ℚ))
    (hf_irr : Irreducible f) (hf_monic : f.Monic)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < f.natDegree) :
    ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard ({t : ℤ | ∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧
        g ∣ (f.map (Polynomial.evalRingHom (↑t : ℚ)))} ∩ Set.Icc (-(N:ℤ)) (N:ℤ)) : ℝ)
        ≤ C * (N : ℝ) ^ α
```
Adjust the `obtain` at `:1317` to five components.

**A5 [S].** `InverseGalois/Hilbert/HilbertIrreducibility.lean:255`
```lean
theorem hilbert_irreducibility_monic (f : Polynomial (Polynomial ℚ))
    (hf : Irreducible f) (hf_monic : f.Monic) (hf_deg : 2 ≤ f.natDegree) :
    Set.Infinite {t : ℤ | Irreducible (specialize f t)}
```

**A6 [S].** `InverseGalois/Hilbert/HilbertIrreducibility.lean:423` — **the deliverable.**
```lean
/-- **Hilbert's irreducibility theorem for integer specializations (`ℚ` is Hilbertian).** -/
theorem hilbert_irreducibility_theorem (f : Polynomial (Polynomial ℚ))
    (hf : Irreducible f) (hf_deg : 1 ≤ f.natDegree) :
    Set.Infinite {t : ℤ | Irreducible (specialize f t)}
```
Then delete `monicAssociate_absIrr` (`:188`) and `irreducible_comp_C_mul_X` (`:139`), both
now dead.

**A7 [S].** `InverseGalois/Hilbert/HilbertIrreducibility.lean:477` —
`reducibleLocus_not_univ` loses its binder.

**A8 [S].** `InverseGalois/Hilbert/RegularExtension.lean:136` — `of_regular_family` loses
`hGabs`; update its docstring, which currently justifies the hypothesis
(`RegularExtension.lean:124–132`). Then fix the three call sites:
`InverseGalois/Hilbert/SymmetricViaHIT.lean:191`,
`InverseGalois/Hilbert/Alternating.lean:201`,
`InverseGalois/Rigidity/RET/Specialization.lean:1111`.
Optionally also simplify `SymmetricViaHIT.exists_resolvent_family`
(`SymmetricViaHIT.lean:178`) and the `ResolventFamily`/`AlternatingFamily`
`*_abs_irreducible` producers, which become unnecessary for HIT (they may still be wanted
for their own sake — check before deleting; `fullResolvent_abs_irreducible` is referenced
at `ResolventFamily.lean:1184, 1233`).

**A9 [S–M].** New: the Ikeda-facing wrapper, stated in the vocabulary the wreath-product
milestone will want.
```lean
/-- A Galois extension of `ℚ(T)` with group `G` — regular or not — realizes `G` over `ℚ`. -/
theorem isInverseGalois_of_galois_ratFunc {G : Type} [Group G] [Finite G]
    (M : Type) [Field M] [Algebra (RatFunc ℚ) M] [IsGalois (RatFunc ℚ) M]
    (e : (M ≃ₐ[RatFunc ℚ] M) ≃* G) : IsInverseGalois G
```
This is the piece that is *not* pure deletion: it turns an abstract Galois extension of
`RatFunc ℚ` into a `Polynomial (Polynomial ℚ)` model (primitive element, clear
denominators, monic-ize) so that `hilbert_irreducibility_theorem` applies, then reruns the
`realizable_of_embeds_and_root` argument. Much of the plumbing already exists in
`InverseGalois/Rigidity/RET/Specialization.lean` (see `:711` onwards, which builds exactly
this bundle in the regular case). Budget **M** (1–3 weeks) for this, and note that it —
not A1–A8 — is the real work of the milestone.

### 7.2 What to do after

1. Ikeda milestones 2–5 as already scoped in `docs/Development/Shafarevich.md:623–…`.
   Milestone 3 there ("multivariable HIT over `ℚ`") is unaffected by this document and
   remains **M**.
2. Route B, as an independent project, at **L**, to unlock the
   `exists_regular_numberField` family (§6.4) — but be clear that it yields realizations
   over `K`, not over `ℚ`.
3. Do **not** attempt Route C.

---

## 8. Appendix — every declaration in `InverseGalois/Hilbert/HilbertIrreducibility.lean`

592 lines, no `sorry`, no `axiom`. "ext refs" = references from other files in
`InverseGalois/`.

| line | kind | name | statement (abridged to one line) | ext refs |
|---|---|---|---|---|
| 63 | `def` | `specialize` | `specialize (f : Polynomial (Polynomial ℚ)) (t : ℤ) : Polynomial ℚ := f.map (Polynomial.evalRingHom (↑t : ℚ))` | many |
| 70 | `lemma` | `specialize_monic` | `f.Monic → (specialize f t).Monic` | 4 |
| 78 | `lemma` | `specialize_monic_natDegree` | `f.Monic → (specialize f t).natDegree = f.natDegree` | 5 |
| 94 | `lemma` | `union_sublinear_ncard` | for `S : Fin n → Set ℤ` each with `ncard (S i ∩ Icc (-N) N) ≤ C·N^α`, the union satisfies `≤ n·C·N^α` | 0 |
| 139 | `lemma` | `irreducible_comp_C_mul_X` | over a field `L`, `c ≠ 0` → `Irreducible (q.comp (C c * X)) ↔ Irreducible q` | 0 |
| 188 | `lemma` | `monicAssociate_absIrr` | `2 ≤ f.natDegree` and `f` absolutely irreducible → `monicAssociate f` is absolutely irreducible | 0 |
| 255 | `theorem` | `hilbert_irreducibility_monic` | `f` irreducible, monic, `2 ≤ natDegree`, absolutely irreducible → `{t : ℤ \| Irreducible (specialize f t)}.Infinite` | 0 |
| 376 | `lemma` | `hit_degree_one` | `f` irreducible with `f.natDegree = 1` → `{t : ℤ \| Irreducible (specialize f t)}.Infinite` | 0 |
| 399 | `lemma` | `irreducible_specialize_of_C_mul` | `IsUnit c` → `Irreducible (specialize (C c * f) t) ↔ Irreducible (specialize f t)` | 0 |
| 423 | `theorem` | `hilbert_irreducibility_theorem` | `f` irreducible, `1 ≤ f.natDegree`, absolutely irreducible → `{t : ℤ \| Irreducible (specialize f t)}.Infinite` | 2 (`RegularExtension.lean:149`, `SymmetricViaHIT.lean:191`) |
| 471 | `def` | `reducibleLocus` | `reducibleLocus f k = {t : ℤ \| ∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧ g ∣ specialize f t}` | 0 |
| 477 | `lemma` | `reducibleLocus_not_univ` | `f` irreducible, monic, absolutely irreducible, `1 ≤ k < f.natDegree` → `reducibleLocus f k ≠ Set.univ` | 0 |
| 499 | `lemma` | `irreducible_iff_not_in_reducibleLocus` | if `(specialize f t).natDegree = f.natDegree` and `1 ≤ f.natDegree`, then `Irreducible (specialize f t) ↔ ∀ k, 1 ≤ k → k < f.natDegree → t ∉ reducibleLocus f k` | 0 |

Nine of the thirteen have no external users; `union_sublinear_ncard`,
`irreducible_specialize_of_C_mul`, `reducibleLocus_not_univ` and
`irreducible_iff_not_in_reducibleLocus` are not even used inside the file. Route A is a
natural moment to prune.

## 9. Appendix — callers

**`hilbert_irreducibility_theorem` (2 real call sites):**

* `InverseGalois/Hilbert/RegularExtension.lean:149`, inside
  `IsInverseGalois.of_regular_family`. **Would benefit:** the `hGabs` hypothesis
  disappears from the repo's main realization seam.
* `InverseGalois/Hilbert/SymmetricViaHIT.lean:191`, inside
  `SymmetricViaHIT.exists_resolvent_family`. Would benefit cosmetically (it already has
  `hGabs` from `ResolventFamily.exists_resolvent_family_core`).

**`IsInverseGalois.of_regular_family` (2 real call sites):**

* `InverseGalois/Hilbert/Alternating.lean:201` — `Aₙ`. Already has `hGabs`
  (`anResolvent_abs_irreducible`, `AlternatingFamilyAnalytic.lean:93`). No mathematical
  benefit, just fewer hypotheses.
* `InverseGalois/Rigidity/RET/Specialization.lean:1111` — the rigidity bridge
  `IsRegularInverseGalois.isInverseGalois`. **This is the interesting one.** Today it can
  only consume *regular* `ℚ(T)`-realizations. After Route A + step A9, the same file could
  host a non-regular sibling consuming any `G`-Galois extension of `ℚ(T)`, which is
  precisely the Ikeda interface.

**Documentation-only mentions** (no code change needed):
`InverseGalois/Rigidity/RET/Specialization.lean:28`,
`InverseGalois/Rigidity/RET.lean:490`,
`InverseGalois/Resolvent/ResolventFamily.lean:20`,
`InverseGalois/Rigidity/RET/{Existence,RegularAlternating,Statement,RegularResolvent}.lean`,
`InverseGalois/Resolvent/AlternatingResolvent.lean:17`,
`docs/Development/{HilbertPlan,Shafarevich}.md`.
