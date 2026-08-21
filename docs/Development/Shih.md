# `PSL₂(𝔽ₚ)` over `ℚ(T)`: Shih's theorem vs. index-two descent

*Assessment written 2026-08-20, revised 2026-08-21, on the `shih` branch.*

The goal is to realize the simple groups `PSL₂(𝔽ₚ)` as **regular** Galois groups over `ℚ(T)`.
There are two candidate routes. This document compares them, ranks the specific obstructions to
each, and records what has been formalized so far.

**Verdict: Route 2 (index-two descent) is cheaper by two or three orders of magnitude, but it is
still weeks of work, and it only reaches a finite list of primes. Route 1 (Shih) is not
formalizable with today's Mathlib; the gap is a multi-year algebraic-geometry programme.**

**Status as of 2026-08-21.** Neither route has been completed, and `PSL₂(𝔽ₚ)` is *not* realized
for any `p`. What has been done instead:

* the whole branch is `sorry`-free and axiom-free again, by turning the two unproved leaves of
  Route 2 into **explicit hypotheses** and by **deleting** the two unproved leaves of Route 1
  (one of which, `AtkinLehner`, was an inconsistent statement — see below);
* the overgroups `PGL₂(𝔽ₚ)` are now realized regularly over `ℚ(T)` for `p = 7, 11, 13, 17, 19`,
  from explicit kernel-checked rigidity certificates, and the machinery to add more primes exists;
* the prime list for Route 2 has been recomputed and corrected: `p = 29` **does** admit a rational
  rigid triple, and among the primes at most `37` only `p = 23` does not.

---

## The two routes at a glance

| | Route 1 — Shih, modular curves | Route 2 — index-two descent from `PGL₂(𝔽ₚ)` |
|---|---|---|
| Primes reached | all `p` with `(2/p) = -1` or `(3/p) = -1` or `(7/p) = -1`, i.e. density `7/8` | only `p` for which `PGL₂(𝔽ₚ)` has a *rational rigid triple*: among `p ≤ 37` that is `5, 7, 11, 13, 17, 19, 29, 31, 37` (a finite list) |
| Mathematical input | moduli of elliptic curves, Weil pairing, Atkin–Lehner, Shimura reciprocity | the rigidity method (already in this repo) plus ramification bookkeeping |
| Mathlib prerequisites | essentially all absent (see below) | all present |
| Repo prerequisites | none | `RigidityCertificate`, the full RET descent tower, the `PGL₂(𝔽₇)` certificate |
| Open `sorry`s today | 0 — the unproved statements were deleted | 0 — the unproved statements are now explicit hypotheses |
| Honest effort estimate | multi-year, and gated on a large Mathlib programme | 3–8 focused weeks |

Two remarks that matter for choosing:

* Route 2 does **not** subsume Route 1. `PGL₂(𝔽ₚ)` has a rational rigid triple only for finitely
  many `p`. Shih covers seven eighths of all primes. So Route 2 is a shortcut to a few named
  groups, not to the family.

  The criterion is a torus computation. `PGL₂(𝔽ₚ)` acts on `ℙ¹(𝔽ₚ)` with two cyclic tori, of
  orders `p - 1` and `p + 1`; an element of order `4` in a torus of order `m` is *outer* (lies
  outside `PSL₂(𝔽ₚ)`) exactly when `4 ∣ m` and `8 ∤ m`, and one of order `6` exactly when `6 ∣ m`
  and `12 ∤ m`. A rational rigid triple needs an outer class of order `4` or `6` to pair with the
  outer involution and a `p`-cycle. Running this over the primes `p ≤ 37`:

  | `p` | `p-1` | `p+1` | outer order `4` or `6`? |
  |---|---|---|---|
  | 5 | 4 | 6 | yes (4 ∣ 4, 8 ∤ 4) |
  | 7 | 6 | 8 | yes (6 ∣ 6, 12 ∤ 6) |
  | 11 | 10 | 12 | yes (4 ∣ 12, 8 ∤ 12) |
  | 13 | 12 | 14 | yes (4 ∣ 12) |
  | 17 | 16 | 18 | yes (6 ∣ 18, 12 ∤ 18) |
  | 19 | 18 | 20 | yes (4 ∣ 20, 8 ∤ 20) |
  | 23 | 22 | 24 | **no** (8 ∣ 24 and 12 ∣ 24) |
  | 29 | 28 | 30 | yes (4 ∣ 28, 8 ∤ 28) |
  | 31 | 30 | 32 | yes (6 ∣ 30, 12 ∤ 30) |
  | 37 | 36 | 38 | yes (4 ∣ 36, 8 ∤ 36) |

  This corrects the earlier note in *Lie-type rigidity survey*, which listed `29` as failing. A
  direct search over `PGL₂(𝔽₂₉)` confirms both halves: an explicit rational rigid triple
  `(2A, 4A, 29A)` with class sizes `406, 870, 840` exists, and no triple of the shape
  `(involution, order 4 or 6, 23-cycle)` exists in `PGL₂(𝔽₂₃)`.
* Route 2 is genuinely worth doing anyway: the same index-two theorem also unlocks `M₂₂` from the
  landed `Aut(M₂₂) = M₂₂ : 2` certificate, which rigidity provably cannot reach directly (`M₂₂`
  has no rigid triple at all).

---

## Route 1: Shih's construction

### The mathematics

Fix a prime `p ≥ 5` and an auxiliary level `N ∈ {2, 3, 7}`.

1. The modular curve `X(p)` is a Galois cover of the `j`-line, defined over `ℚ`, with group
   `GL₂(𝔽ₚ)/{±1}`. Its constant field is `ℚ(ζₚ)`, and the restriction map to
   `Gal(ℚ(ζₚ)/ℚ) ≅ (ℤ/p)ˣ` is the determinant. The geometric monodromy group is therefore
   `SL₂(𝔽ₚ)/{±1} = PSL₂(𝔽ₚ)` — the right group, but with far too many constants.
2. Pull back along `X₀(N) → X(1)`. For `N ∈ {2, 3, 7}` the curve `X₀(N)` has genus `0` with a
   rational cusp, so `ℚ(X₀(N)) = ℚ(t)`, with hauptmoduln
   `j = (t+256)³/t²` (`N = 2`), `j = (t+27)(t+243)³/t³` (`N = 3`),
   `j = (t²+13t+49)(t²+245t+2401)³/t⁷` (`N = 7`).
3. The Atkin–Lehner involution `w_N` acts on `ℚ(t)` as a fractional linear substitution
   `t ↦ c/t`, and `ℚ(t)^{w_N}` is again a rational function field.
4. On moduli `w_N` sends `(E, C)` to `(E/C, E[N]/C)`; an `N`-isogeny multiplies the Weil pairing
   on the `p`-torsion by `N`, so a lift `ω` of `w_N` to the level-`p` tower acts on `μₚ` by
   `ζ ↦ ζ^N`.
5. If `N` is a quadratic non-residue mod `p`, `ω` moves the constants by a non-square multiplier,
   and the twisted tower over `ℚ(t)^{w_N}` is a **regular** `PSL₂(𝔽ₚ)`-extension.

### Which primes

Shih's hypothesis depends only on `p mod 168`. It **fails** exactly for
`p ≡ 1, 25, 47, 121, 143, 167 (mod 168)` — six of the forty-eight units mod `168`, density `1/8`.
The smallest excluded prime is `47`. Note `p = 7` qualifies (`3` is a non-residue mod `7`) and
`p = 23` qualifies (`7` is a non-residue mod `23`) — and `23` is precisely a prime that Route 2
misses, since `PGL₂(𝔽₂₃)` has no rational rigid triple.

This part is **fully formalized and proved** in `InverseGalois/Rigidity/Examples/Shih.lean`
(`Rigidity.Shih.shihPrime_iff`), together with the three underlying quadratic-residue criteria
(`isSquare_two_iff`, `isSquare_three_iff`, `isSquare_seven_iff`).

### Ranked list of Mathlib gaps blocking Route 1

A dedicated Mathlib survey was run for this assessment. Ranked by how much has to be built:

1. **Algebraic curves over a field, with genus, divisors and Riemann–Roch.** Zero coverage. Every
   later item depends on this. Mathlib has schemes and `AlgebraicGeometry.Proj`, but no theory of
   curves, no genus, no Riemann–Roch. *This alone is a large multi-year Mathlib project.*
2. **Modular curves as algebraic curves over `ℚ`.** Zero coverage. Mathlib has `Γ₀(N)`, `Γ₁(N)`,
   `Γ(N)` as subgroups of `SL(2, ℤ)` (`Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`),
   the upper half-plane with the Möbius action and a fundamental domain
   (`Mathlib/NumberTheory/Modular.lean`), modular forms, slash actions and cusps — but no quotient
   *curve*, no model over `ℚ`, no function field. `ModularCurve` does not exist as an identifier.
3. **Moduli interpretation.** Zero coverage of level structures, of the moduli functor, or of the
   modular interpretation of points. Mathlib has Weierstrass curves, the group law and the
   `j`-invariant, but no `E[n]` as a group scheme or Galois module.
4. **Isogenies and the Weil pairing.** Zero coverage of either. The Weil-pairing multiplier is
   *the* arithmetic content of Shih's twist; without it there is nothing to twist by.
5. **Shimura reciprocity / the modular Galois representation.** Zero coverage. The statement
   "`Gal(ℚ(X(p))/ℚ(j)) ≅ GL₂(𝔽ₚ)/{±1}`, with the determinant equal to the cyclotomic character"
   is the hard input; it needs items 1–4 first. Even the group-theoretic prerequisite
   `SL(2, ℤ) ↠ SL(2, ℤ/N)` is absent.
6. **Atkin–Lehner and Fricke involutions.** Zero coverage.
7. **`PGL`.** Does not exist in Mathlib in any form. `PSL(n, R)` exists only as a bare `abbrev`
   (`Matrix.ProjectiveSpecialLinearGroup`, `Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean`)
   with no theorems attached — not even simplicity of `PSL(2, q)`, though the Iwasawa criterion is
   available and this repo's `Mathieu/PSL211Simple.lean` shows how to apply it.
8. **Regular extensions, rigidity, Hilbert irreducibility.** Absent from Mathlib — but *present in
   this repo*, so not actually a blocker.

Items 1–5 are the wall. Nothing short of a sustained Mathlib effort in arithmetic algebraic
geometry moves them.

### What of Route 1 *is* formalized here

`InverseGalois/Rigidity/Examples/Shih.lean` is now imported from `InverseGalois/Rigidity.lean` and
is `sorry`-free. It contains:

* `ShihPrime`, `isSquare_mod_three`, `isSquare_mod_seven`, `isSquare_of_mod_four_eq_three`,
  `isSquare_two_iff`, `isSquare_three_iff`, `isSquare_seven_iff`, `shihPrime_iff` (the `mod 168`
  characterization), `exists_level`;
* `atkinLehner`, `atkinLehner_mul_self`, `atkinLehner_sq`, and
  `exists_ringEquiv_atkinLehnerFixedField`: *the Atkin-Lehner quotient of a rational curve is
  rational*. This is step 3 above, and it is real content: it uses the repo's Mobius-substitution
  calculus (`RET/MobiusAut.lean`), Artin's theorem and Luroth's theorem
  (`RET/FixedField.lean`, `Hilbert/Analytic/Luroth.lean`);
* `LevelTower`, the level-`p` tower packaged as exactly the two facts the descent would consume
  (the determinant character is surjective with kernel `PSL2(Fp)`, and it is the character of the
  action on the constants), together with `LevelTower.index_ker_det`, which records that the
  geometric group has index `p - 1`: that is the obstruction the twist has to remove.

### What was deleted, and why: the `AtkinLehner` structure was inconsistent

The previous version of this file carried a structure `AtkinLehner p N tower` bundling

```
  omega        : tower.M ~=[Q] tower.M
  omega_sq     : omega.trans omega = AlgEquiv.refl
  omega_root   : forall z : tower.M, z ^ p = 1 -> omega z = z ^ N
```

together with two `sorry`s (`levelTower_atkinLehner_exists`, `isRegularInverseGalois_of_atkinLehner`)
and the assembly `shih`. **Those two fields contradict each other.** Applying `omega_root` twice,

```
  z = omega (omega z) = omega (z ^ N) = (omega z) ^ N = z ^ (N * N)
```

for every `p`-th root of unity `z` in `M`. But `M` contains a *primitive* `p`-th root of unity —
that is precisely what the `LevelTower.constants` field says, and it is the whole point of the
construction — so `N^2 = 1 (mod p)`. For `N in {2, 3, 7}` that forces `p` to divide `3`, `8` or
`48`, impossible for `p >= 5`. So `AtkinLehner p N tower` is an **empty** structure for every prime
the construction is about, and `levelTower_atkinLehner_exists` is a **false** statement, not merely
an unproved one. Anything proved from it would have been vacuous.

The mathematical error is the normalisation of the lift. The Atkin-Lehner involution `w_N` of
`X_0(N)` is an involution *on the base*, but its lifts to the level-`p` tower are only well defined
up to the geometric monodromy group, and no lift is an involution: `omega^2` lies in the geometric
group and is nontrivial. In Shih's argument what matters is the class of `omega` modulo the
geometric group and the fact that the induced action on the constants `Q(zeta_p)` is `zeta -> zeta^N`,
i.e. the image of `N` in `(Z/p)^x / ((Z/p)^x)^2`; the twist is by that class. A correct Lean
statement therefore has to replace `omega_sq` by something like `omega^2 in image of Gal(M/Q(t))`,
and cannot state the multiplier as an identity on all of `M`'s `p`-th roots of unity while also
demanding an involution.

Rather than ship a structure that is provably empty, the structure and the three declarations
depending on it were deleted. What survives is exactly what is proved. Restating Shih's input
correctly is a prerequisite for any future attempt on Route 1, and is *not* the hard part — items
1-6 of the gap list above still are.

### Effort estimate for Route 1

* The twist alone (assuming a *correctly stated* `LevelTower` and Atkin-Lehner lift as
  hypotheses): **2-4 weeks**. It is a `RegularFixedField`-style argument: identify the geometric
  subgroup, show `ω` normalizes it, show the multiplier being a non-square forces the extension to
  split off the constants, then apply `Rigidity.RET.isRegularGaloisGroupOverBase_fixedField` over
  the Atkin–Lehner line (which is already known to be rational).
* `levelTower_atkinLehner_exists`: **not estimable in person-months** with current Mathlib. It is
  gated on gaps 1–5 above. A defensible lower bound, assuming a Mathlib curves-and-Riemann–Roch
  library appears, is **1–2 person-years** on top of that.

---

## Route 2: index-two descent from `PGL₂(𝔽ₚ)`

### The mathematics

Let `cert` be a rigidity certificate for `A` with `r = 3` branch points, so the rigidity method
produces a regular `A`-cover `L/ℚ(T)` branched at three rational points `t₀, t₁, t₂` with branch
cycles `b₀, b₁, b₂` satisfying `b₀b₁b₂ = 1`. Let `H ⊴ A` have index `2`.

1. `b₀b₁b₂ = 1` forces **exactly two** of the `bᵢ` to lie outside `H`
   (`exists_two_notMem_of_index_two`, **already proved** in `Index2.lean`).
2. `F := L^H` is a regular quadratic extension of `ℚ(T)` (`finrank_sub`, **already proved**), so
   `F = ℚ(T)(√f)`.
3. `F/ℚ(T)` ramifies at `tᵢ` exactly when `bᵢ ∉ H`, and nowhere else. So exactly two finite places
   ramify and `f = c(T - tᵢ)(T - tⱼ)` up to squares.
4. The conic `y² = c(x - tᵢ)(x - tⱼ)` has the rational point `(tᵢ, 0)`, so `F ≅ ℚ(u)`
   (explicitly `u = y/(x - tᵢ)`, `x = (u²tᵢ - ctⱼ)/(u² - c)`) —
   `nonempty_algEquiv_ratFunc_of_conic`, **already proved**.
5. `L/F` is then a regular `H`-extension of a rational function field:
   `IsRegularInverseGalois H` (`isRegularInverseGalois_of_index_two`, **already proved**).

### Current state of `InverseGalois/Rigidity/RET/Descent/Index2.lean`

Imported from `InverseGalois/Rigidity/RET.lean`, ~430 lines, **`sorry`-free**. The two former
`sorry`s are now explicit hypotheses rather than claimed theorems.

**Proved:**

* `algebraicClosure_eq_bot_of_algHom` — regularity passes to subfields.
* `exists_two_notMem_of_index_two` — the parity count on a product-one generating triple.
* `nonempty_algEquiv_ratFunc_of_transcendental` — a field generated over `k` by one transcendental
  element is `RatFunc k`. Reusable; no such lemma exists in Mathlib (the repo's
  `RatFunc.exists_algEquiv_ratFunc` in `Hilbert/Analytic/Luroth.lean` only handles a generator
  that already lives inside `RatFunc k`).
* `transcendental_algebraMap_X` — the coordinate stays transcendental in any extension of `k(T)`.
* `nonempty_algEquiv_ratFunc_of_conic` / `nonempty_ringEquiv_ratFunc_of_conic` — **step 4 of the
  index-two argument, in full**: if `F = k(T)(y)` with `y² = c(T-a)(T-b)`, `a ≠ b`, `c ≠ 0`, then
  `F ≅ RatFunc k` over `k`, via `u = y/(T-a)`.
* `nonempty_algEquiv_rat_of_ringEquiv` — a ring isomorphism of characteristic-zero fields is a
  `ℚ`-algebra isomorphism. Needed to cross the `Algebra ℚ (RatFunc ℚ)` instance diamond
  (`DivisionRing.toRatAlgebra` vs `RatFunc.instAlgebraOfPolynomial`), which bites whenever an
  `AlgEquiv` over a general base field `k` is instantiated at `k = ℚ`.
* `BranchedRegularCover.finrank_sub` — `[L^H : ℚ(T)] = H.index`, by the Galois correspondence.
* `BranchedRegularCover.sub_algEquiv_ratFunc` — derived from `HasConicSubfield`.
* `BranchedRegularCover.isRegularGaloisGroupOverBase_sub` and the assembly
  `isRegularInverseGalois_of_conicSubfield`: given a three-point branched regular cover `c` and a
  subgroup `H` with `c.HasConicSubfield H`, the group `H` is a regular Galois group over `ℚ`.

**Taken as hypotheses, not proved:**

* the existence of the cover itself, `c : BranchedRegularCover A 3`, from a rigidity certificate
  with `cert.r = 3`;
* `BranchedRegularCover.HasConicSubfield c H`, the statement (now a `def : Prop`, formerly a
  claimed theorem `exists_conic_generator`) that `c.sub H = ℚ(T)(√(d (T - tᵢ)(T - tⱼ)))` for two
  of the three branch points and some `d ≠ 0`.

The second is exactly the *ramification* content of the argument: Kummer theory plus the
identification of the ramified places. The parity count that tells you *which* two branch points,
`exists_two_notMem_of_index_two`, is proved; what is missing is the passage from the structure's
`inertia_eq` / `inertia_bot` fields to the divisor of the radicand.

Because these are hypotheses of the theorem rather than axioms, nothing unproved is asserted, and
`#print axioms` on everything in the tree is still `[propext, Classical.choice, Quot.sound]`. The
price is that `isRegularInverseGalois_of_conicSubfield` cannot yet be *applied* to `PGL₂(𝔽₇)`: no
`BranchedRegularCover` has ever been constructed.

### Why `branchedRegularCover_of_certificate` is not a one-liner

A survey of the descent tower for this assessment found that **the existing chain destroys exactly
the data `BranchedRegularCover` asks for**, at three points:

1. `Descent/BranchCycles.lean:112` — `geomCompositum_exists_of_cover_unramified` returns
   `hcov : c.cover.IsUnramifiedOutside (Set.range t)`, and `geomCompositum_branchCycles_exists`
   throws it away. This is the loss point for the `inertia_bot` field.
2. `Descent/Tower.lean:942 geomTower_nonempty` — the passage
   `ClassInertiaPlaceData → CycloBranchData → GeomTower` drops `branch`, `place` and
   `gen_inertia`. Everything downstream (`Descent.lean` and the public
   `RigidityCertificate.isRegularInverseGalois`) is branch-blind. This is the loss point for
   `inertia_eq`.
3. `Descent/FieldTranslation.lean:59 descentTranslation` — its output is the bare `Prop`
   `IsRegularInverseGalois G`; the field `Ω^{ker ψ'}` and the isomorphism are existentially buried.

Consequently one cannot route through `branch_cycle_descent`; the construction has to be re-run
from `geomCompositum_exists_of_cover_unramified` and `classInertiaPlaceData_of_branchCycles`,
keeping the data. Two genuinely **new** lemmas are needed on top of that:

* **Geometric inertia surjects onto arithmetic inertia.** `Descent/GeomArithBridge.lean:160
  mem_inertia_bridge` goes geometric ⟶ arithmetic only. To turn `geomInertia = zpowers g` into
  `arithInertia = zpowers (…)` (rather than `⊇`), and to turn geometric unramifiedness into
  `arithInertia = ⊥`, the reverse direction is required and does not exist anywhere in the repo.
  A full grep confirms the only arithmetic-side `inertia = ⊥` in the tree is
  `Specialization.lean:334 inertia_trivial_of_separable`, whose hypothesis is separability of a
  specialization at an integer, not "outside the branch locus".
* **Inertia transport down to the fixed field.** `InertiaPlaceData`'s places live on the big tower
  `m.Ω`, whereas `BranchedRegularCover.L` must be the regular field `Ω^{ker ψ'}` produced by
  `RegularFixedField.lean`. Primes have to be contracted along `L ↪ m.Ω`; the repo's transport
  lemmas (`InertiaTransport.lean`, `GeomArithBridge.lean`) all go the other way.

Two smaller mismatches: `InertiaPlaceData` has no `Function.Injective branch` field and records
inertia only as a *membership* (`gen_inertia`), although the *generation* statement
`geomInertia L.M (Q i) = Subgroup.zpowers (g i)` is available and discarded at `Tower.lean:743`.
Branch points are freely choosable (`geomRET` takes any injective `t : Fin r → k`;
`classInertiaPlaceData_of_branchCycles` takes `branch` as an explicit argument), so
`branch i = i` is fine.

### Why `exists_conic_generator` is not a one-liner

Of steps 2–4 above, step 4 is now done. What remains:

* **Kummer**: a degree-`2` Galois extension in characteristic `0` is `ℚ(T)(√f)`. Standard (take
  `β = α - σα`), maybe 100 lines. `finrank_sub` supplies the degree.
* **Ramification ↔ odd valuation of `f`**: this is the substantial part. It has to connect the
  structure's `inertia_eq`/`inertia_bot` (stated for `ArithAKLB.arithInertia` of `L`) with the
  divisor of `f` in `ℚ[X]`, through the intermediate field `F`. There is no "inertia of a
  subextension" API on the arithmetic side.
* **The conic** — **done**: `nonempty_algEquiv_ratFunc_of_conic`, about 80 lines, resting on the
  new general `nonempty_algEquiv_ratFunc_of_transcendental`.

Alternatives considered and rejected: pulling back along a degree-`2` map (the same identification
problem reappears); genus / Riemann–Hurwitz (the repo's `Genus/` modules do not reach function
fields of conics); getting `deg f ≤ 2` without ramification data (impossible — `deg f ≤ 3` is all
that unramifiedness alone gives, and a degree-`3` `f` is an elliptic curve, generally not
rational).

### Effort estimate for Route 2

* `exists_conic_generator`: **1.5–3 weeks** (down from 2–4: the conic step is now proved, and
  `finrank_sub` is in place; what is left is Kummer plus the ramification bookkeeping, and the
  ramification bookkeeping was always the bulk of it).
* `branchedRegularCover_of_certificate`: **2–5 weeks**, most of it in the "geometric inertia
  surjects onto arithmetic inertia" lemma and in re-running the compositum construction while
  keeping the unramifiedness hypothesis.
* Then `PSL₂(𝔽₇)` needs one more concrete step: an explicit isomorphism between the index-two
  subgroup `ker(sign ∘ PGL2F7.subtype) ≤ Equiv.Perm (Fin 8)` and `PSL(2, ZMod 7)`. `PGL2F7` is
  built in `Examples/PGL27.lean` as a permutation group precisely to avoid `Nat.card` reasoning,
  so the identification is an explicit-generator computation in the style of
  `Mathieu/PSL211Simple.lean`: **3–7 days**.

Total: **2.5–7 focused weeks** for `PSL₂(𝔽₇)` (plus `M₂₂` essentially for free), against
"not this decade" for the Shih family.

---

## The overgroups that *are* realized: `PGL₂(𝔽ₚ)`

While `PSL₂(𝔽ₚ)` remains out of reach, the overgroup is not. `InverseGalois/Rigidity/Examples/`
now contains kernel-checked rational rigidity certificates for

| file | group | order | rigid triple | class sizes | check time |
|---|---|---|---|---|---|
| `PGL27.lean` | `PGL₂(𝔽₇)` | 336 | (2B, 6A, 7A) | 21, 56, 48 | fast |
| `PGL2F11.lean` | `PGL₂(𝔽₁₁)` | 1320 | (2A, 4A, 11A) | 66, 110, 120 | 36 s |
| `PGL2F13.lean` | `PGL₂(𝔽₁₃)` | 2184 | (2A, 4A, 13A) | 78, 182, 168 | 47 s |
| `PGL2F17.lean` | `PGL₂(𝔽₁₇)` | 4896 | (2B, 6A, 17A) | 136, 272, 288 | 89 s |
| `PGL2F19.lean` | `PGL₂(𝔽₁₉)` | 6840 | (2A, 4A, 19A) | 190, 342, 360 | 110 s |
| `PGL2F29.lean` | `PGL₂(𝔽₂₉)` | 24360 | (2A, 4A, 29A) | 406, 870, 840 | 375 s |
| `PGL2F31.lean` | `PGL₂(𝔽₃₁)` | 29760 | (2B, 6A, 31A) | 496, 992, 960 | 543 s |
| `PGL2F37.lean` | `PGL₂(𝔽₃₇)` | 50616 | (2A, 4A, 37A) | 666, 1406, 1368 | 1096 s |

Each gives `IsRegularInverseGalois ↥PGL` and `IsInverseGalois ↥PGL`, where `PGL` is the subgroup of
`Equiv.Perm (Fin (p+1))` generated by a Möbius involution and the translation `t ↦ t + 1`.

The shared toolkit is `InverseGalois/Rigidity/Examples/PermCode.lean`: permutations of
`Fin n` are encoded as base-`n` numerals (`enc`, `φ`), composition becomes a structurally recursive
digit computation (`step`, `mulC`) that the kernel evaluates on GMP-backed `Nat` arithmetic rather
than on `Finset.sum`, and the four certificate obligations — centerlessness, rationality of the
three classes, generation, and the product-one fibre bound — are reduced to `decide +kernel`
checks on lists of numerals (`certOf`). Adding a new prime is mechanical.

The last three files (`p = 29, 31, 37`) sit in their own `PGL2Large` lean_lib because they need
`--tstack=262144`, exactly as the `M₂₂` and `M₂₄` certificates do.

## Other routes surveyed (2026-08-21)

* **Belyi (1979)**, *On Galois extensions of a maximal cyclotomic field*, Izv. Akad. Nauk SSSR
  43:2, 267–276. Realizes Chevalley groups over the maximal cyclotomic field `ℚ^ab`, not over `ℚ`
  and not regularly over `ℚ(T)`. Does not help.
* **Malle–Matzat**, *Inverse Galois Theory*, 2nd ed. 2018. Chapter I is the rigidity method (which
  this repo already has in full); Chapter II is GAR realizations and embedding problems. Their
  `PSLₙ(p)` results need `n` odd with `gcd(n, p-1) = 1`, so they say nothing about `n = 2`. All 13
  non-abelian simple groups of order below `|PSL(2,25)|` are known over `ℚ`, but the constructions
  are case-by-case and mostly non-regular.
* **Malle–Saxl–Weigel**, *Generation of classical groups*, Geom. Dedicata 49 (1994), 85–116. Their
  rigidity results are about generation and rigidity, not *rational* rigidity; they do not supply a
  rational rigid triple for `PSL₂(q)`, and none exists: the two classes of elements of order `p`
  are interchanged by the exponents prime to `p`.
* **Mestre / Feit**: `PSL₂(p²)` is regular over `ℚ(T)` for `p ≢ ±1 (mod 5)`, via `p`-division
  points on the Jacobian of a genus-two curve. Even further out of formalization reach than Shih.
* **Explicit polynomial families.** Lamacchia (*Polynomials with Galois group PSL(2,7)*, Comm.
  Algebra 8 (1980)) gives a two-parameter degree-`7` family over `ℚ(a, A)` with group `PSL(2,7)`;
  the repo does have a criterion that consumes exactly this shape,
  `IsRegularInverseGalois.of_embeds_and_root`. But that criterion needs an *absolutely irreducible
  resolvent of degree `|G| = 168`* over the parameter field, together with an explicit root of it
  and an injection of the Galois group into `PSL(2,7)`. For `Sₙ` and `Aₙ` the repo gets those from
  a generic linear resolvent whose factorization is known in closed form; for `PSL(2,7)` there is
  no such closed form, and producing a degree-168 resolvent and proving it absolutely irreducible
  is not cheaper than the ramification work of Route 2. Isolated polynomials over `ℚ`
  (`x⁷ - 7x + 3`, Trinks–Matzat; `x⁷ - 154x + 99`, Erbach–Fischer–McKay) give `PSL(2,7)` over `ℚ`
  but say nothing about regularity over `ℚ(T)`.
* **`PSL(2,7) ≅ GL(3,2)` as a quotient of something already realized.** It is simple, so a quotient
  presentation would need it to be a quotient of a realized group, and the realized catalogue
  (`Sₙ`, `Aₙ`, abelian, dihedral, Möbius, coprime products, `PGL₂(𝔽ₚ)`) contains no group with
  `PSL(2,7)` as a quotient other than `PSL(2,7)` itself. `PSL(2,7) ≤ A₇` is a *subgroup*, index 15,
  which is the same index-descent problem as Route 2 but harder (no conic).

Conclusion: **Route 2 remains the cheapest**, and the estimate below stands.

## Recommendation

1. Do Route 2. It is the only realistic path to any `PSL₂(𝔽ₚ)` in this repo, and it pays for
   `M₂₂` at the same time.
2. Attack the `HasConicSubfield` hypothesis first: it needs no new tower plumbing, only field
   theory, and it is the half that generalizes (any `r = 3` certificate with an index-two
   subgroup). Its conic step and its degree computation are already done.
3. Then construct a `BranchedRegularCover` from a certificate, and only then is `PSL₂(𝔽₇)` in
   reach — with one further concrete step, an explicit isomorphism between the index-two subgroup
   of `Rigidity.PGL27.PGL ≤ Equiv.Perm (Fin 8)` and Mathlib's `PSL(2, ZMod 7)`.
4. Restate Shih's modular input correctly (see the inconsistency above) before any further work on
   Route 1, and revisit it only if Mathlib acquires curves and Riemann–Roch.
