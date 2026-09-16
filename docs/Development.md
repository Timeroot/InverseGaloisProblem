# Development notes

A record of what was built, in what order, and — mostly — of the choices that are not the obvious
ones. The mathematics itself is documented in the module docstrings; `InverseGalois/Catalogue.lean`
is the index of everything realized. This file is for the things a reader cannot recover from the
code: which version of a classical theorem was formalized, which plausible routes were tried and
abandoned, and why the build is shaped the way it is.

## The three layers

The repository grew in three layers, and they are still visible in the directory structure.

1. **Elementary realizations.** Cyclic and abelian groups inside cyclotomic fields; `Sₙ` by
   Hilbert irreducibility; a handful of named small groups (`S₃`, `A₄`, `A₅`, `V₄`, `D₄`, `D₅`)
   proved by exhibiting one polynomial and pinning its Galois group by hand. `Core/`, `Groups/`,
   `Polynomial/`, `Resolvent/`, `Reflection/`. This layer is now subsumed: every group in it is
   realized, regularly, by the machinery of layer 2. It is kept because the individual witnesses
   are the only place the repository computes with an explicit polynomial.

2. **Geometry: the Riemann Existence Theorem and the rigidity method.** `Rigidity/`, 524 files,
   the largest single construction. The output is `IsRegularInverseGalois G`: a regular Galois
   extension of `ℚ(T)` with group `G`. Everything here is unconditional — the geometric input was
   proved, not assumed.

3. **Arithmetic: class field theory and Shafarevich's theorem.** `CFT/` (1148 files) and
   `Solvable/` (169). The output is `IsInverseGalois G` over `ℚ`, for every finite solvable `G`.

Layers 2 and 3 do not meet: the regular inverse Galois problem for solvable groups is open, and
the arithmetic proof produces extensions of `ℚ`, not of `ℚ(T)`.

## Which Riemann Existence Theorem

This is the most consequential design decision in the repository, because RET is the one classical
input that could plausibly have been assumed.

**It was not assumed.** `Rigidity.RET.geomRET` (`Rigidity/RET/Completeness.lean`) is a theorem, and
the realization theorems that rest on it depend only on `propext`, `Classical.choice` and
`Quot.sound`.

The statement formalized is the *covers* form over `ℚ̄`, not the full three-way equivalence of
categories. Mathlib has no category of field extensions and no Riemann surfaces, so the classical
statement

> for `X` a compact Riemann surface and `S ⊆ X` finite, the finite branched covers of `X`
> unramified outside `S`, the finite covering spaces of `X ∖ S`, and the finite extensions of
> `ℳ(X)` unramified outside `S` are equivalent

is specialized to `X = ℙ¹` and then flattened into two implications between concrete objects
(`Rigidity/RET/GeomRET.lean`):

* **existence** — a generating product-one tuple in a finite group is the branch-cycle description
  of an actual Galois cover of the line over `ℚ̄` with the prescribed branch locus;
* **completeness** — an arbitrary cover with a prescribed branch locus has branch cycles.

The two are stated and proved separately, which is not decoration: the rigidity method consumes
*both*, and neither follows from the other. Existence realizes the group over `ℚ̄(T)`; completeness
is what the descent to `ℚ(T)` needs, because the Galois closure of the cover existence produced is
a different, bigger cover whose branch cycles must be produced before any arithmetic can start.
Completeness came first and is the easier half: reading branch cycles off a cover only needs the
cover analytified, and `RET/Analytic/` does that from the defining equation.

Three non-obvious things about the existence proof:

* **The product-one relation is spent on deleting a point.** Rather than working with the sphere
  group `Γ_r = ⟨x₁,…,x_r ∣ x₁⋯x_r = 1⟩`, the construction inverts the coordinate about one branch
  point, sending it to infinity. The remaining `r-1` points are punctures of a plane, whose `π₁` is
  *free*, and the truncated tuple satisfies no relation — its missing entry was the inverse of the
  product of the others. So the whole of RET's existence half is run on a free group, and the
  sphere relation is never carried through the construction (`RET/CoverExistence.lean`).
* **The analytic teeth are Hörmander's `L²` estimate, not GAGA.** The step that cannot be done
  algebraically is producing enough meromorphic functions on the covering surface to write it as an
  algebraic curve. Grauert–Remmert is unavailable, so the repository proves the needed instance of
  it directly: `RET/Analytic/Dbar/` solves `∂̄u = f` with an `L²` bound on the covering surface, and
  `hasEnoughFunctions` follows. Along the way the wall was shown to be *equivalent* to "every
  covering of a punctured plane is algebraic" (damping plus Riemann removable singularities), which
  is what made it clear the `∂̄` route was the right one and not an overshoot.
* **The descent from `ℂ` to `ℚ̄` is by specialization of an equation, not by a comparison
  theorem.** `RET/Transfer/` packages a cover as a `CoverDatum`: a finite list of polynomial
  identities and non-vanishing conditions. That is a first-order statement about the coefficients,
  so once the branch points already lie in `ℚ̄` the datum descends from `ℂ` to `ℚ̄` by a
  Nullstellensatz argument. No model theory, no rigid analytic geometry, no étale comparison.

Underneath all of this, the topological `π₁` had to be built from scratch: `RET/Pi1/Topological/`
proves `π₁` of the `r`-punctured plane is free on the puncture loops, with Seifert–van Kampen
(`isPushout`, a groupoid pushout) proved along the way because Mathlib does not have it.

There is also a full étale-`π₁` development (`RET/Pi1/Etale/`): the category of finite étale
algebras over a field is a Galois category, its fibre functor is checked on all six axioms, and the
absolute Galois group is identified with `Aut` of the fibre functor. It is self-contained and
sorry-free, and it is *not* what the main theorems use — the elementary route above turned out
cheaper. It is kept because it is the correct general framework and the next group of theorems will
want it.

## The rigidity method

`Rigidity.RigidityCertificate` (`Rigidity/Certificate.lean`) is the interface: a finite centerless
group, three rational conjugacy classes, and a certified count. The criterion used is the *fibre*
form rather than the character-theoretic one — for a fixed `z` in the third class, the set
`{x ∈ C₁ : x⁻¹z⁻¹ ∈ C₂}` has exactly `|C_G(z)|` elements and each generates `G` with `z`. This is
equivalent to `N(C) = |G|` plus generation, but it is *decidable by the kernel* on a concrete
permutation group, whereas structure constants would require the character table.

**Nothing in the rigidity layer uses `native_decide`.** All certificate computations are kernel
`decide`. Making that affordable required `Rigidity.PermCode`: permutations of `ℙ¹(𝔽ₚ)` encoded as
base-`(p+1)` numerals, so the kernel manipulates one big numeral rather than a `Finset` of
functions. The rule that kept this tractable is "never let a big literal reach `whnf`".

Realized this way: `Sₙ` for `n ≥ 3`, `PGL₂(𝔽ₚ)` for `p = 7, 11, 13, 17, 19`, and (in separate build
targets, see below) `M₁₁`, `M₁₂`, `M₂₄`, `Aut(M₂₂)`, and `PGL₂(𝔽ₚ)`/`PSL₂(𝔽ₚ)` for larger `p`.

**Beyond `ℚ`: orbit rigidity.** No Mathieu group has a *rationally* rigid triple, and `M₂₂` and
`M₂₃` have no rigid triple at all, so the classical method stops. What does work is weakening
rationality: if every cyclotomic twist of the class tuple is again rigid, the branch-cycle argument
runs over the subgroup of the arithmetic fundamental group fixing the tuple, and realizes the group
regularly over the number field that subgroup cuts out
(`Rigidity.RET.Descent.exists_regular_numberField_of_orbitRigid`). This is what reaches `M₁₁`,
`M₁₂`, `M₂₄`, and `PSL₂(𝔽ₚ)` for every `p ≤ 37` — including `p = 23`, which the rational route
provably cannot reach.

**Shih's theorem was surveyed and rejected.** Shih's modular construction reaches `PSL₂(𝔽ₚ)` over
`ℚ(T)` for a density-`7/8` set of primes, but its inputs — moduli of elliptic curves, the Weil
pairing, Atkin–Lehner involutions, Shimura reciprocity — are essentially all absent from Mathlib;
the honest estimate was a multi-year programme gated on a large Mathlib effort. Only its arithmetic
half survives, as `Rigidity.Shih.shihPrime_iff`. The cheaper alternative, index-two descent from
`PGL₂(𝔽ₚ)` (`RET/Descent/Index2.lean`, the conic through two of the three branch points), is proved
but currently realizes nothing, because nothing yet constructs the `BranchedRegularCover` it
consumes. One earlier casualty is worth recording: a lemma named `AtkinLehner` in an early draft of
the Shih route was not merely unproved, it was *inconsistent as stated*, and was deleted.

## Hilbert irreducibility

The route is the elementary Dörge–Bauer counting proof (1927), not the `p`-adic or the
Néron-specialization one: for an irreducible `f ∈ ℚ[T,X]` of degree `d` in `X`, each degree split
of a factorization contributes `O(N^{1-1/d})` bad specializations in `[-N, N]`, which is `o(N)`.
The estimates are real analysis on Puiseux expansions (`Hilbert/Analytic/`), and that subdirectory
is most of the 43 files. The alternative — "a finite extension of a Hilbertian field is Hilbertian"
— was assessed and is a much larger theorem; the counting proof was ported directly instead.

## Shafarevich's theorem

The hardest single result, and the one where the most routes died. The shape of the finished proof:

**Group theory first, until nothing is left.** Ore's supplement theorem exhibits a nontrivial
finite solvable group as a quotient of `N ⋊ U` with `N` nilpotent and `U` a proper subgroup, so
induction on the order applies; the Sylow splitting turns the nilpotent kernel into kernels of
prime power order. The result, `Shafarevich.isSolvable_isInverseGalois_of_splitPrimePowerEP`,
reduces the entire theorem to one arithmetic statement: *every split embedding problem over `ℚ`
with a kernel of prime power order is solvable*. No group theory survives past that point.

**Class field theory, built rather than assumed.** Mathlib has no class field theory, so `CFT/` is
the bulk of the repository. The parts worth flagging:

* The fundamental class is reached *without* reciprocity, by the cyclotomic-auxiliary route; the
  local invariant `inv_K : Br(K) → ℚ/ℤ` is built from the canonicity of the unramified Frobenius
  and `f = n`. Reciprocity over a number field is then derived (`baseArtinEquiv`), and the power
  residue symbol is treated as a carry cocycle.
* Tate–Nakayama is proved with no hypothesis at all for coefficients flat over `ℤ`, and separately
  for `p`-torsion coefficients with an explicit count replacing Tate's hypotheses. The reason it
  cannot be made unconditional in the form wanted is recorded in the module.
* Poitou–Tate global duality is developed only as far as the ladder consumes it: the everywhere
  locally trivial classes in degree two, made natural in the coefficients so that a single class of
  complete cohomology governs every shrink.
* Grunwald–Wang is proved for squarefree exponent, and Ikeda's theorem for split embedding problems
  with abelian kernel over a field containing the roots of unity.

**The ladder.** The `p`-central series of the kernel turns a split prime-power problem into a
ladder whose every rung is a one-layer embedding problem over a "group of letters". Each rung needs
an algebraic number with prescribed local behaviour — Schmidt–Wingberg's theorem 13 — and the rung
is bought by a diagonal of units subject to local conditions at places chosen to confine the
obstruction, plus a sharp prescription one field up.

**The prime 2, and why the obvious fix is impossible.** At `ℓ = 2` the parity obstruction is real:
the local symbol is the Hilbert symbol, so the product formula makes vanishing of the obstruction
*necessary*, and no stage-dependent recursion can move it. Several attempts to argue around it
failed for exactly this reason. What worked was rebuilding the odd argument so that parity never
arises: the correction handed to the kernel prescription at a named place is trivial on inertia, so
the classes it names are unramified, so they lie on one line automatically and nothing ramified
need be prescribed anywhere. The archimedean places are *named* rather than solved at. The odd
hypothesis then vanished from the entire chain rather than being discharged — `hasPrescribedUnits`
dropped its line datum along with its oddness, and the de-odding cascaded all the way up.

**Hypotheses that turned out to be false.** The working method throughout was to state an unproved
gap as a named `Prop`-valued definition, never an axiom, precisely so that it could be *tested*.
That paid for itself: `HasIdeleClassNakayamaSpan`, `FixedReachableEP`, `ConfinedObstructionEP`,
`TwistedNormEP`, `InvariantRadicandsEP`, the first form of `HasLocalLift`, the fixed-level
prescription, the ramification clause of `HasKernelPrescription` and the invariance clause of the
flat prescription were each written down as plausible-looking hypotheses and each turned out to be
*false as stated*. Had any of them been an axiom the development would have been silently
inconsistent. Also refuted, in the endgame: the rank-one ansatz, the trace ansatz and the twisted
norm. What survives is the invariant divisor with two shrinkings.

One pleasant surprise at the end: Poitou–Tate is not needed at the flat step. The allowed places
are free, so the obstruction has fixed coefficients and the residue is bought by finiteness of the
class group.

## Discipline

* **No axioms, ever.** `sorry` is the only acceptable marker of an unfinished proof, and there are
  none in the default build. An unproved mathematical input is a named `Prop`-valued definition
  carried as a hypothesis, so that it is visible in the statement of every theorem depending on it.
* **`native_decide` is not used** in `Rigidity/`, `CFT/` or `Solvable/`. It survives only in the
  legacy quintic/`D₅` material (`Reflection/PolyReflect*`, `Groups/S4`, `Groups/D4`,
  `Groups/D5GroupFacts`, `Resolvent/PentagonalSum*`, `QuinticGroupTheory`) and in parts of the
  vendored `Mathieu` library. Those are the only places `Lean.ofReduceBool` and
  `Lean.trustCompiler` appear in the axiom list of anything.
* Docstrings state mathematics, not proof status.

## Build engineering

* **`Mathieu` is a vendored `lean_lib`,** kept out of `InverseGalois`'s import graph so the
  catalogue does not depend on it. One file, `M11CosetAction.lean`, is deliberately outside the
  library's closure: its `decide` call is unaffordable and nothing needs it.
* **`MathieuRigidity`, `MathieuRigidityM22`, `MathieuRigidityM24`, `PGL2Large`, `PSL2Large`** exist
  as separate targets for one reason: they need `moreLeanArgs = ["--tstack=262144"]`. The
  certificates in them are ordinary rigidity certificates; only the elaborator's stack depth
  differs.
* **`extras/comparator/`** is deliberately *not* a default target: `Challenge.lean` carries a
  `sorry` by design (it is a benchmark statement), and `Solution.lean` closes it.
* **Instance search can dominate the build.** `RET/Product.lean` once took 82 minutes; a two-line
  shortcut instance for `RatFunc` brought a related file from 4916 s to 100 s. When a Lean file in
  this repository is mysteriously slow, the first thing to check is a pathological instance search
  through `RatFunc`, not the proofs.
* `PolyReflect` (`Reflection/`) is a self-contained reflective normal-form evaluator for
  multivariate polynomial identities, written for the degree-20 resolvent identities of the `D₅`
  proof, which took about an hour each with `ring`. With a linear-merge normal form, a length-aware
  multiplication and Gröbner cofactors stored as parsed string literals, the same identity compiles
  in about 18 seconds. It is the one place in the repository that trades kernel trust for speed.
