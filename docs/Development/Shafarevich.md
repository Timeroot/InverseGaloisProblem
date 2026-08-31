# Solvable groups over ℚ: a literature and feasibility study

**Target.** Shafarevich's theorem: *every finite solvable group is a Galois group over ℚ*.

**Purpose.** Decide what part of the classical route is formalizable in Lean/Mathlib given what
this repository already has (regular realizations of every finite abelian group over ℚ(T), Sₙ, Aₙ,
dihedral, rigidity for many simple groups, Hilbert irreducibility with integer specializations,
closure of realizability under quotients and coprime products), and what part is out of reach
because it rests on class field theory.

**Executive summary.**

* The *full* Scholz–Reichardt theorem, as written by Serre, needs **class field theory twice**
  (Brauer–Hasse–Noether, and Kronecker–Weber/local CFT to glue local characters) and
  **Chebotarev once**. Neither is in Mathlib and both are multi-year projects.
* But the Chebotarev use compresses to a *strictly weaker* statement than Dirichlet's theorem,
  and Mathlib already has its analytic core (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`).
* The genuinely reachable target is **not** Scholz–Reichardt but **Ikeda's theorem** and the
  class of **semiabelian groups**, which is CFT-free, Chebotarev-free, and whose two inputs
  (regular abelian realizations over a base field, and Hilbert irreducibility) are *exactly* the
  two things this repository already owns. That is the recommendation.

---

## 0. Status (2026-08-21) — what has since been formalized

This section is later than the rest of the document and supersedes it where they disagree. The
study below rated Shafarevich "do not start"; that verdict was about the *arithmetic*, and it
still stands. But the split was drawn in the wrong place. The **group-theoretic half is not
expensive at all**, and it is now done — sorry-free and axiom-free.

**Landed in `InverseGalois/Solvable/Shafarevich/`:**

| file | content |
|---|---|
| `Frattini.lean` | `exists_nilpotent_normal_supplement` — Ore's supplement theorem |
| `SemidirectAssoc.lean` | `SemidirectProduct.prodAssoc : (A × B) ⋊ U ≃* A ⋊ (B ⋊ U)` |
| `Reduction.lean` | `SplitNilpotentEP`, and Ore's induction on the order |
| `PrimePower.lean` | `splitNilpotentEP_of_splitPrimePowerEP` — Sylow splitting of the kernel |
| `Main.lean` | the capstones |
| `SplitAbelian.lean` | the unconditional abelian case |

The headline is

```lean
theorem Shafarevich.isSolvable_isInverseGalois_of_splitPrimePowerEP
    (hEP : SplitPrimePowerEP) (G : Type) [Group G] [Finite G] [IsSolvable G] :
    IsInverseGalois G
```

**Shafarevich's theorem now follows from one statement**, `SplitPrimePowerEP`: *if a finite group
`U` is a Galois group over `ℚ` and `H` is a finite `p`-group with a `U`-action, then `H ⋊[φ] U` is
a Galois group over `ℚ`.* No group theory is left.

The whole reduction is carried out for an **abstract realization predicate** `P : ∀ (G : Type)
[Group G], Prop`, the only structural input being `Shafarevich.IsQuotientClosed P` (transport along
a surjection) together with the trivial group. So it specializes for free to the regular predicate
over `ℚ(T)`: `isSolvable_isRegularInverseGalois_of_splitPrimePowerEP` is the same theorem with
`IsRegularInverseGalois` throughout. That statement is of course still conditional, and on a
hypothesis that is *not* known — see "A warning about the regular route" below: regular
realizability of an arbitrary ℓ-group over `ℚ(T)` is an open problem, so there is no theorem there
to discharge it with. It is recorded because the reduction genuinely is predicate-independent.

Two remarks on how this differs from the plan in §5:

* **The Fitting subgroup is not needed, and is absent from Mathlib for groups.** Ore's theorem is
  proved instead through `frattini` plus a Gaschütz argument (two Frattini arguments via
  `Sylow.normalizer_sup_eq_top`, then `frattini_nongenerating`). The Gaschütz step is stated
  quotient-free as `⁅N,N⁆ ≤ frattini G ∧ frattini G ≤ N ⇒ Group.IsNilpotent N`, which avoids
  `↥N ⧸ …` entirely.
* **The abelian and nilpotent cases do not meet.** `SplitAbelian.lean` records that a split
  embedding problem with *abelian* kernel is already unconditional here, via the Dentzer–Stoll
  wreath construction. It does not bootstrap: filtering a `p`-group kernel by its centre turns one
  split problem into a split problem with abelian kernel **plus a residual lifting that is no
  longer split**, and that lifting is exactly where class field theory is unavoidable. This is the
  structural reason Ikeda/wreath reaches precisely the semiabelian groups and stops.

**Arithmetic bricks landed alongside:**

* **Milestone 7 is done.** `InverseGalois/NumberTheory/SplitCompletely.lean` proves Schur's theorem
  on prime divisors of polynomial values (`infinite_setOf_prime_dvd_eval`) and deduces Serre's
  Lemma 2.1.4, `infinite_setOf_prime_splitsCompletely`: for `K/ℚ` Galois, infinitely many rational
  primes split completely in `K`. Elementary — no density theory, no L-functions, no Chebotarev.
  Note that Mathlib has **no** "splits completely" predicate, so `SplitsCompletely` is defined here
  as "every prime above `p` has ramification index and inertia degree one".
* **Milestone 6 is done, in full and unconditionally.** Three files:
  * `IdealNormCount.lean` proves `n ↦ #{I ⊴ 𝒪_K : absNorm I = n}` multiplicative and derives the
    **Euler product for `NumberField.dedekindZeta`** indexed by the rational primes — which Mathlib
    does not have. The proof uses no unique factorization of ideals, only `absNorm I ∈ I` together
    with Bézout comaximality.
  * `IdealEulerProduct.lean` gives the Euler product in its intrinsic form,
    `dedekindZeta_eulerProduct_primeIdeal : ∏' 𝔭, (1 - N𝔭^{-s})⁻¹ = ζ_K(s)` for `re s > 1`. There is
    no Euler product for a Dedekind domain anywhere in Mathlib — everything under
    `Mathlib/NumberTheory/EulerProduct/` is ℕ-indexed — so this is built from scratch, mirroring
    the structure of `EulerProduct/Basic.lean`.
  * `SplitDensity.lean` defines `HasDirichletDensity` (Mathlib has no notion of prime density at
    all) and proves `hasDirichletDensity_splitSet`: **the primes splitting completely in a Galois
    number field of degree `n` have Dirichlet density `1/n`.** Hence the payoff, **statement (★) of
    §1.5**, unconditionally:

    ```lean
    theorem infinite_setOf_splitsCompletely_not_splitsCompletely
        (A B : Type*) [Field A] [NumberField A] [IsGalois ℚ A]
        [Field B] [NumberField B] [IsGalois ℚ B]
        (hlt : Module.finrank ℚ A < Module.finrank ℚ B) :
        {p : ℕ | p.Prime ∧ SplitsCompletely A p ∧ ¬ SplitsCompletely B p}.Infinite
    ```

    This is the **only** consequence of Chebotarev's theorem that Scholz–Reichardt actually needs,
    so the whole of class **(c)** in the §1.4 classification is now discharged. Note the hypotheses
    differ slightly from (★) as stated in §1.5: no containment `A ⊆ B` and no index condition are
    required, a degree inequality suffices, but **both** fields must be Galois over `ℚ`, not just
    `B`. In the Scholz–Reichardt application that is free — the field `A` there is a compositum of
    Galois extensions of `ℚ`. Two side-products worth
    noting: `finite_ramifiedSet` (only finitely many rational primes ramify) had to be proved here,
    since Mathlib has no "ramified ⇒ divides discriminant"; and `log ζ_K` is built as
    `∑' 𝔭, -log(1 - N𝔭^{-s})` directly rather than by taking a logarithm of the product.

---

## 0.1 Status (2026-08-21, later the same day) — the class field theory layer

Milestone 9 has since been done. **Mathlib contains no class field theory at all** — no Chebotarev
in general, no Grunwald–Wang, no Kronecker–Weber, no Hasse norm theorem, no Artin map, no ray class
groups, no ideles, no local class field theory, no Tate cohomology, no cup products, no Herbrand
quotients, no Hochschild–Serre, no `K^ur`, no Krasner's lemma, no crossed products, no relative
Brauer group, no local invariant `inv_v : Br(K_v) → ℚ/ℤ`. `Mathlib/Algebra/BrauerGroup/Defs.lean`
carries the Brauer *monoid* of central simple algebras; the group law, Galois descent, and the
uniqueness half of Wedderburn's theorem were all absent (Wedderburn uniqueness is still an explicit
Mathlib TODO, and `L ⊗[K] L ≃ (Gal(L/K) → L)` does not exist there either). The class
`IsNonarchimedeanLocalField` (`Mathlib/NumberTheory/LocalField/Basic.lean`) exists but has **zero
instances**: not even `ℚ_[p]` is one.

So the whole layer had to be built. It lives in `InverseGalois/CFT/`, is indexed by
`InverseGalois/CFT.lean`, and is sorry-free and axiom-free throughout (`#print axioms` gives
`[propext, Classical.choice, Quot.sound]` on every capstone).

| group | content |
|---|---|
| `CFT/GaloisDescent.lean` | Galois descent for modules, absent from Mathlib |
| `CFT/GroupCohomology/*` | cocycle ↔ `H²` dictionary, corestriction and the `[G : S] • id` relation, killing by the order of the group, normal form for cocycles of a cyclic group, `H²(cyclic) = invariants / norms` |
| `CFT/Brauer/CrossedProduct*.lean` | the crossed product `⨁_σ L·u_σ`: central simple, split by `L`, multiplicative in the cocycle, trivial exactly for a coboundary |
| `CFT/Brauer/Centralizer.lean`, `Split.lean`, `SkolemNoether.lean`, `Division.lean` | the double centralizer theorem, Skolem–Noether, Wedderburn's theorem in the split case, the division representative |
| `CFT/Brauer/SplittingSubfield.lean`, `CrossedProductRecognition.lean`, `H2Surjective.lean` | **`Br(L/K) ≅ H²(Gal(L/K), Lˣ)`** for every finite Galois `L/K`, and hence `Br(L/K)` is killed by `[L : K]` |
| `CFT/Brauer/CyclicBrauer.lean`, `CyclicNorm.lean` | for `L/K` cyclic, **`Br(L/K) ≅ Kˣ / N_{L/K}(Lˣ)`** |
| `CFT/Brauer/MaximalSubfield.lean` | maximal commutative subalgebras; every Brauer class is split by a finite subextension of the algebraic closure |
| `CFT/Brauer/Quaternion.lean`, `RealPlace.lean` | `-1` is not a norm from `ℂ` or from `ℚ(i)`, so `Br(ℂ/ℝ)` and `Br(ℚ(i)/ℚ)` are nontrivial; **`Br(ℂ/ℝ) ≅ ℤ/2`** |

This is the classical Brauer-group half of local class field theory, over an arbitrary field. What
it does **not** contain, and what item 2 of the §1.4 table needs, is the *arithmetic* input:
the local invariant maps and the exactness of
`0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0` (Albert–Brauer–Hasse–Noether). Those need the local theory —
unramified extensions of a local field, the valuation-theoretic computation
`Br(K^ur/K) ≅ ℚ/ℤ`, and then global reciprocity — none of which is reachable from here, and the
first of which cannot even be stated until `ℚ_[p]` is made an instance of the local-field class.

## 0.2 Status (2026-08-21) — the reduction, sharpened twice more

`SplitPrimePowerEP` is no longer the frontier. Two further purely group-theoretic reductions have
landed:

* `Shafarevich/AbelianKernel.lean` peels the centre off a `p`-group kernel one layer at a time. The
  centre is characteristic, so the quotient carries an induced action and the projection
  `H ⋊[φ] U → (H/Z) ⋊[φ'] U` has commutative kernel; induction on the order gives
  `splitPrimePowerEP_of_abelianKernelEP`. The hypothesis is now about embedding problems that are
  no longer split, but whose kernel is **abelian**:
  ```lean
  def AbelianKernelEP : Prop :=
    ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (π : E →* W),
      Function.Surjective π → IsMulCommutative π.ker → IsInverseGalois W → IsInverseGalois E
  ```
* `Shafarevich/MinimalKernel.lean` filters that abelian kernel further, down to a **minimal
  elementary abelian** one.

Both reductions are again carried out for an abstract quotient-closed predicate, so the regular
analogues over `ℚ(T)` come for free.

**Revised verdict.** Milestone 9 is done. Milestones 8, 10 and 11 — Kronecker–Weber,
Scholz–Reichardt, Shafarevich's arithmetic core — remain out of reach, for exactly the reasons
given in §4.1, and the two blockers are precisely rows 2 and 5 of the §1.4 table:
Albert–Brauer–Hasse–Noether, and the gluing of local abelian characters (which over `ℚ` *is*
Kronecker–Weber). Everything else on the route is now either done or elementary. What has changed
is that the non-arithmetic scaffolding is no longer a cost, that the crossed-product side of the
Brauer group is available in full, and that the target is a single, precisely stated,
self-contained proposition about embedding problems with minimal elementary abelian kernel.

## 0.3 Status (2026-08-22) — the degree-two slice of the arithmetic is done

§0.1 named the missing arithmetic input as "the local invariant maps and the exactness of
`0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0`". **In degree two, over `ℚ`, that is now proved**, by an
argument that goes around the invariant maps entirely rather than through them: in exponent two the
whole sequence degenerates into a statement about ternary quadratic forms, and Legendre's descent
proves it directly.

| statement | file |
|---|---|
| the local Hilbert symbol at every place of `ℚ`, bimultiplicative, computed explicitly | `CFT/Local/*` |
| **Hilbert reciprocity** `∏_v (a, b)_v = 1` | `CFT/Global/Reciprocity.lean` |
| **Hasse–Minkowski for ternary forms over `ℚ`** | `CFT/Global/HasseMinkowski.lean` |
| **the Hasse norm theorem for `ℚ(√b)/ℚ`** = ABHN for quaternion algebras over `ℚ` | `CFT/Global/HasseNorm.lean` |
| **Hasse–Minkowski for diagonal forms in any number of variables** | `CFT/Global/DiagHasse.lean` |
| the same, freed of the invertibility hypothesis, and as a principle for **representing** a rational number | `CFT/Global/DiagRepr.lean` |
| a diagonal form in ≥ 5 variables is isotropic at every **odd** place, so only `ℝ` and `ℚ₂` matter | `CFT/Global/OddQuinary.lean` |
| the real place by inspection, and the resulting two-condition criterion in ≥ 5 variables | `CFT/Global/RealSigns.lean` |
| **Hasse–Minkowski for an arbitrary (non-diagonal) rational form**, via congruence to a diagonal one | `CFT/Global/MatHasse.lean` |
| a diagonal form in five dyadic **units** is isotropic, hence the ≥ 5-variable criterion for **odd integer** coefficients is the sign condition alone | `CFT/Local/DyadicQuinary.lean` |
| nondegeneracy of the **dyadic** Hilbert symbol: `[ℚ_2^× : N(L^×)] = 2` and `Br(L/ℚ_2) ≅ ℤ/2` | `CFT/Local/DyadicNondegenerate.lean` |
| **`IsNonarchimedeanLocalField ℚ_[p]`**, with `𝒪[ℚ_[p]] ≃+* ℤ_[p]` compact, complete, discrete, finite residue field | `CFT/Local/PadicLocalField.lean` |
| a diagonal dyadic form with three unit coefficients and one of valuation one is isotropic | `CFT/Local/DyadicQuaternary.lean` |
| isotropy is invariant under rescaling coefficients by squares or by a common scalar; dyadic square-class normalisation | `CFT/Global/DiagScale.lean` |
| **`u(ℚ₂) ≤ 4`**: every diagonal form over `ℚ₂` in ≥ 5 variables is isotropic | `CFT/Global/Meyer.lean` |
| **Meyer's theorem**: a diagonal rational form in ≥ 5 variables is isotropic iff it is indefinite, and then represents everything the real place allows | `CFT/Global/Meyer.lean` |
| `u(ℚ_p) ≤ 4` at **every** finite place, and Meyer's theorem for an arbitrary symmetric rational matrix: rational zero iff real zero | `CFT/Global/Meyer.lean` |
| every `p`-adic form in ≥ 5 variables, diagonal or not, is isotropic, and a diagonal one with nonvanishing coefficients is **universal** | `CFT/Global/Meyer.lean` |
| **`u(ℚ₂) = 4` exactly**: the sum of four squares is anisotropic over `ℚ₂`, so five variables are genuinely needed | `CFT/Local/DyadicAnisotropic.lean` |
| **`u(ℚ_p) = 4` exactly, at every finite place**: at an odd place the unramified norm form plus its multiple by the uniformiser is anisotropic | `CFT/Local/OddAnisotropic.lean` |
| the five-variable hypothesis in Meyer's theorem is **sharp**: `⟨1, -5, -2, 10⟩` is isotropic over `ℝ` but anisotropic over `ℚ` | `CFT/Local/DyadicNormFive.lean` |

All sorry-free and axiom-free. See `docs/Development/ClassFieldTheory.md` for the full map of the
layer, the proof architecture of the descent, and why it is not circular with reciprocity.

**This does not move the Shafarevich frontier.** Scholz–Reichardt needs ABHN for **odd** `ℓ`, and
nothing in the ternary-forms argument survives the passage from exponent `2` to exponent `ℓ`: the
whole point of the degree-two case is that a Brauer class of order two is a conic, which has no
analogue. Rows 2 and 5 of the §1.4 table — ABHN in general, and the gluing of local abelian
characters — remain exactly as stated in §0.2. What has changed is that the *degree-two* theory is
complete and usable. The target named here a day earlier — Serre's existence theorem for Hilbert
symbols, i.e. exponent-two Grunwald–Wang, and thence Hasse–Minkowski in `n` variables — has since
been reached: the general-`n` Hasse principle is proved by induction on the number of variables
with the quinary argument as the inductive step, and the odd-place computation then shows that
from five variables on only the real and the dyadic place carry information. The diagonalisation
step is supplied too — every symmetric matrix over a field in which `2` is invertible is congruent
to a diagonal one, and congruence preserves isotropy and commutes with base change — so Serre's
chapter on Hasse–Minkowski is complete for an arbitrary rational quadratic form, not only for a
diagonal one. What is *not* reachable from any of this is the `u`
-invariant of `ℚ₂`, whose proof runs through the classification of `2`-adic forms by their Hasse
invariant. **That gap has since been closed, by a different route.** Rather than classify `2`-adic
forms, normalise the five coefficients to units or twice units by square classes: if all five are
of one kind the quinary unit form settles it, after dividing the whole form by two in the second
case; otherwise, among five booleans not all equal, three agree and a fourth differs, so a
four-variable subform has three coefficients of one kind and one of the other, and that quaternary
form is isotropic by a second modulo-eight search. Hence `u(ℚ₂) ≤ 4`, and with the odd places and
the real place, **Meyer's theorem**: a diagonal rational form in at least five variables is
isotropic exactly when it is indefinite. So the `u`-invariant statement and Meyer's theorem, both
named unreachable a few hours earlier, are proved. The bound is sharp: the sum of four squares is
anisotropic over `ℚ₂` by the same modulo-eight congruence, so `u(ℚ₂) = 4` exactly. At an odd place the
obstruction is a valuation instead of a congruence — the norm form of the unramified quadratic
extension takes only values of even valuation, so adjoining its multiple by the uniformiser gives
an anisotropic quaternary form — and hence `u(ℚ_p) = 4` at **every** finite place.

One remark of §0.1 is now obsolete. It said that the local invariant maps "cannot even be stated
until `ℚ_[p]` is made an instance of the local-field class"; `CFT/Local/PadicLocalField.lean`
supplies that instance — the first anywhere, Mathlib's `IsNonarchimedeanLocalField` having had
none — so the statements of local class field theory are now expressible over `ℚ_[p]`. Being able
to state them is not being able to prove them: ABHN itself is untouched.

---

## 0.4 Status (2026-08-22, later) — auditing the seven inputs against the code

§1.4 below classifies the arithmetic that Scholz–Reichardt consumes into seven inputs. That table
was written before the class field theory layer existed. Re-reading it against what is now in the
repository changes the picture substantially: **five of the seven are done or elementary, and only
one is genuinely out of reach.**

| § 1.4 input | rating there | actual status |
|---|---|---|
| 1. choice of `q` in the split case | (a) | **done** — `CFT/Scholz/PrimeChoice.lean` |
| 2. `H²(ℚ, C_ℓ) → ∏_p H²(ℚ_p, C_ℓ)` injective (ABHN) | (d) | **the one real blocker** |
| 3. local liftability at unramified `p` | (a) | **elementary**, and the statement is available |
| 4. local liftability at tame ramified `p` | (d) | **(d)-lite**; every Scholz prime is tame (below) |
| 5. gluing local characters into a global one | (d) | **elementary in this setting** (below) |
| 6. linear disjointness of `ℚ(μ_ℓ, p^{1/ℓ})` | (a) | group-theoretic half **done** — `CFT/ScalarSemidirect.lean` |
| 7. a prime with prescribed Frobenius | (c) | **done unconditionally** — `NumberTheory/SplitDensity.lean` |

Three of these deserve comment.

**Input 7 is exactly the theorem (★) of §1.5, and it is proved.**
`InverseGalois.NumberTheory.infinite_setOf_splitsCompletely_not_splitsCompletely` states that for
number fields `A ⊂ B` with `finrank ℚ A < finrank ℚ B` there are infinitely many rational primes
splitting completely in `A` and not in `B`; it is deduced from
`hasDirichletDensity_splitSet`, which gives the split set of a Galois number field Dirichlet
density `1 / n`, with the Euler-product input discharged by
`InverseGalois.NumberTheory.eulerProductHypothesis`. No Chebotarev, no `L`-functions of nontrivial
characters — the analytic content is the pole of the Dedekind zeta function alone. So the input
that §1.4 rated hardest after ABHN costs nothing.

**Input 6's group theory is done.** `CFT/ScalarSemidirect.lean` builds
`ScalarSemidirect ℓ s = (Fin s → ZMod ℓ) ⋊ (ZMod ℓ)ˣ` with the scalar action and proves
`scalarSemidirect_not_exists_quotient_card`: for `ℓ` odd it has no quotient of order `ℓ`, because
conjugation by `-1` inverts the module, so the module lies in the commutator subgroup, and the
complement has order `ℓ - 1`, which `ℓ` does not divide. This is the only place in the whole
argument where `ℓ ≠ 2` is used. What remains of input 6 is the *field-theoretic* half: identifying
`Gal(ℚ(μ_ℓ, p₁^{1/ℓ}, …, p_s^{1/ℓ})/ℚ)` with that semidirect product.

**Kronecker–Weber is not a Scholz–Reichardt blocker.** Milestone 8 below lists it as a gate. It is
not one, for the following reason: in the Scholz condition `(S_N)` every ramified prime `p`
satisfies `p ≡ 1 mod ℓ^N`, hence `p ≠ ℓ`, hence the ramification is **tame** and the inertia group
at `p` is cyclic of order dividing `ℓ^N`, with the local extension contained in the tame abelian
part of `ℚ_p^ab`, which is `ℚ_p(μ_{p^k})`-by-unramified and completely explicit. Input 4 is
therefore a statement about `(ℤ/ℓ^N)²` = (unramified) × (tame), and input 5 — Serre's Lemma
2.1.6, gluing prescribed local abelian characters into one global Dirichlet character — reduces
to choosing a Dirichlet character of the right conductor, because the local conditions live on
cyclotomic fields to begin with. Neither needs the *converse* statement that every abelian
extension of `ℚ` is cyclotomic.

A caution recorded here so it is not rediscovered: **`(S_N)` is not closed under compositum**
without the splitting hypotheses of `CFT/Scholz/SplitCase.lean`. Take `ℓ = 2`, `N = 1`: `ℚ(√3)`
and `ℚ(√−3)` are each ramified only at `3` (and, for the first, `2`), but their compositum
`ℚ(√3, i)` acquires a ramified prime whose inertia is not of split type. The compositum theorem
`IsScholz.of_sup_eq_top` genuinely needs the two-way splitting hypotheses it carries.

**Conclusion.** The single irreducible obstruction is the central embedding step, isolated in the
code as the hypothesis `InverseGalois.CFT.IsCentralStepSolvable ℓ` of
`CFT/Scholz/Induction.lean`, and its arithmetic content is ABHN for cyclic algebras of odd degree
over `ℚ`. Everything the induction needs *around* that step is now either proved or elementary.
`isScholzRealizable_of_isPGroup` is stated with that hypothesis and is otherwise complete: supply
ABHN and every finite `ℓ`-group, `ℓ` odd, is realised over `ℚ`.

---

## 0.5 Status (2026-08-22, evening) — the hypothesis narrowed three times

ABHN did not fall. What did happen is that the *statement* of the remaining hypothesis was cut
down three times, so that the arithmetic still owed is as small as the argument allows, and input 6
was finished on both halves.

**The step is only needed for `ℓ`-groups.** The induction of `CFT/Scholz/Induction.lean` peels a
central subgroup of order `ℓ` off a group of order `ℓ ^ k`, so the source of the surjection it
feeds to the step is always an `ℓ`-group. `IsCentralStepSolvable ℓ` now carries `IsPGroup ℓ G` as a
hypothesis; the old statement quantified over all finite `G`, which is strictly more than
Scholz–Reichardt proves.

**The step is only needed for non-split extensions.** `CFT/Scholz/SplitReduction.lean` proves
`IsCentralStepSolvable.of_nonsplit`: a surjection with central kernel admitting a homomorphic
section presents its source as `H × C_ℓ` (`mulEquivProdOfSection`), and the compositum construction
of the split case already realises such a product — without even spending a level, since
`IsScholzRealizable.mono` lowers the level for free.

**The step is only needed for kernels inside the Frattini subgroup.**
`CFT/Scholz/FrattiniStep.lean` proves `IsCentralStepSolvable.of_frattini`: a kernel of prime order
escaping some maximal subgroup `M` meets `M` trivially and generates the group with it, so `M` is a
complement and the surjection restricts to an isomorphism `M ≅ H` whose inverse is a section. Only
Frattini kernels are left, and those are exactly the extensions with a nonzero obstruction.

So the hypothesis that stands between the repository and Scholz–Reichardt is now

> `IsFrattiniCentralStepSolvable ℓ`: for a finite **`ℓ`-group** `G` surjecting onto `H` with
> **central** kernel of order `ℓ` contained in the **Frattini subgroup** of `G`, a realization of
> `H` satisfying `(S_{N+1})` extends to one of `G` satisfying `(S_N)`.

**The conclusion was raised from `ℓ`-groups to odd nilpotent groups.**
`CFT/Scholz/NilpotentOdd.lean`: a finite nilpotent group is the product of its Sylow subgroups,
which are `q`-groups for the odd primes `q` dividing its order and pairwise coprime, so granted the
step for every odd prime, **every finite nilpotent group of odd order is a Galois group over `ℚ`.**

**Input 6 is complete.** `CFT/Scholz/RadicalDisjoint.lean` proves the field-theoretic half
abstractly — a number field Galois over `ℚ` and generated by a primitive `ℓ`-th root of unity `ζ`
together with elements whose `ℓ`-th powers are rational has no quotient of order `ℓ`, because the
automorphism squaring `ζ` conjugates every automorphism fixing `ζ` into its square and hence forces
the whole `ζ`-fixing subgroup into the commutator subgroup — and `CFT/Scholz/RadicalTower.lean`
builds the field itself, as the splitting field of `∏_{c ∈ {1} ∪ S} (X ^ ℓ − c)` inside
`AlgebraicClosure ℚ`, so `inf_radicalField_eq_bot` is available in the form the induction wants.

**Unconditional by-product.** The same session's group theory gave a new class of *regular*
realizations, which owe nothing to any hypothesis: a finite group with a normal abelian subgroup of
cyclic quotient is semiabelian (`Solvable/SemiabelianCriterion.lean`), hence regular over `ℚ(T)`
(`Rigidity/RET/Wreath/AbelianByCyclic.lean`). The covering argument replaces a section: the cyclic
group generated by a lift of a generator of the quotient, together with the abelian subgroup,
surjects the semidirect product onto the group. Metacyclic groups and generalized quaternion
groups are the visible cases.

---

## 0.6 Status (2026-08-22, night) — the prime 2 handed to geometry, and a wider semiabelian class

Two things happened. The conditional theorem stopped being about odd groups, and the
unconditional class of regular realizations grew.

**The prime `2` is no longer an exception; it is a hypothesis on one Sylow subgroup.**
`CFT/Scholz/NilpotentSylowTwo.lean` splits the nilpotent assembly by prime: the odd Sylow
subgroups go through the Scholz–Reichardt induction, and the Sylow `2`-subgroup is left as an
assumption. `InverseGalois/Shafarevich.lean`, a new top-level module, discharges that assumption
with the *geometric* route — the Dentzer–Stoll wreath product construction, which is
unconditional — and so proves

> granted `IsCentralStepSolvable q` for every odd prime `q`, **a finite nilpotent group whose
> Sylow `2`-subgroup is semiabelian is a Galois group over `ℚ`**,

together with the corollaries for a Sylow `2`-subgroup that is abelian, cyclic, or of order at
most `8` — the last in the form *every finite nilpotent group of order not divisible by `16`*.
The two routes are genuinely independent: one is arithmetic and conditional, the other geometric
and unconditional, and they are joined only by the coprime-product closure of the realization
predicate.

**The semiabelian class was widened.** All of the following are new, sorry- and axiom-free, and
each one is immediately a *regular* realization over `ℚ(T)` through
`isRegularInverseGalois_of_isSemiabelian`; the corollaries are collected in
`Rigidity/RET/Wreath/SmallGroups.lean`.

* `Solvable/SemiabelianZGroup.lean` — **every finite Z-group is semiabelian**: Mathlib's
  `IsZGroup.isCyclic_commutator` and `IsZGroup.isCyclic_abelianization` exhibit a group all of
  whose Sylow subgroups are cyclic as metacyclic, which the metacyclic criterion already covers.
  In particular **every finite group of squarefree order is regular over `ℚ(T)`.**
* `Solvable/SemiabelianHall.lean` — the splitting criteria: a normal abelian subgroup with a
  complement (Schur–Zassenhaus, or a normal abelian Sylow subgroup, or any homomorphic section)
  and a semiabelian quotient gives a semiabelian group.
* `Solvable/SemiabelianSmall.lean` — a group with an abelian subgroup whose index is the smallest
  prime factor of the order is semiabelian, whence the orders `p`, `p ^ 2`, `p ^ 3` and `p * q`.
* `Solvable/SemiabelianCriterion.lean` gained `IsSemiabelian.of_mul_comm`, the abelian case with
  commutativity as a hypothesis rather than an instance.

What this does *not* do is move ABHN. The hypothesis of §0.5 is unchanged and remains the single
arithmetic debt.

---

## 0.7 Status (2026-08-22, late) — class two, every order below 24, and the Frattini induction

The semiabelian class was pushed again — once structurally, by nilpotency class, and once by
*order* — and the conditional nilpotent theorem moved one power of two.

**Every finite group of nilpotency class at most `2` is semiabelian**
(`Solvable/SemiabelianClassTwo.lean`, `IsSemiabelian.of_commutator_le_center`). This is the
structural high point of the batch and it is proved by the Frattini induction below in three lines
of mathematics: if `G' ≤ Z(G)` and `x ∉ Φ(G)`, then `A = ⟨x⟩ · Z(G)` is abelian, and it is normal
because `[A, G] ≤ G' ≤ Z(G) ≤ A`; a maximal subgroup supplementing `A` is proper and again of class
at most `2`, so the induction closes. Every subgroup of a class-`2` group has class at most `2`,
which is exactly what the induction needs and what fails for class `3`. In particular every
extraspecial group, every group of order `p ^ 3`, and every `2`-group of class `2` — of any order —
is regular over `ℚ(T)`, so the hypothesis on the prime `2` in the conditional Shafarevich theorem is
now met by an unbounded family of `2`-groups.

**Every finite group of order less than `24` is semiabelian**
(`Solvable/SemiabelianSmallOrders.lean`, `IsSemiabelian.of_card_lt_twentyfour`), hence regular over
`ℚ(T)`. Two new shape criteria were needed to close the gaps in the enumeration:

* `Solvable/SemiabelianP2Q.lean` — **order `p ^ 2 * q`** (`IsSemiabelian.of_card_eq_sq_mul_prime`).
  Sylow counting produces a normal Sylow subgroup in every case; the one order at which the counts
  admit no immediate normal subgroup, `12` with `n₂ = 3`, is settled separately by showing the
  Sylow `2`-subgroup is unique there.
* `Solvable/SemiabelianP2Q2.lean` — **order `p ^ 2 * q ^ 2`**
  (`IsSemiabelian.of_card_eq_sq_mul_sq`), whence the orders `36` and `100`. The one shape the
  counts leave open is `36` with four Sylow `3`-subgroups; there the kernel of the conjugation
  action on those four subgroups has order `3`, is central, and its quotient of order `12` hands
  back a normal Sylow `2`-subgroup.
* `Solvable/SemiabelianP4.lean` — **order `p ^ 4` for every prime `p`**
  (`IsSemiabelian.of_card_eq_prime_pow_four`). A maximal abelian normal subgroup of a `p`-group is
  self-centralizing, and in a group of order `p ^ 4` self-centralizing forces index at most `p`,
  so the quotient is cyclic and the criterion of §0.6 applies. In particular every group of order
  `16` is semiabelian.

`24` is exactly the right place for the enumeration to stop. **`SL(2,3)`, of order `24`, is the
smallest non-semiabelian group**: its only abelian normal subgroup is its centre `C₂`, which is
also its Frattini subgroup, so no abelian normal subgroup escapes the Frattini subgroup and no
supplement argument can start. The milestone is sharp, not an artefact of the criteria available.

**The supplement argument was isolated as an induction** (`Solvable/SemiabelianFrattini.lean`).
Call a finite group *Frattini-supplemented* when, unless trivial, it has an abelian normal subgroup
not contained in its Frattini subgroup. Such a subgroup is supplemented by a maximal subgroup —
a *proper*, hence smaller, subgroup — so `IsSemiabelian.of_isFrattiniSupplemented` turns the
covering criterion into a genuine induction on the order. This is the general form of every
order-by-order argument above, and it is also precisely what `SL(2,3)` defeats.

**Two criteria for a dominant prime** (`Solvable/SemiabelianLargePrime.lean`). If `|G| = m * q`
with `q` prime and `m < q`, the number of Sylow `q`-subgroups divides `m` and is `≡ 1 mod q`, so it
is `1`: the Sylow subgroup is normal, cyclic of prime order, and `G` is semiabelian as soon as the
quotient of order `m` is (`IsSemiabelian.of_card_eq_mul_prime_of_lt`). The same argument with
`|G| = m * q ^ 2` gives a normal Sylow subgroup of order `q ^ 2`, which is abelian
(`of_card_eq_mul_prime_sq_of_lt`). Combined with the order-`<24` theorem this yields two infinite
families with no bound on `|G|`: `of_card_eq_mul_prime_of_lt_twentyfour` and
`of_card_eq_mul_prime_sq_of_lt_twentyfour`, for `m < 24 < q`.

`Solvable/SemiabelianSylowCount.lean` replaces the size comparison `m < q` by the exact condition
the counting argument needs: no divisor of `m` other than `1` is congruent to `1` modulo `q`. That
is a statement about the finite set `m.divisors`, hence decidable, so at a concrete order it is
discharged by evaluation — the orders `40`, `45`, `75` and `99` are recorded that way.

**The hypothesis on the prime `2` is now met structurally as well as numerically.**
`isInverseGalois_of_isNilpotent_of_classTwo_sylow_two`: granted the odd central step, a finite
nilpotent group whose Sylow `2`-subgroup has nilpotency class at most `2` is a Galois group over
`ℚ`, with no bound at all on the order.

**The conditional headline moved from `16` to `32`.** With order `16` now semiabelian,
`isInverseGalois_of_isNilpotent_of_not_dvd_thirtytwo` says: granted the odd central step, every
finite nilpotent group of order not divisible by `32` is a Galois group over `ℚ`. The Sylow
`2`-subgroup then has order at most `16`, and every group of order `1, 2, 4, 8, 16` is semiabelian.

**The arithmetic hypothesis was narrowed.** `isInverseGalois_of_..._of_frattini` variants assume
only `IsFrattiniCentralStepSolvable q` — the central step for surjections whose kernel lies inside
the Frattini subgroup of the source. A central kernel of prime order escaping the Frattini subgroup
is complemented by a maximal subgroup, so that extension splits and is realised by a compositum
with no arithmetic at all. This is the narrowest form the induction actually calls for, and hence
the smallest statement ABHN would have to supply.

ABHN itself is untouched. `CFT/Global/` is, on inspection, entirely the `ℓ = 2` world —
Davenport–Cassels, Hilbert symbols, the Hasse principle for diagonal quadratic forms — so the
odd-`ℓ` injectivity of `H²(ℚ, C_ℓ) → ∏_p H²(ℚ_p, C_ℓ)` is not close. It remains the single debt.

---

## 0.8 How far the geometric route can go at all — the semiabelian literature

The conditional nilpotent theorem needs the Sylow `2`-subgroup to be semiabelian, so it is worth
knowing where that hypothesis stops being satisfiable. The reference is

> M. Kida, *On semiabelian groups*, J. Group Theory **27** (2024), 697–712,
> DOI [10.1515/jgth-2024-0010](https://doi.org/10.1515/jgth-2024-0010) (open access),

which is the first systematic study of which groups are semiabelian since Dentzer introduced the
class. Its facts, in the order they matter here.

**Not every finite `2`-group is semiabelian.** Wilkens' classification splits the non-modular
quaternion-free `2`-groups into types A, B, C; types A and B are semiabelian (Kida, Prop. 3.10) but
type C is not (Kida, Thm 4.6). So the geometric route can never, by itself, finish the nilpotent
case of Shafarevich: there is a genuine obstruction at the prime `2`, not merely a gap in the
criteria available here.

**Where the obstruction starts.** Kida's Magma computation (Example 5.5) lists every non-semiabelian
*stem* group of order at most `100`:

  `(24,3) = SL(2,3)`, `(48,28) = C2 . S4`, `(64,8) = C2² . SD16`, `(64,41) = D8 ⋊ C4`,
  `(96,3)`, `(96,190)`, `(96,201)`, `(96,203)`.

Since being semiabelian is invariant under isoclinism (Kida, Thm 1.1) and every group is isoclinic
to a stem group, this says: the smallest non-semiabelian group is `SL(2,3)` of order `24`, and the
smallest non-semiabelian **`2`-group** has order `64`. Every group of order `32` is semiabelian.
So `isInverseGalois_of_isNilpotent_of_not_dvd_thirtytwo` could in principle be improved to
"not divisible by `64`" and no further — but that would mean checking all `51` groups of order `32`,
whereas the criteria formalized here are structural.

**The criteria Kida proves.** Nilpotent of class `2` (Thompson; formalized here in §0.7); solvable
with all Sylow subgroups abelian (Thompson); modular `p`-groups and Hamiltonian `2`-groups
(Prop. 3.6); Wilkens types A and B (Prop. 3.10); the isoclinism invariance (Thm 1.1); and, for
non-nilpotent solvable groups, a criterion through Carter subgroups (Prop. 5.4). The class is closed
under quotients, direct products and wreath products, but **not** under subgroups — `(96,204)` is
semiabelian and contains `SL(2,3)`, which is not. That failure of subgroup-closure is exactly what
makes the Frattini induction of §0.7 have to carry its hypothesis along by hand.

**Consequences worth formalizing, in order of value.** Thompson's abelian-Sylow criterion is the
widest of them and subsumes a great deal: a group of cubefree order has all its Sylow subgroups of
order `1`, `p` or `p²`, hence abelian, so *every finite solvable group of cubefree order is
semiabelian*, which contains the whole `p^a q^b` small-order zoo already treated one shape at a
time. Wreath-product closure is the next: iterated wreath products of `C_p` are exactly the Sylow
`p`-subgroups of the symmetric groups, an unbounded family of `p`-groups.

---

## 0.9 Status (2026-08-22, late evening) — Thompson's criterion, wreath closure, order below 32

Both of the "consequences worth formalizing" of §0.8 are now in the repository, sorry- and
axiom-free, together with one more step of the enumeration of small orders.

**Thompson's abelian-Sylow criterion.** `InverseGalois/Solvable/SemiabelianAGroup.lean`:

```lean
IsSemiabelian.of_forall_sylow_comm {G : Type} [Group G] [Finite G] [IsSolvable G] :
  (∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (x y : ↥(P : Subgroup G)), x * y = y * x) →
    IsSemiabelian G

IsSemiabelian.of_isSolvable_of_cubefree {G : Type} [Group G] [Finite G] [IsSolvable G] :
  (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ Nat.card G) → IsSemiabelian G
```

The proof is the Frattini induction of §0.7 with a new supply of abelian normal subgroups escaping
the Frattini subgroup. Write `Q = frattini G`, which is proper and normal. The quotient `G ⧸ Q` is
nontrivial and solvable, so it has a minimal normal subgroup `K` that is elementary abelian of some
exponent `p`; let `N` be its preimage in `G` and `P` a Sylow `p`-subgroup of `N`. Then `P ⊔ Q = N`,
because the index of the join divides both the `p`-free index of `P` in `N` and the `p`-power
`Q.relIndex N`. Frattini's argument (`Sylow.normalizer_sup_eq_top`) gives
`(P : Subgroup G).normalizer ⊔ N = ⊤`, hence `normalizer ⊔ Q = ⊤`, and since the Frattini subgroup
is non-generating this forces `normalizer = ⊤`: `P` is normal in `G`. It is abelian because it is a
`p`-subgroup and therefore sits inside a Sylow `p`-subgroup of `G`, which is abelian by hypothesis;
and it is not contained in `Q`, since otherwise `N = P ⊔ Q = Q`. The hypothesis passes to subgroups
(a Sylow subgroup of a subgroup is contained in a Sylow subgroup of the whole group), which is what
lets the induction on `Nat.card G` run in spite of the failure of subgroup-closure for
semiabelianness itself.

**Wreath closure.** `InverseGalois/Solvable/SemiabelianWreath.lean`:

```lean
IsSemiabelian.regularWreathProduct : IsSemiabelian D → IsSemiabelian Q → IsSemiabelian (D ≀ᵣ Q)
IsSemiabelian.iteratedWreathProduct : IsSemiabelian G → ∀ n, IsSemiabelian (IteratedWreathProduct G n)
IsSemiabelian.sylow_perm {p n : ℕ} [Fact p.Prime] {α : Type} [Finite α] :
  Nat.card α = p ^ n → ∀ P : Sylow p (Equiv.Perm α), IsSemiabelian ↥(P : Subgroup (Equiv.Perm α))
```

The induction is on the derivation of `IsSemiabelian D`, using the functoriality of `D ≀ᵣ Q` in its
bottom argument: an injection `D₁ →* D₂` induces an injection of wreath products and a surjection
induces a surjection, so the `of_surjective` case is immediate, and the semidirect-product case
identifies the kernel of `mapLeft SemidirectProduct.rightHom` as an abelian normal subgroup with a
semiabelian quotient. The Sylow statement is Mathlib's
`Sylow.mulEquivIteratedWreathProduct`, which presents a Sylow `p`-subgroup of `Equiv.Perm α` for
`Nat.card α = p ^ n` as the `n`-fold iterated wreath product of a group of order `p`.

**One more order.** `IsSemiabelian.of_card_lt_thirtytwo` covers every finite group of order less
than `32` other than `24`: the orders `25` to `31` are `5²`, `2 · 13`, `3³`, `2² · 7`, the primes
`29` and `31`, and the squarefree order `30`, each already covered by a shape criterion. `24` is
`SL(2,3)`'s order and is genuinely excluded. `Squarefree 30` needs `decide +kernel` — plain `decide`
gets stuck on the well-founded recursion in `Nat.minSqFac`, and `norm_num` has no extension for it.

**Regular corollaries.** Each of these appears in `RET/Wreath/SmallGroups.lean` as an entry of the
catalogue of regular Galois groups over `ℚ(T)`: `isRegularInverseGalois_of_forall_sylow_comm`,
`isRegularInverseGalois_of_isSolvable_of_cubefree`, `isRegularInverseGalois_sylow_perm`,
`isRegularInverseGalois_iteratedWreathProduct`, `isRegularInverseGalois_of_card_lt_thirtytwo`.

**What blocks the next order.** The conditional nilpotent theorem is still
`isInverseGalois_of_isNilpotent_of_not_dvd_thirtytwo`, because the criteria above say nothing about
a `2`-group of order `32` in which *every* abelian normal subgroup lies inside the Frattini
subgroup. The situation is completely pinned down: for such a `G`, a maximal abelian normal
subgroup `A` is self-centralizing, `|A| = 4` is impossible (`Aut C4` and `Aut (C2 × C2)` have no
subgroup of order `8`), `|A| ≤ 2` forces `C_G(A) = G`, and `|A| ≥ 16` makes `G` abelian or gives an
abelian subgroup of index `2`; so `|A| = 8` and, `G` being non-cyclic, `A = Φ(G)` with
`G / A ≅ C2 × C2` acting faithfully. For `A ≅ C8` this is contradictory: `x² ∈ A` cannot generate
`A` (that would put `x` in `C_G(A)`), so the commutator `[x, y]` is a square in `A`, and then
`⟨a², y⟩` is an abelian normal subgroup of order `8` outside `A`. The cases `A ≅ C4 × C2` and
`A ≅ C2³` (where `G / A` is one of the Klein subgroups of `GL(3,2)`) are the remaining work, and
they are what stands between `not_dvd_thirtytwo` and the sharp `not_dvd_sixtyfour` of §0.8.

Past `32`, the orders `33` to `47` are all covered already — `40 = 2³ · 5` and `45 = 3² · 5` by the
divisor count that makes the largest Sylow subgroup unique, `36 = 2² · 3²` by the `p² q²` file, the
rest by shape — so `InverseGalois/Solvable/SemiabelianFortyEight.lean` records

```lean
IsSemiabelian.of_card_lt_fortyeight {G : Type} [Group G] [Finite G] :
  Nat.card G < 48 → Nat.card G ≠ 24 → Nat.card G ≠ 32 → IsSemiabelian G
```

and settling the order `32` would remove the second exception at once. The bound `48` is sharp:
`(48,28) = C2 . S4` is not semiabelian.

---

## 0.10 Status (2026-08-24) — class field theory, and the second inequality

Of the two blockers named in §0.2, Albert–Brauer–Hasse–Noether is the one that cannot be dodged:
the embedding problem of Scholz–Reichardt is solvable exactly because a Brauer class that is
locally trivial everywhere is trivial, and there is no elementary substitute for that in exponent
`ℓ > 2`. The degree-two slice of ABHN is already in the tree (`docs/Development/ClassFieldTheory.md`
§1.3), by an argument about ternary quadratic forms that generalises to nothing. So the real
class field theory has to be built, and the route being followed is Milne, *Class Field Theory*,
chapter VII: the two inequalities for the idele class group, then reciprocity, then the exact
sequence of Brauer groups. This section records how far that has got; the file-level map is in
`docs/Development/ClassFieldTheory.md` §4.

**Tate cohomology of a cyclic group.** `InverseGalois/CFT/Tate/` is a self-contained development
of `Ĥ⁰` and `Ĥ⁻¹` for an automorphism `σ` of an abelian group of order dividing `n`, together with
the Herbrand quotient

```lean
InverseGalois.CFT.herbrand (σ : A ≃+ A) (n : ℕ) : ℚ :=
  (Nat.card (tateH0 σ n) : ℚ) / (Nat.card (tateHm1 σ n) : ℚ)
```

and everything the quotient is normally used with: the six-term hexagon of a short exact sequence
(`Exact.lean`, `Hexagon.lean`) and hence multiplicativity, invariance under a commensurable
subgroup (`Commensurable.lean`, `Isogeny.lean`), Shapiro's lemma for an induced module
(`Shapiro.lean`, `InducedLattice.lean`, `PermLattice.lean`), Hilbert 90 for a cyclic action
(`CyclicHilbert90.lean`), and transport along an equivariant isomorphism (`Congr.lean`). For a
trivial action the two groups are the cokernel and the kernel of multiplication by `n`
(`Trivial.lean`, `TrivialLattice.lean`), which is what turns every Herbrand computation below into
an index computation.

**The local layer.** `InverseGalois/CFT/Local/` computes the local invariants a place at a time.
The units of a complete discretely valued field have Herbrand quotient the degree of the extension
(`UnitFiltration.lean`, `FiltrationHerbrand.lean`, `UnitHerbrandChain.lean`), by filtering the unit
group and matching each graded piece against the additive filtration through the exponential
(`Exp.lean`, `ExpEquiv.lean`, `ExpSurjective.lean`). The same exponential, run in the other
direction, shows that a unit congruent to one to sufficient accuracy is an `n`-th power
(`PowNeighbourhood.lean`), the accuracy needed being governed by the valuation of the residue
characteristic and the valuation of `n`. Reading the Herbrand quotient of the units through its
definition then gives the local index of the `n`-th powers:

```lean
InverseGalois.CFT.index_range_powMonoidHom_localUnitGroup
    (hsurj : Function.Surjective (Valued.v : A → ℤᵐ⁰)) [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) (hnz : n ≠ 0)
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
  (powMonoidHom n : ↥(localUnitGroup A) →* ↥(localUnitGroup A)).range.index
    = Nat.card (gradedAdd A 0) ^ m * Nat.card ↥(rootsOfUnity n A)
```

with the corresponding statements for the whole multiplicative group at a finite place
(`AdicPowIndex.lean`) and at an infinite one (`InfinitePowIndex.lean`) — this is Milne 6.8. The
local norm index `(K_v^× : Nm L_w^×) = [L_w : K_v]` for a cyclic local extension is
`NormIndex.lean`, on top of the unramified and ramified norm forms.

**The idele layer.** `InverseGalois/CFT/Units/` assembles the local factors into the ideles.
`Idele.lean` defines them as a restricted product, written additively, of the unit groups of the
completions; `AdicSIdeles.lean` and `SUnit.lean` cut out the `S`-ideles and the `S`-units;
`IdeleClass.lean` forms the idele class group with its Galois action and identifies its Tate
cohomology with that of the `S`-idele classes for a large enough `S`. Combining the local Herbrand
quotients through Shapiro's lemma over the orbits of the Galois group on the places
(`AdicIdeleHerbrand.lean`, `SIdeleHerbrand.lean`, `SUnitHerbrand.lean`) gives

```lean
InverseGalois.CFT.herbrand_ideleClassAut_eq_degree :
  herbrand (ideleClassAut (k := k) (K := K) σ) n = n
```

for a cyclic extension of degree `n`, and hence **the first inequality**:

```lean
InverseGalois.CFT.first_inequality : n ≤ Nat.card (tateH0 (ideleClassAut (k := k) (K := K) σ) n)
```

**The second inequality.** This is Milne VII §6, the algebraic proof. *This subsection describes
the state on 2026-08-24 and has since been overtaken: the second inequality is done. The
prime-degree case is `Kummer/SecondInequality.lean`, the root of unity is removed by
`Kummer/CyclotomicDescent.lean`, and `Kummer/CyclicIndex.lean` climbs the tower to give
`index_ideleDiag_sup_ideleNorm_eq_card`, the norm index of an arbitrary cyclic extension of number
fields being its degree. What follows is kept for the map of the pieces.* The strategy is
Kummer-theoretic: adjoin an `ℓ`-th root of unity, choose a set of
places `S` containing the infinite places, the places above `ℓ` and enough places to make the
class group trivial, and count the index of a large group of `n`-th powers inside the `S`-ideles
in two ways. The counting ingredients are now in place.

* The global index of the `n`-th powers in the `S`-units — Milne 6.7's first half — is
  `Units/SUnitIndex.lean`, `index_range_powMonoidHom_sUnits`, `= n ^ (r₁ + r₂ + |S|)` in the usual
  notation; the proof is the Dirichlet unit lattice plus the Herbrand quotient of a trivial action
  on a finitely generated group.
* The product of the local indices over the relevant places — Milne 6.6 — is
  `Kummer/PowIndex.lean`, `prod_index_range_powMonoidHom_units_of_isPrimitiveRoot`, `= n ^ (2 |S|)`
  when the base field contains a primitive `n`-th root of unity and `S` contains every place at
  which `n` is not a unit. Milne's product runs over `S` alone, which is exactly what this counts.
* Its idele formulation is `Units/PowIdele.lean`: the subgroup of the `S`-ideles carrying the
  `n`-th powers has relative index the product of those local indices,

  ```lean
  InverseGalois.CFT.relIndex_powSIdele_of_isPrimitiveRoot (hζ : IsPrimitiveRoot ζ n)
      (F : Finset (HeightOneSpectrum (𝓞 K))) (hF : ∀ v, v ∈ F ↔ v ∈ S)
      (hn : ∀ v, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ F) :
    (powSIdele S T n).relIndex (sIdele S T) = n ^ (2 * (Fintype.card (InfinitePlace K) + F.card))
  ```

  resting on the general fact (`PiIndex.lean`) that two subgroups of a product which are given
  place by place and agree outside a finite set have relative index the product of the local
  relative indices.
* Milne 6.4, that the group `E` of Kummer generators consists of norms, is the element-level
  Shapiro chain of `Units/SIdeleNorm.lean`; Milne 6.5 is the index identity
  `relIndex_sup_mul_relIndex_inf`.

What is left of §6 is the Kummer-theoretic half rather than the counting half: 6.3 (an `S`-unit
that is an `n`-th power in every completion at a place of `T` is one in the Kummer extension), 6.9
(surjectivity of `U(S) → ∏_{v ∈ T} U_v/U_v^p`, which needs 6.3 and the order count `[M : L] = p^t`),
the remaining inclusion in 6.7, and then 6.1–6.2, which reduce the general case to one containing
the `p`-th roots of unity and need Milne 4.7 (Frobenius elements generate).

**A topology-free route to the end of §6.** Milne's Proposition 4.5 — a finite solvable extension
with `K^× · D` dense in `I_K` for some `D ⊆ Nm(I_L)` is trivial — is stated with the idele
topology, which the repo does not have. It is not needed. The variant

> if `L/K` is finite solvable and `D ≤ I_K` satisfies `D ⊆ Nm_{L/K}(I_L)` and `K^× · D = I_K`
> **exactly**, then `L = K`

has a two-line proof from the first inequality: pick `K ⊊ K' ⊆ L` with `K'/K` cyclic, then
`I_K = K^× · D ⊆ K^× · Nm(I_{K'}) ⊆ I_K`, so `(I_K : K^× Nm I_{K'}) = 1`, contradicting
`(I_K : K^× Nm I_{K'}) ≥ [K' : K] > 1`. Milne 6.10(b) delivers the *equality* `I_K = D · K^×`,
not merely density, so the whole of §6 can be run without ever topologising the ideles.

Both of the bricks that route needs are now laid, for the cyclic extensions that are all it uses.

1. **The idele norm map.** `Units/IdeleNorm.lean` defines `ideleNorm k K hgen hσ : I_K → I_k` for a
   cyclic extension. The assembly over the places is avoided entirely: the sum of the conjugates of
   an idele is fixed by the generator, hence by the whole group, hence — by the fixed-point theorem
   below — is the image of a unique idele of the base field, and that idele is the norm. The
   defining property is `ideleComap_ideleNorm`, that the norm read in the extension is the Tate norm
   of the Galois action.
2. **Milne Lemma 4.1.** `Units/IdeleFixed.lean` proves `mem_range_ideleComap_iff`, that an idele of
   the extension is fixed by the Galois group exactly when it comes from the base field, and
   `Units/IdeleClassIndex.lean` proves the idele-class half in the form the inequalities want:

   ```lean
   InverseGalois.CFT.ideleQuotEquivTateH0 :
     (↥(idele k) ⧸ ((ideleDiag k).range ⊔ (ideleNorm k K hgen hσ).range))
       ≃+ tateH0 (ideleClassAut (k := k) σ) n
   ```

   The map sends an idele of the base field to the class of its image, which is fixed; it is
   surjective because a fixed class is the class of a fixed idele and a fixed idele comes from the
   base field; and it kills exactly the principal ideles and the norms, because a principal idele of
   the extension fixed by the Galois group is the principal idele of a unit of the base field.

So `first_inequality` now reads in its classical form,

```lean
InverseGalois.CFT.first_inequality_index :
  n ≤ ((ideleDiag k).range ⊔ (ideleNorm k K hgen hσ).range).index
```

that is `(I_k : k^× · Nm I_K) ≥ [K : k]`, and the topology-free 4.5′ is its immediate corollary for
a cyclic extension, `Units/NormIndex.lean`:

```lean
InverseGalois.CFT.subsingleton_gal_of_ideleDiag_sup_ideleNorm_eq_top
    (htop : (ideleDiag k).range ⊔ (ideleNorm k K hgen hσ).range = ⊤) : Subsingleton Gal(K/k)
```

Norm transitivity, `Nm_{L/K} = Nm_{K'/K} ∘ Nm_{L/K'}` — what lets the cyclic step be taken inside a
tower — is `Units/IdeleNormTower.lean`:

```lean
InverseGalois.CFT.ideleNorm_trans (x : ↥(idele K)) :
  ideleNorm k F (ideleNorm F K x) = ideleNorm k K x
```

Both the tower compatibility of the inclusions (`ideleComap_trans`, `Units/IdeleTower.lean`, resting
on the place-by-place compatibilities of `Units/PlaceTower.lean`) and the equivariance of the
inclusion under restriction of automorphisms (`ideleAut_ideleComap_restrict`,
`Units/IdeleRestrict.lean`, resting on `Units/PlaceRestrict.lean`) feed into it; the sum over the
Galois group of the whole extension splits because lifting an automorphism of the middle field and
multiplying by one fixing it is a bijection from the product of the two Galois groups.

With that, **4.5′ holds for a solvable extension**, `Units/SolvableNorm.lean`:

```lean
InverseGalois.CFT.subsingleton_gal_of_isSolvable_of_ideleDiag_sup_le [IsSolvable Gal(K/k)]
    (hD : D ≤ (ideleNorm k K).range) (htop : (ideleDiag k).range ⊔ D = ⊤) :
  Subsingleton Gal(K/k)
```

The cyclic subextension is produced group-theoretically: a nontrivial finite solvable group has a
nontrivial complex character (its abelianization is a nontrivial finite commutative group and
characters separate the elements of such a group), and the quotient by the kernel of a character is
a finite subgroup of `ℂ^×`, hence cyclic; the fixed field of the kernel is the `K'` above.

What remains of the §6 count is recorded above; ABHN itself, however, does not wait for it — see
§0.11.

---

## 0.11 Status (2026-08-25) — Albert–Brauer–Hasse–Noether, and the shape it takes for Scholz

ABHN is in the tree. It did **not** need the second inequality, reciprocity, or the Brauer-group
exact sequence of Milne §7: the cohomological form of the theorem is exactly the injectivity of
`H²(G, K^×) → H²(G, I_K)` together with the vanishing of `H²` of the ideles place by place, and
the injectivity is the long exact sequence of

```text
1 → K^× → I_K → C_K → 1
```

fed by `H¹(G, C_K) = 0`, which the first inequality already gives — `Units/IdeleClassH1.lean` for a
cyclic group and `Units/IdeleClassH1Full.lean` in general, via dévissage along a solvable series.
So the statement is

```lean
InverseGalois.CFT.injective_map_H2_globalUnits (k K) :          -- Units/IdeleClassSES.lean
  Function.Injective ((map … (globalUnitsToIdele k K) …).hom)
```

and, combined with the place-by-place statement `exists_coboundary_idele`
(`Units/IdeleCoboundary.lean`, a two-cocycle of the ideles which is a coboundary at every place is
a coboundary — the restricted-product bookkeeping is `Units/IdeleClass.lean`):

```lean
InverseGalois.CFT.exists_sub_add_eq_globalUnits                 -- Units/ABHN.lean
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (ha  : ∀ x y z, globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y)
    (hinf : ∀ w : InfinitePlace K, … the image of `a` in `w.Completionˣ` is a coboundary …)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), … the image of `a` in `(v.adicCompletion K)ˣ` is … ) :
  ∃ b, ∀ x y, a x y = globalUnitsAut x (b y) - b (x * y) + b x
```

**The local hypotheses, and how many of them are real.** For the Scholz–Reichardt step the cocycle
is killed by an odd prime `ℓ`, and then almost all of `hinf`/`hfin` is free.

* *Archimedean places.* `GroupCohomology/CoprimeCoboundary.lean` proves that summing the cocycle
  identity over its third variable exhibits `|G| • f` as the coboundary of `y ↦ ∑ z, f y z`
  (`nsmul_card_eq_of_isCocycle₂`), so a Bézout combination gives

  ```lean
  InverseGalois.CFT.exists_sub_add_eq_of_coprime (φ : G →* AddAut M)
      (hcop : Nat.Coprime (Nat.card G) n) (hf : … cocycle …) (hn : ∀ x y, n • f x y = 0) :
    ∃ c, ∀ x y, f x y = φ x (c y) - c (x * y) + c x
  ```

  Mathlib's `NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two` says the decomposition
  group at an archimedean place has order one or two, which is coprime to an odd `n`.
* *Unramified finite places.* A unit killed by a nonzero integer has valuation zero, because the
  valuation lands in the torsion-free group `ℤ` (`mem_ker_unitVal_of_nsmul_eq_zero`). So the local
  component is a two-cocycle of the decomposition group with values in the units of the valuation
  ring, and there `Local/UnramifiedCoboundary.lean` already had the vanishing: the decomposition
  group is cyclic and the norm on the units of the valuation ring is surjective.
* *Ramified finite places.* These are the only ones left, and they are precisely where Serre's
  condition `(S_{N+1})` — `p ≡ 1 mod ℓ^{N+1}`, residue degree one, tame — is spent.

The assembly of those three observations is the new module `Units/ABHNTorsion.lean`, whose main
statement is the form of ABHN that a central embedding problem with kernel of odd prime order meets:

```lean
InverseGalois.CFT.exists_sub_add_eq_globalUnits_of_odd {n : ℕ} (hn : Odd n)
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (hpow : ∀ x y, n • a x y = 0)
    (ha   : ∀ x y z, globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y)
    (hram : ∀ v, ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal → … local coboundary at `v` …) :
  ∃ b, ∀ x y, a x y = globalUnitsAut x (b y) - b (x * y) + b x
```

It rests on the equivariance of the local embeddings for the decomposition group,
`smulUnitsAut_adicUnitHom` and `smulUnitsAut_infiniteUnitHom`, also in that module.

**Getting back down to `μ_ℓ`.** ABHN is a statement about `K^×`, and the obstruction of the
embedding problem lives in `H²(G, ℤ/ℓ)`. The two are matched by the Kummer sequence, which is
`Kummer/InflationRootsOfUnity.lean`: Hilbert 90 turns a coboundary in `K^×` into an element `β`
with `g • β / β = b g ^ n` (`exists_pow_eq_of_isMulCoboundary₂`), and over an extension containing
an `n`-th root of `β` the inflated cocycle is cobounded by a cochain of `n`-th roots of unity
(`exists_cochain_pow_eq_one`). Since `H²(D, μ_ℓ) → H²(D, K_w^×)` is injective for the local
decomposition groups, nothing is lost in the passage.

**Getting back down from `ℚ(μ_ℓ)`.** The Kummer argument wants the `ℓ`-th roots of unity in the
base, and the degree of that adjunction divides `ℓ - 1`, hence is coprime to `ℓ`. The descent is
group-theoretic, `GroupCohomology/CoprimeSplit.lean`:

```lean
InverseGalois.CFT.exists_splitting_of_coprime_index
    (π : E →* G) (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    (hcop : Nat.Coprime U.index (Nat.card π.ker)) (s : U →* E) (hs : ∀ u, π (s u) = u) :
  ∃ σ : G →* E, ∀ g, π (σ g) = g
```

by the transfer: the transfer of the difference between the identity of `E` and the given section
is the `U.index`-th power map on the kernel, which is bijective there, so inverting it turns the
transfer into a retraction and dividing the identity by that retraction kills the kernel.

**What is still missing for `IsFrattiniCentralStepSolvable ℓ`.** The remaining inputs are all on
the ramified side and all local:

1. local liftability at a ramified tame `p` satisfying `(S_{N+1})`, where `Gal(E/ℚ_p) ≅ (ℤ/ℓ^N)²`;
2. the gluing of the local characters into one global condition;
3. the radical closure — given `β ∈ K^×` and `n`, a finite normal extension `M/k` containing an
   `n`-th root of `β`, which is `IntermediateField.normalClosure` applied to `K(α)` with
   `Polynomial.monic_X_pow_sub_C` supplying integrality;
4. the conversion of the resulting `μ_ℓ`-valued cochain into a solution of the embedding problem,
   the improper-to-proper upgrade through the Frattini kernel (`Scholz/FrattiniStep.lean` already
   has `exists_section_of_not_le_frattini`), and the preservation of `(S_N)`.

---

## 0.12 Status (2026-08-25) — item 5 is *not* Kronecker–Weber; it is one local count at `ℓ`

Items 1, 3 and 4 of the list closing §0.11 are done (`Kummer/RadicalClosure.lean`,
`Kummer/CocycleDescent.lean`, `Kummer/CentralEmbedding.lean`, `Local/PrimeResidue.lean`,
`Units/ABHNRamified.lean`, `GroupCohomology/CoprimeDescent.lean`). What the Kummer tower now
delivers is packaged as

```lean
InverseGalois.CFT.HasProperSolution (K : IntermediateField k Ω) (f : G →* H) (π : Gal(↥K/k) →* H) :=
  ∃ M, K ≤ M ∧ NumberField ↥M ∧ IsGalois k ↥M ∧
    ∃ ρ : Gal(↥M/k) →* Gal(↥K/k), Surjective ρ ∧ (ρ is restriction of automorphisms) ∧
      ∃ φ : Gal(↥M/k) →* G, Surjective φ ∧ ∀ g, f (φ g) = π (ρ g)
```

— a *proper* solution of the embedding problem in a field containing the given one, with the
compatibility retained. **It carries no ramification control at all**, and that is now the whole of
what is left.

### The reduction of Serre's Lemma 2.1.6 over ℚ

Serre glues local characters using local *and* global class field theory. Over ℚ, and for a kernel
`C = C_ℓ` of prime order, the gluing needs strictly less. Write `ε_p := φ̃|_{I_p}`, a character
`I_p → C_ℓ` (it lands in `C_ℓ` because `φ = π ∘ φ̃` is unramified at every `p ∉ ram(L)`, and `L`
satisfies `(S_{N+1})` so `ℓ ∉ ram(L)`). Two elementary observations collapse the problem:

* `ε_p` is invariant under conjugation by the decomposition group `D_p`, because `C_ℓ` is central
  in `G` and `ε_p` is the restriction of the homomorphism `φ̃` defined on all of `D_p`.
* The group `Hom(I_p, C_ℓ)^{D_p}` is therefore the only receptacle, and it is *small*:

| `p` | `Hom(I_p, C_ℓ)^{D_p}` | why |
|---|---|---|
| `p ≠ ℓ`, `ℓ ∤ p − 1` | trivial | Frobenius acts on tame inertia by `τ ↦ τ^p`, so `ε(τ)^{p−1} = 1` |
| `p ≠ ℓ`, `ℓ ∣ p − 1` | cyclic of order `ℓ` | tame quotient of `I_p` is `∏_{q≠p} ℤ_q`, so `Hom(I_p, C_ℓ) ≅ C_ℓ` |
| `p = ℓ` | cyclic of order `ℓ` | inflation–restriction: `H¹(D_ℓ, 𝔽_ℓ)` has order `ℓ²`, `H¹(D_ℓ/I_ℓ, 𝔽_ℓ)` order `ℓ`, `H²(Ẑ, 𝔽_ℓ) = 0` |

and in each of the two nontrivial rows the restriction of an explicit **cyclotomic** character is a
generator: the degree-`ℓ` subfield of `ℚ(μ_p)` for `p ≡ 1 mod ℓ` (totally ramified at `p`,
unramified elsewhere), and the degree-`ℓ` subfield of `ℚ(μ_{ℓ²})` for `p = ℓ`. Hence

> **Lemma 2.1.6 over ℚ for `C = C_ℓ` is: `ε := ∏_p χ_p^{a_p}`**, a finite product of cyclotomic
> characters, with the exponents `a_p` read off one prime at a time. **No Kronecker–Weber, no
> reciprocity law, no global idele class group.**

`InverseGalois/CFT/Cyclotomic/OnePrimeRamified.lean` already supplies the characters of the second
row (`exists_cyclic_ramified_exactly_at_one_prime`), and `Cyclotomic/CyclicSubfield.lean` the cyclic
subfields of `ℚ(μ_q)`; the tame row is `TameCharacter.lean` (`tameChar_conj_arithFrobAt`,
`card_inertia_dvd_sub_one`); `Scholz/Tame.lean` already has tame Kronecker–Weber
(`exists_algHom_cyclotomicField_of_isLevel`).

### What genuinely remains

The single irreducible input is the last row of the table, i.e. the **local count at `ℓ`**:

> **(L_ℓ)** `ℚ_ℓ` has exactly `ℓ + 1` cyclic extensions of degree `ℓ`; equivalently
> `|H¹(G_{ℚ_ℓ}, ℤ/ℓ)| = ℓ²`; equivalently every cyclic degree-`ℓ` extension of `ℚ_ℓ` lies in
> `ℚ_ℓ(μ_{ℓ²}) · ℚ_ℓ^{ur}` — **local Kronecker–Weber in exponent `ℓ` at the residue characteristic**.

An elementary route avoiding local class field theory: descend to `E = ℚ_ℓ(μ_ℓ)`, whose degree
`ℓ − 1` over `ℚ_ℓ` is prime to `ℓ`, so `H¹(G_{ℚ_ℓ}, ℤ/ℓ)` is the `ω`-eigenspace of
`E^×/(E^×)^ℓ` for `Δ = Gal(E/ℚ_ℓ)` (Kummer theory plus inflation–restriction). As a `Δ`-module
`E^×/(E^×)^ℓ ≅ 𝔽_ℓ ⊕ μ_ℓ ⊕ 𝔽_ℓ[Δ]` — valuation, roots of unity, and the principal units, the last
by the `ℓ`-adic logarithm on `U¹` — so the `ω`-eigenspace is two-dimensional. The local unit
filtration machinery this needs is already present (`Local/UnitFiltration.lean`, `Local/Exp.lean`,
`Local/ExpEquiv.lean`, `Local/FiltrationHerbrand.lean`).

*Why the wild place cannot be dodged.* `(S_N)` forbids ramification at `ℓ`, and the tame part of
`I_ℓ` has order prime to `ℓ` so maps trivially into the `ℓ`-group `G`; the obstruction is exactly
`φ̃` on **wild** inertia at `ℓ`. The Kummer freedom in the solution (replacing `β` by `βγ`,
`γ ∈ k^×`) only moves the local class at `λ ∣ ℓ` inside the image of `k_λ^×`, which is a proper
subgroup of `(K_λ^×/(K_λ^×)^ℓ)^{D_λ}` in general; and `(S_N)` does *not* require the solution to be
unramified outside `ram(L)` — extra ramification at good primes `q ≡ 1 mod ℓ^N` splitting completely
in `L` is harmless — but no amount of good extra ramification removes a bad one at `ℓ`.


## 0.13 Status (2026-08-25) — the Scholz-side plumbing

Four bricks, all sorry- and axiom-free, all pushed; full build green at 9106 jobs.

**1. The induction contract now carries the order of the quotient.** All three central-step
predicates — `IsCentralStepSolvable`, `IsNonsplitCentralStepSolvable`,
`IsFrattiniCentralStepSolvable` — gained the hypothesis `Nat.card H ∣ ℓ ^ N`.  It is not
cosmetic.  `exists_surjective_hom_of_forall_ramified_primeResidue` demands `ℓ · |D_v| ∣ p − 1` at
every ramified place; `|D_v|` divides `|H|`, and Serre's condition at level `N + 1` supplies only
`ℓ^{N+1} ∣ p − 1`, so without `|H| ∣ ℓ^N` the arithmetic hypothesis of the local–global engine
cannot be met.  The induction is restructured accordingly: with `level(j) = N + (m − j)` along a
central chain of length `m`, step `j → j+1` needs `2j+1 ≤ N+m`, so `m ≤ N+1`;
`isScholzRealizable_of_card_eq_pow_of_le` carries `k ≤ N + 1` and the general
`isScholzRealizable_of_card_eq_pow` realizes at `max N k` and drops back down with
`IsScholzRealizable.mono` (moved into `Scholz/Realization.lean`, since `Scholz/SplitReduction.lean`
imports `Scholz/Induction.lean` and not conversely).  Every externally visible statement, including
all of `InverseGalois/Shafarevich.lean`, is unchanged.

**2. Serre's condition is inherited by subfields** (`Scholz/Condition.lean`):
`isSplitInertia_of_tower`, `IsScholz.of_tower`.  Both halves of `(S_N)` constrain only the ramified
primes; `ramifiedSet_subset` moves the level condition down, and `Ideal.inertiaDeg_algebra_tower`
factors the residue degree through the intermediate field.

**3. Realizations from an abstract field, and from a quotient** (`Scholz/Realization.lean`):
`isScholzRealizable_of_isGalois` embeds any number field satisfying `(S_N)` into
`AlgebraicClosure ℚ` (via `embSubfield`/`embEquiv`) and transports the condition and the group;
`isScholzRealizable_of_surjective` then realizes **every quotient** of the Galois group, by passing
to the fixed field of the kernel.  This is the adapter the central step will finish with: an
embedding-problem solution hands back a big field plus a surjection, not a `ScholzRealization`.

**4. The local groups are cyclic** (`CFT/TameCyclic.lean`, `Scholz/Tame.lean`):
`isCyclic_inertia_of_tame` — the tame character embeds inertia into the units of a finite field, so
tame inertia is cyclic; `isCyclic_stabilizer_of_isSplitInertia` — the residue-degree half of `(S_N)`
identifies the decomposition group with inertia; and the capstone `IsScholz.isCyclic_stabilizer`:
for a field of `ℓ`-power degree satisfying `(S_N)` with `N ≥ 1`, the decomposition group at every
ramified prime is cyclic.  That discharges the first of the three clauses of `hram` in
`exists_surjective_hom_of_forall_ramified_primeResidue`.

**What `hram` still wants**, per place `v` of `K` ramified over the base `k = ℚ(μ_ℓ)`:
(i) `IsCyclic ↥(stabilizer Gal(K/k) v)` — the analogue over `k` of the capstone above;
(ii) the residue field of `K_v` is prime, i.e. every integral element of the completion is
congruent to a rational integer — this follows from residue degree one over `ℚ` but needs the
identification of the residue field of the completion with `𝓞 K / P`;
(iii) `ℓ · |D_v| ∣ p − 1`, which is now available from the level condition plus the new
`Nat.card H ∣ ℓ ^ N` hypothesis.

**Remaining assembly** (Serre's plan): (A) base-change to `k = ℚ(μ_ℓ)` with
`Gal(K₀·k/k) ≅ Gal(K₀/ℚ)` — coprime degrees, so `CFT/Compositum.lean`'s
`galEquivProd (h : A ⊓ B = ⊥)` is the tool; (B) the three clauses above; (C) the character
`χ : ker f → k^×`; (D) `HasProperSolution`; (E) descent to `ℚ` by
`exists_surjective_hom_comp_eq_of_coprime_index`; (F) ramification control by twisting, which needs
the cyclotomic twisting characters of `Cyclotomic/OnePrimeRamified.lean` together with the local
count `(L_ℓ)` of §0.12.

### 0.14 Status (2026-08-25, later) — the local clauses are all discharged at the ℚ level

Step (B) is finished, in the sense that each of the three clauses of `hram` is now a theorem about
the rational prime below the place.

* **(iii) the congruence.** `mul_card_stabilizer_dvd_sub_one` in `Scholz/Condition.lean`: from
  `IsLevel ℓ (N + 1) E` and `Nat.card Gal(E/ℚ) ∣ ℓ ^ N` one gets
  `ℓ * Nat.card ↥(stabilizer Gal(E/ℚ) P) ∣ p - 1` at every ramified `p`.  The decomposition group
  is a subgroup, so its order divides `ℓ ^ N`, and the level condition supplies one more power.
* **(i) cyclic decomposition group.** `IsScholz.isCyclic_stabilizer` in `Scholz/Tame.lean`.
* **(ii) prime residue field and residue characteristic.** The new module
  `Local/PrimeResidueField.lean`.  Residue degree one makes the residue field an extension of the
  prime field of rank one, so `Int.cast : ℤ → 𝓞 K ⧸ P` is surjective
  (`surjective_intCast_quotient_of_inertiaDeg_eq_one`); composing with the approximation lemma
  `exists_algebraMap_sub_le_exp_neg_one` of `Local/AdicResidue.lean` — which already packages the
  density of `K` in `v.adicCompletion K` — gives the predicate the criterion asks for
  (`exists_intCast_sub_lt_one_of_inertiaDeg_eq_one`).  A companion lemma
  `exists_hasResidueChar_of_liesOver` pins the residue characteristic to the *given* rational prime,
  which the existing `exists_hasResidueChar_adicCompletion` of `Local/AdicHerbrand.lean` leaves
  existentially quantified, and `exists_hasResidueChar_and_primeResidue` packages all three in the
  exact `∃ q e, HasResidueChar ∧ prime residue ∧ m ∣ q - 1` shape of
  `exists_surjective_hom_of_forall_ramified_primeResidue`.

**(A) is now the gating item.**  A ℚ-base assembly is impossible in principle: the criterion needs
a primitive `n`-th root of unity in the base, and `n = ℓ`.  So the local clauses have to be
transported from `ℚ` to `k = ℚ(μ_ℓ)`.  The transport should be cheap — clause (ii) is already a
statement about the residue degree of `v` over the rational prime, and clauses (i) and (iii) follow
from `stabilizer Gal(K/k) v ≤ stabilizer Gal(K/ℚ) P`, since a subgroup of a cyclic group is cyclic
and its order divides.  What is not cheap is the base change itself: `Gal(↥(A ⊔ B)/↥B) ≃* Gal(A/ℚ)`
for `A ⊓ B = ⊥` needs an `Algebra ↥B ↥(A ⊔ B)` structure, hence `IntermediateField.extendScalars`
and the attendant `IsScalarTower` pinning.  The group-theoretic content is already available:
`galEquivProd` identifies `Gal(↥(A ⊔ B)/ℚ)` with `Gal(A/ℚ) × Gal(B/ℚ)`, under which the fixing
subgroup of `B` is the first factor.

## 0.15 Status (2026-08-26) — **the central step is unconditional; the odd nilpotent case is done**

The last arithmetic hypothesis of the Scholz–Reichardt induction is gone.  `IsCentralStepSolvable ℓ`
is now a **theorem** for every odd prime `ℓ` (`CFT/Scholz/FrattiniInertiaBound.lean`), so
`InverseGalois/Shafarevich.lean` carries no hypotheses at all.  Full build green at **9165 jobs**,
zero errors, zero warnings, zero sorries and zero axioms outside the comparator.

Unconditionally over `ℚ`:

* `InverseGalois.isInverseGalois_of_isPGroup_odd` — every finite `ℓ`-group, `ℓ` an odd prime;
* `InverseGalois.isInverseGalois_of_isNilpotent_of_odd` — every finite nilpotent group of odd order;
* `InverseGalois.isInverseGalois_of_isNilpotent_of_semiabelian_sylow_two` — every finite nilpotent
  group whose Sylow `2`-subgroups are semiabelian, hence
  `..._of_not_dvd_thirtytwo` / `..._of_not_dvd_sixteen`.

### The chain that closed it

The induction needed, at a prime `P` over `ℓ` of an `ℓ`-extension `A/ℚ`, that a solution of the
central embedding problem be a *power of one fixed character* on the inertia subgroup.  That is the
rank one condition, and it was reduced in three steps.

**Step 1 — rank one from cyclicity** (`Scholz/AbelianInertia.lean`, `Scholz/InertiaRankOne.lean`).
The values of the solution on inertia are central, so the solution factors through the abelianized
decomposition group `D^ab`; there it suffices that the image `I^ab` of inertia be *cyclic*.

**Step 2 — cyclicity from a small Frattini quotient** (`Scholz/FrattiniInertia.lean`).  `I^ab` is
generated by what it contributes to `D^ab/(D^ab)^ℓ` together with `ℓ`-th powers, and `D/I` is cyclic
of order the residue degree.  If the Frattini image of inertia has order at most `ℓ` **and** `D/I`
is large enough — order divisible by the exponent of `Gal(A/ℚ)` — then `D` is generated by one
element together with `I`, and `I^ab` comes out cyclic.  Largeness is not automatic but is bought:
adjoin a cyclic extension of degree `ℓ^n` in which `ℓ` is *inert*, which forces the residue degree
up, and then bring cyclicity back down with `Scholz/AbelianInertiaTransport.lean`, which moves
`I^ab` along any homomorphism carrying decomposition into decomposition and inertia **onto** inertia
(restriction to a normal subextension, and isomorphism of number fields, are both of this shape).
This is the predicate `IsFrattiniInertiaSmallAt ℓ`.

**Step 3 — the Frattini bound itself** (`Scholz/FrattiniInertiaSmall.lean`, the substantial one).
Work in a field `N` containing a primitive `ℓ`-th root of unity `ζ`, at a prime `W ∣ ℓ`.  Let
`ρ : Gal(N/ℚ) → (ZMod ℓ)ˣ` be the mod `ℓ` cyclotomic character, `S` the decomposition group of `W`,
`H = S ⊓ ker ρ` and `F = fixedField H`.  `F` is *not* normal over `ℚ`, which is the reason the file
carries its own glue (`fixedFieldAut`, `mem_inertia_fixedFieldHom`, …).  The master identity of
`Scholz/FixedFieldRamification.lean` — the ramification index times the residue degree of the prime
below a fixed field is the index of the intersection of the decomposition group with the subgroup —
gives `e · f = |ρ(S)| ≤ ℓ − 1` at the place of `F` below `W`.  Since `ζ − 1` divides `ℓ` to depth
`ℓ − 1`, that bound *pins* both invariants: `e = ℓ − 1`, `f = 1`
(`Kummer/RamifiedCyclotomicPlace.lean`).  In particular `ρ(S) = ⊤`, so some `τ ∈ S` sends `ζ` to
`ζ^g` with `g` a primitive root mod `ℓ`; such a `τ` normalises `H` and so descends to an
automorphism `δ` of `F` fixing the place.  That is exactly the abstract local datum
`IsCyclotomicPlace` of `Kummer/CyclotomicPlace.lean`, whose consequence
`inertia_character_dependent` says: two `ZMod ℓ`-valued characters of `Gal(N/F)` invariant under
conjugation by `τ` are *dependent on inertia*.  Conjugation invariance is free for characters pulled
back from an abelian target containing the image of `τ`.  Transporting the dichotomy along a
homomorphism `f : Gal(N/ℚ) → G` carrying `S` into `D` and inertia **onto** an `ℓ`-subgroup `I`
bounds the image of `I` in `D^ab/(D^ab)^ℓ` by `ℓ`; the missing `(ℓ − 1)`-st roots needed to run the
transfer are supplied by `powCoprime`, using `gcd(ℓ, ℓ − 1) = 1` and the fact that `I` is an
`ℓ`-group.

**Removing the root of unity** (`Scholz/FrattiniInertiaBound.lean`).  An `ℓ`-extension of `ℚ` with
`ℓ` odd contains no `ζ_ℓ`, so Step 3 does not apply directly to `A`.  Pass to `M = A ⊔ ℚ(μ_ℓ)`.
`M` is no longer an `ℓ`-extension — and that is fine, because Step 3 only asks that the *image of
inertia* be an `ℓ`-group, which it is, being a subgroup of `Gal(A/ℚ)`.  With
`f = autCongr eA ∘ restrictNormalHom A₀` for a copy `A₀ ≅ A` inside `M`, `map_inertia_eq_inertia`
supplies the surjectivity onto inertia and `restrictNormal_mem_stabilizer` the containment of
decomposition groups.  Hence `IsFrattiniInertiaSmallAt ℓ`, hence `IsAbelianInertiaCyclicAt ℓ`, hence
`IsInertiaRankOneAt ℓ`, hence `IsCentralStepSolvable ℓ`.

### What remains for full Shafarevich

Exactly two things, and only the second is a wall.

1. **The prime `2` in the nilpotent case.**  Handled today by the geometric (Dentzer–Stoll) route,
   which reaches the semiabelian `2`-groups.  By Kida (2024) the smallest non-semiabelian `2`-group
   has order `64`, so geometry alone can never finish it; the fix is to extend Scholz–Reichardt to
   `ℓ = 2`, where the argument above genuinely breaks (`ζ_2 = −1` lies in every field, `ρ` is
   trivial, and `ℓ − 1 = 1` gives no room).  Mapped out in §0.16, whose first brick is landed.
2. **From nilpotent to solvable.**  `Shafarevich.isSolvable_isInverseGalois_of_splitPrimePowerEP`
   already reduces everything to a *split* embedding problem with `p`-group kernel, and the
   nilpotent realizations above are not of that shape: filtering a `p`-group kernel leaves a
   residual non-split lifting.  The genuine Shafarevich argument uses Ikeda plus a Grunwald–Wang
   input.  *(Superseded in part by §0.24: the power-class form of Grunwald–Wang, squarefree
   exponent, is now in the repo; the character form and Poitou–Tate are not.)*

---

## 0.16 Status (2026-08-26, later) — mapping the prime `2`, and the first brick

Landed: **the whole local–global layer now works at every prime**, `2` included.

### Where oddness actually sat

Tracing `Odd ℓ` down from `exists_surjective_hom_of_forall_ramified_primeResidue`
(`CFT/Kummer/CentralEmbedding.lean`) through `ABHNRamified` → `ABHNLocalPower` → `ABHNCoboundary`
→ `ABHNTorsion` shows it is consumed in **exactly one line** of the whole chain, at the archimedean
places:

```lean
have hcop : Nat.Coprime (Nat.card ↥(stabilizer Gal(K/k) w)) n := by
  rcases InfinitePlace.nat_card_stabilizer_eq_one_or_two k w with h | h
  ...
  · rw [h]; exact Nat.coprime_two_left.mpr hn
```

Everything else — the unramified finite places, the ramified ones, the Kummer bookkeeping, the
Frattini argument — never looks at the parity of `ℓ`.

That line is now the predicate `InverseGalois.CFT.IsCoprimeAtInfinitePlaces k K n`, and it has a
second source besides oddness: `IsCoprimeAtInfinitePlaces.of_isUnramifiedAtInfinitePlaces`, which
applies whenever no archimedean place of `K` ramifies over `k` — over `ℚ`, whenever `K` is totally
real.  The chain is restated over the predicate, with the old `_of_odd` statements kept as
corollaries, so:

> **At `ℓ = 2` the Albert–Brauer–Hasse–Noether reduction, and with it the solvability of a central
> Frattini embedding problem with kernel of order `2`, holds verbatim for a totally real base.**

### What the rest of the `ℓ = 2` argument needs

The induction hypothesis has to carry *totally real* alongside the Scholz condition.  That is not a
burden — for odd `ℓ` it is automatic, an odd-degree Galois extension of `ℚ` having no element of
order `2` to act as complex conjugation — and at `ℓ = 2` it is exactly what buys the archimedean
places back.  With `K/ℚ` totally real and unramified at `2`:

* **the local problem at `2` is always solvable unramified.**  `K/ℚ` unramified at `2` makes the
  decomposition group `D₂ ⊆ G` cyclic of `2`-power order `f`.  Its preimage in `G̃` is a central
  extension of a cyclic group by `ℤ/2`, hence abelian, hence either cyclic of order `2f` — solved by
  the unramified extension of that degree — or split, and then the splitting composed with
  `Ẑ ↠ ℤ/f` solves it, again unramified.
* **the local problem at `∞` is trivially solvable**, the decomposition group being trivial.
* **the ramified finite places are unchanged**: `2 · |D_v| ∣ p − 1` is the same Scholz congruence as
  before, with `ℓ = 2`.

So a global solution exists.  The work is in *correcting* it, and there the two things that break
are known precisely.

1. **`RadicalDisjoint` / `NilpotentRadical` are false at `2`.**  `not_surjective_of_radical` rests on
   an automorphism sending `ζ ↦ ζ²`, which for `ℓ = 2` is the identity on `ζ = −1`; and the
   statement itself fails, `2` being a square in the totally real `2`-extension `ℚ(√2)`.  Its one
   use is `Scholz/AuxPrimeChoice.lean:70`, to know that the radicand `m` — a product of primes
   already ramified in `A` — is not an `ℓ`-th power in `A`, so that Chebotarev can find a prime `q`
   splitting completely in `A` with `m` a non-residue.  A ramification argument does *not* rescue
   this: `ℚ(√m)` ramifies exactly where `A` does.  What is true at `2` is sharper and turns it into
   a counting problem: `m` is a square in `A` iff `ℚ(√m) ⊆ A`, so the bad radicands form a subgroup
   of `ℚ^×/(ℚ^×)²` of order `2^{d(G)}`, `d(G)` the minimal number of generators of `G = Gal(A/ℚ)`,
   spanned by the quadratic subfields of `A`.  The correction must choose `m` inside the residue
   span and outside that finite subgroup, which is a dimension count against
   `Scholz/ResidueSpan.lean` rather than a new theorem about radicals.
2. **The correcting characters are short by one dimension at `2` and `∞`.**  Write the defect of a
   solution at a place `v` as a class in `ℚ_v^×/(ℚ_v^×)²`.  The correctors allowed by the Scholz
   condition are `ℚ(√d)` with `d = ± 2^a ∏ pᵢ^{bᵢ} q`, where the `pᵢ` are already ramified and
   `q ≡ 1 mod 2^N` is the new auxiliary prime.  Every odd factor is `≡ 1 mod 8`, hence a square in
   `ℚ₂`, so the class of `d` at `2` is `(−1)^s 2^a` and its sign is `(−1)^s`: the *same* `s`.  The
   pair (class at `2` mod unramified, sign) therefore ranges over an index-two subgroup of
   `(ℤ/2)² × ℤ/2`, and the defect must satisfy the one relation
   `(−1)`-component of the defect at `2` `=` defect at `∞`.

Item 2 is the classical `ℓ = 2` difficulty — the same place where Šafarevič's 1954 argument had its
gap — and is what a formalization has to supply, presumably from Hilbert reciprocity applied to the
defect.  Item 1 is routine.

### Item 2 in the repository's own language: `IsInertiaRankOneAt 2` is false

Item 2 is not a stylistic obstacle; it is a *false hypothesis*, and the repository already names it.
`Scholz/InertiaRankOne.lean` defines

```lean
def IsInertiaRankOneAt (ℓ : ℕ) : Prop := ...   -- at a place over `ℓ`, every homomorphism of order
                                               -- dividing `ℓ` on inertia is a power of one fixed
                                               -- surjective one
```

and `Scholz/FrattiniInertiaBound.lean` proves `isInertiaRankOneAt (hℓ : ℓ.Prime) (hodd : Odd ℓ)`.
The oddness there is *not* removable, because the statement itself fails at `2`.  The abelianized
inertia subgroup of `ℚ₂` is `ℤ₂^×  ≅ ℤ/2 × ℤ₂`, so its quotient by squares is `(ℤ/2)²`: there are
**three** distinct ramified quadratic characters of `ℚ₂`, cut out by `ℚ₂(√−1)`, `ℚ₂(√2)` and
`ℚ₂(√−2)`, and no one of them is a power of another.  Inertia at `2` has rank **two**, not one.
For odd `ℓ` the corresponding group is `ℤ_ℓ^× ≅ ℤ/(ℓ−1) × ℤ_ℓ`, whose quotient by `ℓ`-th powers is
cyclic of order `ℓ`, generated by the cyclotomic character of conductor `ℓ²` — which is exactly the
generator `FrattiniInertiaSmall.lean` produces from a primitive root modulo `ℓ`, and `(ZMod 2)ˣ` is
trivial so there is no primitive root to produce.

This is the same count as item 2, seen locally instead of globally, and it says what the `ℓ = 2`
theorem has to look like.  The correct statement is not rank one at `2`; it is rank one at the pair
of places `{2, ∞}` *jointly*.  The two counts line up exactly:

| | rank of the target | rank of the correctors |
|---|---|---|
| place `2`, mod unramified | `2`  (`{1, −1, 2, −2}`) | |
| place `∞` | `1`  (the sign) | |
| **total** | **3** | **2**  (`−1` and `2`, the sign being tied to the `−1`) |

So the deficiency is exactly one dimension, and the missing input is one relation between the defect
at `2` and the defect at `∞` of a *global* solution.  A purely local lemma cannot supply it; the only
source is reciprocity, and in the standard treatments (Neukirch–Schmidt–Wingberg IX §6) it arrives as
Poitou–Tate duality: the collection of local defects is correctable by a global quadratic character
exactly when it annihilates the dual Selmer group, and the auxiliary prime `q` is chosen to shrink
that dual Selmer group.  What `q` cannot kill are the classes `d` with `ℚ(√d) ⊆ A` — `q` splits
completely in `A`, so such a `d` stays a square at `q` — and those are precisely the classes item 1
also has to avoid.  Items 1 and 2 are therefore two readings of a single dimension count against the
quadratic subfields of `A`.

Poitou–Tate duality is in neither Mathlib nor this repository.  Global reciprocity, on the other
hand, *is* here in the degree-two case that item 2 needs — see §0.17, which turns item 2 into a
theorem.  The same layer is what gap 2 (nilpotent → solvable) needs for Grunwald–Wang, so the two
remaining gaps share their next prerequisite; see §0.10 for how far the idele-class-group side has
got.

---

## 0.17 Status (2026-08-26, later still) — item 2 is a theorem, and it is Hilbert reciprocity

§0.16 item 2 predicted that the correctors allowed by the Scholz condition satisfy **one relation**
between their defect at `2` and their defect at `∞`, and guessed that the relation would have to
come from reciprocity.  Both are now settled, and the reciprocity in question is the ordinary
Hilbert product formula over `ℚ`, which the repository has had since
`InverseGalois/CFT/Global/Reciprocity.lean`.  No Poitou–Tate duality is involved.

The `(−1)`-component of a class in `ℚ₂^×/(ℚ₂^×)²` — the component that the quadratic extension
`ℚ₂(i)` cuts out — is the Hilbert symbol `(−1, ·)₂`, and the defect at `∞` is the sign.  So the
predicted relation is the identity `(−1, d)₂ = sign(d)`, and `Global/NegOneSymbol.lean` proves it
for exactly the integers the Scholz condition produces:

```lean
InverseGalois.CFT.hilbertSymbolAt_neg_one_eq_one_of_one_mod_four {p : Nat.Primes}
    (hp : (p : ℕ) % 4 = 1) {d : ℚ} (hd : d ≠ 0) :
  hilbertSymbolAt p (-1) d = 1

InverseGalois.CFT.hilbertSymbolAt_two_neg_one_intCast {d : ℤ} (hd : d ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ d → p % 4 = 1) :
  hilbertSymbolAt primeTwo (-1) ((d : ℚ)) = if d < 0 then -1 else 1
```

The first is the local input: at a prime congruent to one modulo four, `−1` is a square, so its
symbol against anything is trivial.  The second reads the product formula backwards — the product
of the local symbols of `(−1, d)` over all places is one, every odd place contributes `1`, so the
dyadic symbol is the reciprocal of the real one, which is the sign.  The corollary is item 2 as a
formal statement:

```lean
InverseGalois.CFT.hilbertSymbolAt_two_neg_one_ne_neg_one_of_pos {d : ℤ} (hd : 0 < d)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ d → p % 4 = 1) :
  hilbertSymbolAt primeTwo (-1) ((d : ℚ)) ≠ -1
```

A Scholz-admissible corrector at level `N ≥ 2` is `d = ± 2^a ∏ pᵢ^{bᵢ} q` with every odd factor
congruent to `1` modulo `2^N`, hence to `1` modulo `4`; the hypothesis of the corollary is exactly
that.  So the pair (dyadic defect, real defect) attainable by a corrector is confined to the
index-two subgroup `{(0,+), (α,−), (β,+), (αβ,−)}` of the rank-three target, `α` the class of `−1`
and `β` the class of `2`, precisely as the table in §0.16 predicted.  The prediction is no longer a
count on paper; it is a theorem, and it is sharp.

### The escape, and what it costs

The same product formula says where the missing generator lives.  For an odd prime `q`,

```lean
InverseGalois.CFT.hilbertSymbolAt_two_neg_one_prime_of_three_mod_four {q : ℕ} (hq : q.Prime)
    (hq4 : q % 4 = 3) :
  hilbertSymbolAt primeTwo (-1) ((q : ℚ)) = -1
```

and `q > 0`, so `q` realizes the pair `(α, +)` that no admissible corrector can.  The deficiency is
therefore **caused by the level condition itself**: it is the congruence `q ≡ 1 mod 2^N` on the
auxiliary prime, not anything about the prime `2`, that removes the missing dimension.  Admitting a
single auxiliary prime `q ≡ 3 mod 4` restores it.

That is not free, and the price is worth stating plainly.

* `ℚ(√q)` with `q ≡ 3 mod 4` has discriminant `4q`, so it **ramifies at `2`**.  This is not an
  accident of the choice: `(−1, d)₂ = −1` forces `ℚ₂(√d)/ℚ₂` to be ramified, so *any* corrector that
  moves the dyadic defect ramifies at `2`.  The induction invariant of §0.16 — `K/ℚ` totally real
  and unramified at `2`, which is what buys back the archimedean places in
  `IsCoprimeAtInfinitePlaces` and makes the local problem at `2` solvable unramified — cannot be
  literally preserved across such a correction.  It has to be replaced by a bounded-dyadic-conductor
  invariant.
* `q ≡ 3 mod 4` violates the level congruence at `q` itself, so the next stage of the induction sees
  a ramified prime that is not `≡ 1 mod 2^N`.  The Scholz congruence at a ramified place is what
  makes the *local* embedding problem there solvable, so relaxing it at `q` has to be paid for at
  the following step.

Both costs are about the design of the induction invariant at `ℓ = 2`, not about a missing theorem.
That is a real change of shape in the argument, and it is where the `ℓ = 2` work now sits; but the
arithmetic input that §0.16 identified as the wall — one relation, from reciprocity, tying the
dyadic defect to the real one — is supplied and proved.

---

## 0.18 Status (2026-08-26, night) — Albert–Brauer–Hasse–Noether with **no** condition at infinity

§0.16 located the whole of `Odd ℓ` in one line, at the archimedean places, and gave it a name:
`IsCoprimeAtInfinitePlaces k K n`.  At `n = 2` that predicate says every archimedean place of `K` is
unramified over `k`, i.e. over `ℚ` that `K` is totally real.  §0.17 then showed that the totally
real-and-unramified-at-`2` invariant **cannot** be carried through the correction step: any
corrector that moves the dyadic defect ramifies at `2`, and the corrector that supplies the missing
dimension is `ℚ(√q)` with `q ≡ 3 mod 4`, which ramifies at `2` and breaks the level congruence.

The way out is not to preserve the invariant but to make the theorem not need it.  That is now
done.

### The theorem

```lean
InverseGalois.CFT.exists_isMulCoboundary_of_sq_eq_neg_one
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K]
    {ι : K} (hι : ι ^ 2 = -1) {n : ℕ} (hn : n ≠ 0)
    {a : Gal(K/ℚ) → Gal(K/ℚ) → ℚˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha  : ∀ x y z, a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
              «a is a coboundary in (v.adicCompletion K)ˣ over the decomposition group at v») :
  ∃ b : Gal(K/ℚ) → Kˣ, ∀ g h, g • b h / b (g * h) * b g = Units.map (algebraMap ℚ K) (a g h)
```

No hypothesis at the archimedean places, and **no parity condition on `n`**.  The single price is
`ι ∈ K` with `ι² = −1`.

### How it is proved

Let `Γ = Gal(K/ℚ)` and `N = stabilizer Γ ι`.  Because `σ ι ∈ {ι, −ι}` for every `σ`, `N` is normal
of index two (index exactly two, `ι ∉ ℚ`), and its fixed field `F` contains `ι`, hence is **totally
complex**, hence `IsUnramifiedAtInfinitePlaces F K` holds vacuously — there is no real place of `F`
left to ramify.

1. **Restriction.**  Base change along `AlgEquiv.restrictScalars` from `ℚ` to `F` is definitionally
   free: the action on `HeightOneSpectrum (𝓞 K)`, `adicCompletionAut`, `globalUnitsAut` and
   `smulUnitsAut` all transport by `rfl` (`Units/BaseChangeCocycle.lean`).  So the existing
   Albert–Brauer–Hasse–Noether theorem, applied over `F`, trivialises `a|_{N×N}`.
2. **Inflation.**  A two-cocycle whose restriction to an index-two subgroup is a coboundary equals,
   after twisting by the coboundary of a one-cochain, the *inflation* of a single invariant element
   `c ∈ Kˣ` (`GroupCohomology/IndexTwo.lean`, `exists_twist_eq_indexTwoInflation`; the
   `H¹(N, Kˣ) = 1` input is Hilbert 90 for the subgroup, `SubgroupHilbert90.lean`).  Twisting does
   not disturb the local hypotheses (`Units/LocalCoboundaryTwist.lean`), so the local data descends
   to the inflated cocycle.
3. **Locally a sum of two squares.**  The inflation of `c` is a coboundary over the decomposition
   group at `v` exactly when `c` is a norm from `K_v` for the quadratic subextension cut out by
   `ι`, i.e. when `c` is a **sum of two squares** in the completion of `ℚ` under `v`
   (`Units/LocalSqrtNegOne.lean`).  Being `Γ`-invariant, `c` is a rational number.
4. **Globally a sum of two squares.**  A rational number which is a sum of two squares in every
   `ℚ_p` is a sum of two squares (`Units/RatSumSquares.lean`), by the Hasse norm theorem for
   `ℚ(i)/ℚ` — and the real place costs nothing, a sum of two squares in a single completion being
   already positive.  So `c = x² + y² = N(x + y ι)`, and the inflation of `c` is a coboundary
   globally (`SqrtNegOne.lean`, `isMulCoboundary₂_indexTwoInflation`).
5. Undo the twist.

### Modules

| file | content |
|---|---|
| `CFT/SqrtNegOne.lean` | the stabiliser of a square root of `−1` is normal of index two; its fixed field is totally complex; `σ f · f = x² + y²` |
| `CFT/SubgroupHilbert90.lean` | Hilbert 90 for a subgroup acting on `Kˣ` |
| `CFT/GroupCohomology/Inflation.lean` | inflation of a two-cocycle along a quotient |
| `CFT/GroupCohomology/IndexTwo.lean` | twist, `indexTwoInflation`, and the reduction of an index-two-split cocycle to it |
| `CFT/Units/BaseChangeCocycle.lean` | `restrictScalars` transports every ingredient by `rfl` |
| `CFT/Units/ABHNArchimedean.lean` | the archimedean clause is vacuous over a totally complex base |
| `CFT/Units/LocalSqrtNegOne.lean` | the local coboundary condition ⇔ locally a sum of two squares |
| `CFT/Units/LocalCoboundaryTwist.lean` | twisting preserves local triviality |
| `CFT/Units/RatSumSquares.lean` | everywhere-locally a sum of two squares ⇒ a sum of two squares |
| `CFT/Units/ABHNSqrtNegOne.lean` | the assembly |
| `CFT/Units/ABHNSqrtNegOneRamified.lean` | the same with the ramified places in the form the construction verifies |
| `CFT/Kummer/CentralEmbeddingSqrtNegOne.lean` | the four embedding-problem criteria over such a base, plus a mixed one |

All sorry-free and axiom-free; full build green.

### What this buys, and what it does not

**Buys.**  The induction invariant at `ℓ = 2` no longer has to be *totally real*.  It can be
`ι ∈ K` — an invariant which is preserved by *every* enlargement of `K`, in particular by every
corrector, including `ℚ(√q)` with `q ≡ 3 mod 4`.  The obstruction §0.17 identified as a change of
shape in the argument is removed at the source: the archimedean places are simply no longer part of
the criterion.  Concretely,

```lean
InverseGalois.CFT.exists_surjective_hom_rat_of_forall_ramified_primeResidue
```

is the exact analogue of `exists_surjective_hom_of_forall_ramified_primeResidue` with `Odd n`
deleted and `ι² = −1` in its place.

**Does not buy.**  Requiring `ι ∈ K` makes the place above `2` **ramified**, and at a ramified place
the criterion asks for something.  The residue-characteristic congruence `n · |D_v| ∣ p − 1` is
unsatisfiable at `p = 2`, so the place above `2` has to be discharged the other way — by a
homomorphic lift of `π|_{D_v}` into `G`.  Hence the mixed criterion

```lean
InverseGalois.CFT.exists_surjective_hom_rat_of_forall_ramified_lift_or_primeResidue
```

which asks, at each ramified place, for *either* a lift *or* the congruence.  The Scholz primes
supply the congruence; the place above `2` must supply a lift.

### What the `ℓ = 2` argument now needs

Exactly one arithmetic statement, and it is purely local:

> Let `K/ℚ` be a `2`-extension containing `i`, `v` the place above `2`, `D = D_v ⊆ Gal(K/ℚ)` its
> decomposition group, and `1 → ℤ/2 → G̃ → D → 1` the pullback of the central extension along the
> inclusion.  Then the surjection `G_{ℚ₂} ↠ D` lifts to `G̃`.

Equivalently: the local obstruction in `H²(G_{ℚ₂}, ℤ/2) ≅ Br(ℚ₂)[2] ≅ ℤ/2` vanishes.  It is **not**
automatic — that group is not zero — so this is a genuine condition on the tower, and the right
formulation is a condition on the dyadic behaviour of `K` that the induction can carry (for instance
that `K_v/ℚ₂` be *cyclic*, which makes `G̃_v` abelian and the lift a matter of choosing an
unramified or split extension, as in the second bullet of §0.16).

§0.19 works that condition out, finds that it **fails** in the base case, and concludes that
`ι ∈ K` is not the `ℓ = 2` route after all.  The theorem stands; the route does not.

---

## 0.19 Status (2026-08-26, night, later) — the place `2` is silent when it is unramified, and that is the whole trade

§0.18 built a real theorem and then drew the wrong strategic conclusion from it.  This section
corrects the conclusion, computes the condition §0.18 left open (it is **false** in the smallest
case), and states the one trade that the `ℓ = 2` induction actually faces.

### Three corrections to §0.18

1. **`ℚ(√q)` with `q ≡ 3 mod 4` is real.**  `q > 0`, so that corrector is a real quadratic field and
   does not break total reality.  The two costs §0.17 records are the correct ones: it ramifies at
   `2`, and it violates the level congruence at `q`.
2. **The criterion asks nothing at an unramified place.**  In this repository the local hypothesis
   of Albert–Brauer–Hasse–Noether ranges over the *ramified* finite places only, because
   `exists_sub_add_eq_adicUnits_of_nsmul_eq_zero` (`Units/ABHNTorsion.lean`) discharges every
   unramified finite place for a torsion cocycle, and `exists_sub_add_eq_infiniteUnits_of_coprime`
   discharges the archimedean ones.  So under §0.16's invariant — `K/ℚ` totally real and unramified
   at `2` — the prime `2` costs **nothing at all**.  That is the mechanism behind §0.16's first
   bullet, and it is already a theorem here.
3. **`ι ∈ K` therefore does not remove an obstruction; it creates one.**  Requiring `ι ∈ K` makes
   the place above `2` ramified, and that is the only reason the criterion asks anything there.

### The condition at `2` under `ι ∈ K`, computed

Base case `K = ℚ(i)`, `v | 2`, `D_v = Gal(ℚ₂(i)/ℚ₂)` cyclic of order two, `n = 2`, values in
`{±1}`.  For a cyclic decomposition group the second cohomology of the local units is the invariants
modulo the norms, so the local condition is that `−1` be a norm from `ℚ₂(i)^×`, i.e. a sum of two
squares in `ℚ₂`, i.e. that the Hilbert symbol `(−1, −1)₂` be trivial.  It is not, and the
repository already proves it: `hilbertSymbolAt_two_neg_one_intCast` at `d = −1` (no odd prime
divides `−1`, so the hypothesis is vacuous) gives `hilbertSymbolAt primeTwo (-1) (-1) = -1`.

So at `v | 2` neither the power form, nor the sharper norm form of `Units/ABHNLocalNorm.lean`, nor a
homomorphic lift `D_v →* G` can discharge a cocycle whose value `−1` occurs.  The condition §0.18
posted as "the whole remaining `ℓ = 2` arithmetic" is not merely unproven — it is **false** for the
smallest instance, and it has to be, because the embedding problem `ℤ/4 ↠ ℤ/2 = Gal(ℚ(i)/ℚ)` is
genuinely unsolvable: `ℚ(√d)` lies in a cyclic quartic field exactly when `d` is a sum of two
squares, and `−1` is not.  Its obstruction is the class `(−1, −1)`, ramified at exactly `{2, ∞}`.
Dropping the archimedean condition without adding one at `2` would prove that false statement.

### Why the place `2` cannot simply be omitted

The sum of the local invariants of a class of `Br(K/ℚ)` is zero, so a place may be omitted from the
hypotheses exactly when at most one invariant is left unknown.

| invariant at | `K` totally real | `ι ∈ K` |
|---|---|---|
| `∞` | `0`, the decomposition group being trivial | unknown |
| unramified finite | `0` | `0` |
| Scholz primes | `0`, by the congruence | `0`, by the congruence |
| `2` | ? | ? |

Totally real leaves one unknown and reciprocity determines it.  `ι ∈ K` leaves two unknowns and one
relation, and nothing follows.  This is §0.16's rank count again, read off the Brauer group instead
of off the square classes.

### The trade, stated once

At `ℓ = 2` the induction has exactly two shapes, differing in one bit: whether `2` may ramify.

**(a) `2` unramified** — the §0.16 invariant.  The local–global step needs nothing at `2`.  The
price is the corrector count: the defect has rank three (the dyadic class modulo the unramified one,
rank two; the sign, rank one) and the admissible correctors reach only an index-two subgroup of it
(§0.17, and its local avatar is that `IsInertiaRankOneAt 2` is false).  Deficiency one.  Closing it
needs either a corrector ramified at `2` — which contradicts the invariant — or a relation on the
*defect* matching the one §0.17 proves for the *correctors*.  This is the classical difficulty; its
shape is the special case of Grunwald–Wang at `2`, and it is where Šafarevič's 1954 argument went
wrong.

**(b) `2` allowed to ramify** — invariant: `K/ℚ` Galois, totally real, ramified only at `2` and at
Scholz primes.  Now nothing needs correcting at `2`: `IsInertiaRankOneAt 2` is never invoked, the
rank-three target collapses to the sign alone, and `ℚ(i)`, `ℚ(√2)`, `ℚ(√−2)` become admissible
correctors, so the sign is freely correctable.  Correction at the *odd* ramified primes is the tame
case and is unchanged.  The price is a single missing theorem, and it is a clean one.

> **(T5)**  Let `K/ℚ` be a totally real Galois number field and `a` a two-cocycle of `Gal(K/ℚ)` with
> values in `ℚˣ`, killed by `n`.  If `a` is a coboundary over the decomposition group at every
> ramified finite place **except those above one fixed prime**, then `a` is a coboundary.

Its proof is the reciprocity law for the Brauer group — the sum of the local invariants of a class
split by `K` is zero — together with injectivity of the local invariant on `Br(K_v/ℚ_v)`.  The
repository has the degree-two case over `ℚ`, the Hilbert product formula in
`Global/Reciprocity.lean`, but not the invariant map; that is the next step of the class-field-theory
tower already under construction (§0.10, the second inequality).

**(b) is the better trade.**  (a) asks for exactly the input the classical argument got wrong.  (b)
asks for a standard piece of class field theory which is on the critical path for gap 2 anyway —
Grunwald–Wang, for the nilpotent-to-solvable reduction, needs the same layer.  The recommendation is
to stop trying to move the archimedean place and to build the invariant map.

### What this changes in the repository

Nothing is retracted.  The theorem of §0.18 is true, sorry-free and axiom-free, and it is the right
statement of Albert–Brauer–Hasse–Noether over a base containing `i`; it is simply not the `ℓ = 2`
route.  The sharpening in `Units/ABHNLocalNorm.lean` — at a ramified place with cyclic decomposition
group the local condition is that the values be **norms**, not powers, since the second cohomology
of a cyclic group is its invariants modulo its norms — is the form (T5) will be phrased against, and
it is what makes the computation above a one-line consequence of the Hilbert symbol.

---

## 0.20 Status (2026-08-26, late) — the second inequality is *done*; the wall is reciprocity alone

### What is already in the repository, and was not recorded above

A survey of the class-field-theory layer turns up two theorems that §0.10 and §0.19 still describe
as future work.  They are complete, sorry-free, and in the default build.

* **The second inequality, in every degree.**  `Kummer/CyclotomicDescent.lean` proves
  `index_ideleDiag_sup_ideleNorm_eq_of_prime_degree` — for an extension of prime degree `p`,
  `[J_k : k^× N(J_L)] = p` — by adjoining a `p`-th root of unity to the ambient algebraically closed
  field and descending.  `Kummer/CyclicIndex.lean` then climbs the cyclic tower and lands
  `index_ideleDiag_sup_ideleNorm_eq_card` and `index_ideleDiag_sup_ideleNorm_eq_finrank`: for any
  **cyclic** extension of number fields the idele-class norm index is the degree.
* **The Hasse norm theorem for cyclic extensions.**  `Units/HasseNorm.lean` combines that with the
  first inequality and Hilbert 90 for the idele classes to prove
  `card_tateHm1_ideleClassAut_eq_one` (`Ĥ⁻¹(G, C_K) = 0`) and
  `mem_normSubgroup_of_mem_range_ideleNorm`: an element of `k` which is everywhere locally a norm
  from a cyclic `L/k` is a global norm.

Together with the local computations of `Local/NormIndex.lean` (`card_tateH0_adicUnitsField`,
`subsingleton_tateHm1_adicUnitsField`) this means the **class field axiom is verified in the
repository, locally and globally**: for a cyclic extension, `Ĥ⁰` has order the degree and `Ĥ⁻¹`
vanishes, on the multiplicative group locally and on the idele class group globally.  In Neukirch's
abstract formulation that is the entire input to class field theory *except* the invariant map.

### The single remaining wall

Everything left in the Shafarevich programme funnels through **global Artin reciprocity**, i.e. the
invariant map `inv_v : Br(k_v) → ℚ/ℤ` together with `Σ_v inv_v = 0`:

* gap 1 (`ℓ = 2` Scholz–Reichardt) needs (T5), which *is* `Σ inv_v = 0` plus injectivity of one
  local `inv_v`;
* gap 2 (`ElementaryAbelianKernelEP`) needs Grunwald–Wang, which needs the same layer.

The second inequality is no longer the frontier; it is behind us.

### Four shortcuts to (T5), and why each fails

These were examined and ruled out.  Recording them so they are not re-attempted.

1. **Counting.**  Both available counts fix only the *order* of the relevant subgroup, never which
   subgroup it is.  `|Br(K/k)| = n` against `|⊕_v Br(K_w/k_v)| = ∏ n_v` says the kernel of `Σ inv`
   has order `∏ n_v / n`; `[J : k^× N(J_K)] = n` against `[D_{v₀} : N] = n_{v₀}` says the same thing
   in idele language.  Reciprocity is precisely the identification of the subgroup, so no count can
   replace it.
2. **Correcting by the quaternion class `(−1,−1)_ℚ`.**  That class is ramified exactly at `{2, ∞}`,
   so multiplying by it exchanges an unknown at `2` for an unknown at `∞`: it proves
   `(T5)@2 ⟺ (T5)@∞`, and nothing more.
3. **Quaternion symbols.**  `Σ inv_v = 0` *is* available for symbol classes — that is the Hilbert
   product formula, already proven in `Global/Reciprocity.lean` — and it is additive, so a *product*
   of symbols would suffice.  But this needs `Br(ℚ)[2]` to be generated by quaternion classes, i.e.
   index = exponent over `ℚ` (class field theory) or Merkurjev's theorem (harder), plus
   `Br(ℚ_p)[2] ≅ ℤ/2` (local class field theory).  Circular.
4. **Brauer induction.**  At `p = 2` every subgroup of a `2`-group is "elementary", so induction from
   elementary subgroups says nothing.

Also worth recording: one cannot simply assume local solvability at `2`.  The embedding problem
`ℤ/4 ↠ ℤ/2 = Gal(ℚ₂(i)/ℚ₂)` is genuinely obstructed —
`hilbertSymbolAt primeTwo (-1) (-1) = -1` in the repository — so the local condition at a dyadic
ramified place is a real condition, not a formality.

### Route (c): drop total reality instead, and omit the archimedean place

§0.19 offered two shapes for the `ℓ = 2` induction.  There is a third, and on the corrector side it
is strictly better than both.

> **(c)** Keep the §0.16 invariant that `2` is **unramified**, but **drop** the requirement that `K`
> be totally real, and use (T5) with the **archimedean** place omitted.

Under (a) the corrector deficiency is one because a corrector `d = ± 2^a ∏ pᵢ^{bᵢ} q` has its sign
tied to its `−1`-component: the target has rank three (dyadic class modulo unramified, rank two;
sign, rank one) and the correctors reach only rank two.  Under (c) the sign is no longer part of the
target — the archimedean condition is the one being omitted — so only the rank-two dyadic class must
be corrected, and `{−1, 2, −2}` spans exactly that.  **Deficiency zero.**  The price is (T5) with the
archimedean place omitted rather than a finite one; by shortcut 2 above that is the same theorem.

So all three routes cost exactly one theorem, (T5), and (c) costs nothing else.  The recommendation
of §0.19 is unchanged and reinforced: **build the invariant map**.

### The shape of the remaining work

Global reciprocity over `ℚ` decomposes as:

1. **Local**: `Br(K) ≅ ℚ/ℤ` for a local field, with `Br(K^ur/K)` the whole of it.  The unramified
   half is already done — `Local/UnramifiedInvariant.lean` builds `unramifiedInvariant` and proves
   it bijective.  What is missing is that *every* class is split by an unramified extension.  The
   classical algebraic proof of that goes through the valuation on a central division algebra: the
   residue algebra is a division algebra over a finite field, hence commutative by Wedderburn's
   little theorem (`littleWedderburn`, in Mathlib), and lifting a generator of the residue extension
   produces an unramified maximal subfield.
2. **Cyclotomic approximation**: every class of `Br(ℚ)` is split by a cyclic cyclotomic extension
   with prescribed local degrees.
3. **Reciprocity for cyclotomic extensions**, which is the elementary computation
   `Frob_{(a)} : ζ ↦ ζ^a`.
4. **Assembly of (T5)**, then the `ℓ = 2` Scholz induction under route (c), then Grunwald–Wang for
   gap 2.

Step 1 is the deep one and is the natural next target.

### Bricks landed alongside this survey

* `GroupCohomology/InflationRestriction.lean` — the exactness of `0 → H²(G/N, Mᴺ) → H²(G, M) →
  H²(N, M)` at the middle term, for an **arbitrary** normal subgroup with vanishing `H¹(N, M)`,
  written on cochains.  The index-two case was already in `GroupCohomology/IndexTwo.lean`; the
  general case replaces the two named cosets by a choice of representatives
  (`exists_cosetSection`) and runs the same three corrections.  The packaged consequence,
  `isMulCoboundary₂_of_forall_subgroup_of_forall_inflated`, is the dévissage step: `H²(G, M) = 0`
  follows from `H¹(N, M) = 0`, `H²(N, M) = 0` and the vanishing of `H²` on inflated cocycles.  This
  is what a general-degree second inequality, and Tate's theorem after it, will be built on.
* **The counting half of the *local* first inequality**, i.e. `|Br(L/K)| ≤ [L:K]` for every solvable
  extension of local fields, in five modules:
  * `Brauer/RelativeIndex.lean` — the relative Brauer group of a cyclic extension is `Kˣ/N Lˣ`.
  * `Brauer/SolvableBound.lean` — the dévissage.  It is now stated for a predicate on the *pair*
    `(F, E)` rather than on the top field alone, because the hypothesis actually carried through the
    induction (every automorphism is an isometry) is a property of the pair.  `IsDevissageClosed P`
    accordingly asks for *both* halves of the tower cut out by a subgroup: `P (fixedField C) E` and
    `P F (fixedField C)`.
  * `Brauer/SolvableNormBound.lean` — the same dévissage restated with the cyclic input as a bound
    on the index of the norm subgroup, so that no algebra appears in the hypothesis.
  * `Local/SubfieldValued.lean` — the descent brick.  A subfield of a valued field carries the
    *restricted* valuation `(Valued.v).comap (algebraMap S A)` together with the induced uniformity;
    `IsValuedExtension S A` bundles the two compatibilities, and everything the local computation
    needs (completeness of a closed subfield, the residue characteristic, finiteness of the graded
    pieces) descends along it *unchanged*, because the valuation is restricted and not renormalised.
  * `Local/FixedFieldValued.lean` — the fixed subfield of a group of isometries is closed, hence
    complete; its value group is still nontrivial because `∏_{σ ∈ C} σ π` is fixed and has value
    `(v π)^{|C|}`; and the isometry hypothesis transports both ways, down via
    `AlgEquiv.liftNormal_commutes` and up via `AlgEquiv.restrictScalars`.
  * `Local/CompleteNormIndex.lean`, `Brauer/LocalBrauerBound.lean` — the assembly.
    `IsLocalExtension K A` says `A` carries a complete valuation with a residue characteristic,
    finite graded pieces and a nontrivial value group, preserved by every `K`-automorphism;
    `card_relative_le_finrank_of_isLocalExtension` is the conclusion.
* The local Herbrand chain (`Local/AdicHerbrand.lean`, `Local/AdicUnits.lean`,
  `Local/UnitHerbrandChain.lean`, `Local/UnitValuation.lean`) no longer needs the valuation to be
  *surjective* onto `ℤᵐ⁰`.  A generator `m` of the value group (`IsUnitValGen A m`) and the divided
  map `unitValDiv hm x = unitVal x / m` have the same kernel, surject onto `ℤ`, and are
  `G`-invariant, so a merely **nontrivial** value group suffices.  This is what makes the class of
  local extensions closed under the dévissage: a fixed subfield has a nontrivial value group, but
  its value group is `|C|·ℤ`, not `ℤ`.

The one hypothesis still taken as input rather than proven is that every `K`-automorphism of `A` is
an isometry.  For a complete discretely valued `A` this is automatic — the valuation ring is the
integral closure of that of `K` — but proving it is an independent piece of work, and stating it as
a hypothesis keeps the dévissage usable for the abstract valued fields the Herbrand chain runs on.

### 0.20.1 The restriction map, computed (`Brauer/BaseChangeCentralizer.lean`)

Every use of the invariant map needs `res_{L/K} : Br(K) → Br(L)` evaluated on an explicit algebra,
and the classical formula is the *centralizer* formula: if `L` sits inside a central simple
`K`-algebra `A` and `B = C_A(L)`, then

```
L ⊗_K A  ≅  M_{[L:K]}(B)      as L-algebras,
```

so `res_{L/K} [A] = [C_A(L)]` in `Br(L)`.  `exists_algEquiv_matrix_of_range_eq_centralizer` is that
statement.  It is proved by making `A` a right `B`-module (a left `Bᵐᵒᵖ`-module, `BMod`), letting
`L ⊗_K A` act by right multiplication on the first factor and left multiplication on the second
(`toEndB`), and identifying the target:

* `A ≅ B^{[L:K]}` as `Bᵐᵒᵖ`-modules is *free for free* — `B` is simple (it is the centralizer of a
  simple subalgebra) and `SkolemNoether.nonempty_linearEquiv_of_finrank_eq` upgrades the dimension
  identity `dim_K A = [L:K] · dim_K B` to an isomorphism of modules, with no Wedderburn
  decomposition and no explicit basis;
* `End_{Bᵐᵒᵖ}(B^d) ≅ M_d(End_{Bᵐᵒᵖ} B) ≅ M_d(B)` — the second step is `AlgEquiv.moduleEndSelfOp`,
  and it is `B` rather than `Bᵐᵒᵖ` precisely because the module is a *right* module;
* `L ⊗_K A` is simple, so `toEndB` is injective, and the two sides have the same `L`-dimension.

The statement is phrased with an abstract `B` and an injective `g : B →ₐ[K] A` whose range is the
centralizer, the embedding of `L` being *derived* as `g ∘ (algebraMap L B)`; this avoids having to
put an `Algebra L` structure on the subtype `↥(Subalgebra.centralizer K …)` at the call site.
Taking `B = L` recovers `exists_algEquiv_matrix_of_centralizer_eq_range` of `Brauer/Centralizer.lean`
(a self-centralizing subfield splits), and taking `L = K` gives `K ⊗ A ≅ M_1(A)`.

### 0.20.2 Restriction on crossed products (`Brauer/CrossedProductRestrict.lean`)

§0.20.1 computes `res` in terms of a centralizer; this section computes that centralizer in the one
case every invariant-map argument needs.  Let `E / K` be finite Galois, `f` a multiplicative
`2`-cocycle of `Gal(E/K)` with values in `Eˣ`, and `M` an intermediate field.  Then

```
C_{(E/K, f)}(M) = (E/M, f|_{Gal(E/M) × Gal(E/M)}),
```

and consequently

```
res_{M/K} [E/K, f]  =  [E/M, f|_{Gal(E/M)}]    in Br(M).
```

`baseChangeHom_mk_csa` is that identity; `nonempty_algEquiv_matrix_restrict` is the algebra
statement `M ⊗_K (E/K, f) ≅ M_{[M:K]}((E/M, f|))` it comes from.  On the cohomological side
`restrictCocycle` is literally the restriction of cochains along `Gal(E/M) → Gal(E/K)`, so this says
the diagram

```
H²(Gal(E/K), Eˣ) ──→ Br(K)
      │ res                │ res
      ▼                    ▼
H²(Gal(E/M), Eˣ) ──→ Br(M)
```

commutes — the compatibility that turns `inv_L ∘ res = [L:K] · inv_K` into a computation with
cocycles.

Three points of the Lean encoding are worth recording.

* The centralizer half is a support computation, not an algebra computation.  Writing `y` in the
  basis of symbols, `y · u_c = u_c · y` for `c ∈ M` reads coordinatewise as
  `(g c − c) · y_g = 0` (`toFinsupp_mul_incl` against `toFinsupp_incl_mul`), so every `g` in the
  support of `y` fixes `M` pointwise.  `Finsupp.mapDomain_comapDomain` then rebuilds `y` from the
  smaller crossed product.  `AlgEquiv.ofRingEquiv` is what promotes such a `g` to an element of
  `Gal(E/M)`.
* `CrossedProduct hf'` for the restricted cocycle carries an `Algebra M` structure but **no**
  `Algebra K` structure globally — `M` is not central in `CrossedProduct hf`, so declaring one as an
  instance would be wrong.  It is introduced with `letI` inside the proof of
  `nonempty_algEquiv_matrix_restrict`, via `RingHom.toAlgebra'` on `incl hf' ∘ algebraMap K E`,
  exactly long enough to feed `exists_algEquiv_matrix_of_range_eq_centralizer`.  This is why that
  brick was stated with an abstract `B` and a derived embedding of `L`.
* `AlgEquiv.restrictScalars K : Gal(E/M) → Gal(E/K)` is definitionally the identity on underlying
  maps, so `restrictScalars_one`, `restrictScalars_mul`, `restrictScalars_apply` and
  `restrictScalars_smul_units` are all `rfl` — but `rw` will not close goals by them, and each of
  the multiplicativity proofs needs them spelled out.

### 0.20.3 Route (c) is *free*: Albert–Brauer–Hasse–Noether over `ℚ` with no hypothesis at all

The four preceding sections all end with the same recommendation — build the invariant map, because
(T5) needs reciprocity.  That recommendation is now wrong for gap 1.  Route (c)'s form of (T5) is a
theorem, and its proof does not touch reciprocity.

```lean
InverseGalois.CFT.exists_isMulCoboundary_of_forall_ramified
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K] {n : ℕ} (hn : n ≠ 0)
    {a : Gal(K/ℚ) → Gal(K/ℚ) → ℚˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z, a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v, ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal → ‹local coboundary at v›) :
  ∃ b : Gal(K/ℚ) → Kˣ, ∀ g h, g • b h / b (g * h) * b g = Units.map (algebraMap ℚ K) (a g h)
```

No parity of `n`, no condition at the archimedean place, no square root of minus one, no total
reality: **a torsion two-cocycle of rational units which is a coboundary at every ramified finite
place is a coboundary.**  That is (T5) with the archimedean place omitted, which §0.20 identified as
exactly what route (c) buys its deficiency-zero corrector count with.

#### Why no reciprocity is needed

§0.18 proved the same statement under the extra hypothesis `ι² = −1` in `K`, and §0.19 concluded
that the hypothesis was fatal because it makes the place above `2` ramified.  It is fatal only if
one insists that `K` be the field the induction carries.  It need not be: the hypothesis can be met
by **enlarging** `K`, and the enlargement never enters the conclusion.

* `K/ℚ` finite Galois is the splitting field of a separable `p ∈ ℚ[X]`
  (`IsGalois.is_separable_splitting_field`).  Put `L := (p · (X² + 1)).SplittingField`.  Then `L/ℚ`
  is finite Galois, contains a root of `X² + 1`, and receives `K` by
  `Polynomial.IsSplittingField.lift`.
* Inflate the cocycle along `AlgEquiv.restrictNormalHom K : Gal(L/ℚ) → Gal(K/ℚ)`.  Cocycle identity
  and `n`-torsion inflate for free.
* The local hypothesis inflates too, and this is the point that §0.19 missed.  A place `w` of `L`
  lies above a place `v` of `K`; the inflated cocycle's local condition at `w` is the image of the
  condition at `v` under the decomposition-group restriction and the map on local units.  It is
  therefore supplied at **every** place `w` of `L`, ramified or not — including the places above `2`
  that the enlargement has just ramified — because it is supplied at every place of `K` that the
  criterion asks about, and the unramified places of `K` are discharged by
  `exists_sub_add_eq_adicUnits_of_nsmul_eq_zero` as always.  Ramification created *by the
  enlargement* costs nothing, because the hypothesis is transported from below rather than checked
  above.
* Apply §0.18 over `L`, and descend: a coboundary whose values are inflated is a coboundary
  downstairs, because `Gal(L/ℚ) ↠ Gal(K/ℚ)` and the cochain can be pushed through Hilbert 90 for
  the kernel.

So the dyadic place, which under `ι ∈ K` was a genuine obstruction *for `K`*, is not one *for `L`*:
the whole content of §0.19's negative computation is that `−1` is not a norm from `ℚ₂(i)`, and the
inflated cocycle never has to be a norm anywhere, only to be a coboundary where it already is one.

#### Modules

* `Units/TowerCoboundary.lean` — a family of units of the base which is a local coboundary at a
  place of a middle field inflates to a local coboundary at every place above it.  The compatibility
  content is `adicCompletionAut_adicCompletionComap_restrict`: the automorphism of the completion
  attached to `σ ∈ D_w` and the one attached to its restriction agree on the completion below, both
  being continuous and agreeing on a dense image.
* `Units/InflationDescent.lean` — `exists_isMulCoboundary_of_restrictNormalHom`: a global coboundary
  for the inflated cocycle descends.
* `Units/ABHNFinite.lean` — the assembly, plus the unramified-place bookkeeping
  (`exists_sub_add_eq_adicUnits_of_pow_eq_one`).

The consumers in `Kummer/CentralEmbeddingSqrtNegOne.lean` lose the hypothesis and are renamed
`exists_surjective_hom_rat_of_forall_ramified{,_lift,_pow,_primeResidue,_lift_or_primeResidue}`.

#### One Lean obstacle, and how it was side-stepped

The natural enlargement is the compositum `K ⊔ ℚ(i)` inside a fixed algebraic closure.  That does
not work: for `S : IntermediateField ℚ Ω` there are several competing `Algebra ℚ ↥S` structures
(`IntermediateField.algebra'`, `DivisionRing.toRatAlgebra`, and the `SMul` coming from
`SubfieldClass`), they are propositionally but not definitionally equal, and for the relative
compositum `supOver A K : IntermediateField ↥K Ω` instance search resolves `Algebra ℚ ↥(supOver A K)`
to `DivisionRing.toRatAlgebra`, so `FiniteDimensional ℚ`, `IsGalois ℚ` and
`IsScalarTower ℚ ↥K ↥(supOver A K)` all fail to synthesize.  `Subsingleton.elim` transports a *Prop*
across the diamond but cannot repair instance search inside a later `haveI`.

For an **abstract** `L` there is no diamond at all — `L` carries one `Algebra ℚ` structure, the one
it was given.  `Polynomial.SplittingField` is abstract, `Normal.of_isSplittingField` and
`NumberField.of_module_finite` supply the two instances, and `IsSplittingField.lift` plus
`IsScalarTower.of_algebraMap_eq fun x => (lift.commutes x).symm` supply the tower.  This is the
pattern of `Mathlib/FieldTheory/PolynomialGaloisGroup.lean`, and it is the recommended shape for any
"enlarge the field" step in this layer.

One tactic note: writing `set q := p * (X ^ 2 + C 1)` makes `rw` rewrite inside `q.SplittingField`
and unfold the construction again.  Introducing `q` by `obtain ⟨q, hqp, hqc⟩ : ∃ q : ℚ[X], _ := …`
keeps it an opaque local, which is what the downstream `letI : Algebra K q.SplittingField` needs.

#### What this changes strategically

| | before | now |
|---|---|---|
| gap 1, `ℓ = 2` Scholz–Reichardt | blocked on (T5), i.e. on the invariant map | **local–global layer complete**; blocked on the induction invariant |
| gap 2, `ElementaryAbelianKernelEP` | blocked on Grunwald–Wang | unchanged — still needs the invariant map |

The invariant map is still worth building, and it is still the only route to gap 2.  It is no longer
on the critical path for gap 1.

#### What `ℓ = 2` still needs

Route (c)'s induction invariant: `K/ℚ` Galois with `Gal(K/ℚ)` a `2`-group, **unramified at `2`**,
every other ramified prime `≡ 1 mod 2^N`, and **no condition at the archimedean places**.  Against
that invariant:

1. **The local–global step.**  Done, by the theorem above; at `ℓ = 2` no cyclotomic base change is
   needed either, since `μ₂ ⊂ ℚ`, so `Scholz/ProperSolution.lean`'s detour through
   `cycSubfield ℓ` collapses.
2. **The dyadic corrector.**  `IsInertiaRankOneAt 2` is false and stays false (§0.16); what replaces
   it is a rank-**two** cancellation at the dyadic place, the two generators being the classes of
   `−1` and `2`.  `{−1, 2, −2}` spans the target exactly: deficiency zero, and the auxiliary prime
   keeps its congruence `q ≡ 1 mod 2^N` (no `q ≡ 3 mod 4` is needed, which is what makes route (c)
   better than §0.17's escape).  *The justification of "deficiency zero" given when this was first
   written was wrong; see §0.21 for the correct one and for what it costs.*
3. **§0.16 item 1**, the radicand.  `RadicalDisjoint`/`NilpotentRadical` are false at `2`; the
   replacement is the dimension count against the quadratic subfields of `A` — the bad radicands
   form a subgroup of `ℚ^×/(ℚ^×)²` of order `2^{d(G)}`, and `Scholz/ResidueSpan.lean` has to be made
   to dodge it.

---

## 0.21 Status (2026-08-27) — the `ℓ = 2` local–global step is *landed*; the dyadic corrector, correctly analysed

### What landed

Three modules, all sorry-free and in the default build.

* **`Scholz/ProperSolutionTwo.lean`** — `hasProperSolution_two`.  A central Frattini embedding
  problem with kernel of order `2`, posed over a field `A` of two-power degree satisfying `(S_{N+1})`,
  is solvable over an extension of `A`.  The proof is the direct application of §0.20.3's
  hypothesis-free ABHN over `ℚ`: `IsPrimitiveRoot (-1 : ℚ) 2` supplies the root of unity, so there is
  **no cyclotomic base change**, and there is **no condition at the archimedean place**.  The local
  hypothesis at each ramified place is `isCyclic_and_exists_hasResidueChar_rat`, which reads Serre's
  condition off the places of `A` directly instead of transporting it to a compositum.
* **`Scholz/CentralStepTwo.lean`** — `exists_surjective_hom_of_isScholz_two` and
  `exists_surjective_hom_of_centralStep_two`.  Same interface as the odd-`ℓ`
  `exists_surjective_hom_of_{isScholz,centralStep}`, with `Odd ℓ` gone and the coprime-index descent
  deleted: the `ρ` that `HasProperSolution` supplies **is** `galRestrictLE`, which is exactly what
  the coercion clause of `HasProperSolution` says.
* **`Scholz/CentralCyclicLift.lean`** — the group-theoretic heart of the dyadic corrector, see below.

One Lean note worth keeping.  `ProperSolutionTwo`'s local lemma is stated for
`{K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]` with **no `[Algebra ℚ K]` binder**.  Adding
one makes the algebra structure an opaque `fvar` which cannot unify with the
`DivisionRing.toRatAlgebra` baked into `IsScholz.isCyclic_stabilizer`,
`mul_card_stabilizer_dvd_sub_one` and `inertia_ne_bot_iff_mem_ramifiedSet`.  For
`A : IntermediateField ℚ (AlgebraicClosure ℚ)` the two candidate instances
`IntermediateField.algebra' A` and `DivisionRing.toRatAlgebra` are equal by `rfl`, so the call site
works; it is only the section variable that breaks it.

### The dyadic corrector: the earlier sketch was right, the earlier *reason* was not

§0.20.3 item 2 asserted that `{−1, 2, −2}` spans the dyadic target exactly, i.e. deficiency zero.
That conclusion stands.  The justification offered there — "the decomposition group at `2` of the
solution field is abelian, so its inertia character is determined by `ℚ₂`" — does **not** work, and
the failure is instructive enough to record.

Write `L₀ ⊇ A` for the solution field, `A` unramified at `2`, `C := ker f ≅ ℤ/2` central.  Then
`I_2(L₀) ⊆ Gal(L₀/A) = C` and `D_2(L₀)/I_2` is cyclic, so `D := D_2(L₀)` really is abelian.  But
abelian is not enough: `D` can be cyclic of order `4` with `I_2 = D²` the subgroup of squares, and
then `Ψ|_{I_2}` — a surjection `I_2 ↠ ℤ/2` — does **not** extend to any character of `D`, so no
comparison with a character of `D` can produce the corrector.  Such a `D` genuinely occurs: by local
class field theory the map `ℚ₂^× → ℤ/4`, `2 ↦ 1`, `−1 ↦ 2`, `1 + 4ℤ₂ ↦ 0`, cuts out a cyclic quartic
extension of `ℚ₂` with `e = 2, f = 2` whose inertia subgroup is the squares.

What *is* true is the same statement one level up, over the absolute Galois group of `ℚ₂` rather
than over `D`:

> Because `2` is unramified in `A`, the local embedding problem at `2` has an **unramified**
> solution: `G_{ℚ₂}` has a procyclic unramified quotient, and Frobenius may be sent to any preimage
> in `G` of the Frobenius image in `H`.  The global solution and the unramified local one differ by
> a genuine character `μ : G_{ℚ₂} → C` (their ratio is a homomorphism because `C` is central), and
> `Ψ|_{I_2} = μ|_{I_2}` because the unramified solution is trivial on inertia.  A quadratic character
> of `ℚ₂` is `χ_c` for `c ∈ ℚ₂^×/(ℚ₂^×)²`, a group of order `8` with representatives
> `±1, ±2, ±5, ±10` of which `5` is the unramified class; so `μ|_{I_2} = χ_d|_{I_2}` for one of the
> four **rational** classes `d ∈ {1, −1, 2, −2}`.

Deficiency zero, confirmed — and the reason is the unramified local solution, not abelianness.

Two consequences worth stating plainly.

* Whether the dyadic place can be removed is **not** an invariant of the solution that a twist can
  change: twisting `Ψ` by a quadratic character `λ` replaces `Ψ|_{I_2}` by `Ψ|_{I_2}·λ|_{I_2}`, and
  `λ|_{I_2}` is always one of the four classes above.  It is a property of the embedding problem,
  and the argument above is what makes it always favourable.
* Allowing the corrector to be `χ_m` for a general rational `m` (rather than `m ∈ {−1, 2, −2}`) buys
  nothing at `2`: `χ_m|_{I_2}` depends only on the class of `m` in `ℚ₂^×/(ℚ₂^×)²` modulo the
  unramified class, i.e. only on `m` mod `⟨5⟩`, i.e. on one of the same four classes.  An auxiliary
  prime `q ≡ 5 mod 8` contributes the unramified class and is invisible on inertia.

### Making the unramified lift finite — `Scholz/CentralCyclicLift.lean`

The argument above lives on `G_{ℚ₂}`, which the repository does not have.  It can be made finite.
The only thing `G_{ℚ₂}` was used for is: *the unramified quotient is procyclic of order divisible by
`exp G`, so Frobenius may be sent anywhere.*  A finite Galois `M/ℚ` has `D/I` cyclic of order the
residue degree at `2`, so it suffices to make the residue degree divisible by `exp G` — and that
costs one elementary enlargement:

> For every `k`, any prime divisor `r` of `2^{2^k} + 1` has `ord_r(2) = 2^{k+1}` exactly
> (`2^{2^k} ≡ −1`, so the order divides `2^{k+1}` and does not divide `2^k`).  Hence in `ℚ(ζ_r)` the
> prime `2` is unramified with residue degree `2^{k+1}`.  Adjoin such an `r` with `2^{k+1} ≥ |G|`.

Inertia upstairs surjects onto inertia downstairs, so a cancellation proved over `M·ℚ(ζ_r)` descends
to `M`; and the enlargement is unramified at `2` and at every prime of the Scholz set, so it costs
the induction invariant nothing except the prime `r`, which is an ordinary correctable prime.

With the residue degree arranged, the group-theoretic step is exactly:

```lean
InverseGalois.CFT.exists_monoidHom_range_le_ker_eqOn
    {D G H : Type*} [Group D] [Group G] [Group H] {I : Subgroup D} [I.Normal]
    (hcyc : IsCyclic (D ⧸ I)) (hexp : ∀ g : G, g ^ Nat.card (D ⧸ I) = 1)
    {f : G →* H} (hZ : f.ker ≤ Subgroup.center G) {θ : D →* G} (hI : ∀ σ ∈ I, θ σ ∈ f.ker) :
  ∃ μ : D →* G, μ.range ≤ f.ker ∧ ∀ σ ∈ I, μ σ = θ σ
```

together with its `Nat.card G ∣ Nat.card (D ⧸ I)` corollary.  The proof picks a generator of `D ⧸ I`
and a preimage `x`, builds the homomorphism `D →* G` killing `I` and sending `x ↦ θ x` (legitimate
because the order of the quotient kills `G`), observes that it agrees with `θ` after composing with
`f` — the two agree on `I` and at `x`, which generate `D` — and takes the pointwise ratio, which is
a homomorphism because `f.ker` is central.  Supporting lemma:
`exists_monoidHom_apply_eq_of_forall_mem_zpowers`, a homomorphism out of a cyclic group prescribed
freely on a generator.

### What the dyadic corrector still needs

1. **(F2), the local Kummer fact — the route is settled and most of its bricks have landed.**
   Let `M/ℚ` be finite Galois, `P | 2`, `D` and `I` the decomposition and inertia groups at `P`,
   `Z` the decomposition field, and `μ : Gal(M/Z) →* ℤ/2` any character.  Then there is
   `d ∈ {1, −1, 2, −2}` with `μ` and `χ_d` agreeing on `I`.  The proof needs **neither** the
   completion `v.adicCompletion ℚ` **nor** the square-class count `[ℚ₂^× : (ℚ₂^×)²] = 8`: it is a
   statement about the place `w` of `Z` under `P`, which has `e(w/2) = f(w/2) = 1`, and the only
   input is that `2` is a uniformizer there and the residue field is `𝔽₂`.
   - *Step A*, `e = f = 1` at the decomposition field: `ramificationIdx_eq_one_of_stabilizer_le`
     (`Scholz/FixedFieldRamification.lean`), with `U := stabilizer Gal(M/ℚ) P`.  **In repo.**
   - *Step B*, the quadratic subextension cut by `μ` is generated by a square root `y` of some
     `β ∈ Z`: Mathlib's `exists_root_adjoin_eq_top_of_isCyclic`.  **In Mathlib.**
   - *Steps C/D*, the square class: **landed** as `Kummer/DyadicSquareClass.lean` (pure valuation
     layer — for a unit `u` exactly one of `(u ± 1)/2` lies in the place, and one of `1, 2` makes
     the exponent of the uniformizer even) and `Kummer/DyadicPlace.lean` (the bridge, reading the
     uniformizer off `e = 1` and the residue field off `f = 1`).
   - *Step E*, a radical whose radicand is congruent to one modulo four is unramified:
     `eq_of_isCongrPow` (`Kummer/InertiaBound.lean`).  **In repo.**
   - *Step F*, the assembly `α := y·√d`: **landed** as `Kummer/DyadicInertiaChar.lean`
     (`exists_sq_intCast_eqOn_inertia`).  Requiring `i, √2 ∈ M` — that is, `ζ₈ ∈ M`, which the
     induction may arrange because `ℚ(ζ₈)/ℚ` is a `2`-extension ramified only at `2` — removes the
     need for any compositum: `√d ∈ M` for all four `d`, so `y·√d` is a radical inside `M` itself.
     The companion `Kummer/QuadraticChar.lean` (`sqrtChar`, `sqrtChar_range_le`,
     `sqrtChar_eq_one_of_mem_inertia`) turns a square root of one of `1, −1, 2, −2` into a genuine
     character of `Gal(M/ℚ)` with values in any subgroup containing a prescribed element of order
     dividing two, and shows it is trivial on inertia at every place away from `2`.
   - *Step G*, extending `θ|_I` to `μ` on `D`: **landed** as `Scholz/DecompositionLift.lean`
     (`exists_monoidHom_stabilizer_eqOn_inertia`), which wires
     `exists_monoidHom_range_le_ker_eqOn_of_card_dvd` (`Scholz/CentralCyclicLift.lean`) to the
     cyclicity of `D/I` and needs `|G| ∣ |D/I| = f(P/2)`.
   - *Step H* = (F1′), making `2^k ∣ f(P/2)` by adjoining `ℚ(ζ_r)` for `r = 2^{2^k}+1`, so that
     `ord_r(2) = 2^{k+1}`: **landed** as `Scholz/DyadicResidueDegree.lean`
     (`pow_dvd_inertiaDeg_two_of_cycSubfield_le`).  Primality of the Fermat number is *not* needed:
     `2^{2^k} ≡ −1 (mod 2^{2^k}+1)` alone pins the order.
   - *The assembly*: **landed** as `Scholz/DyadicCorrector.lean` (`hasCorrectingCharAt_two`).
     Given `|ker f| = 2`, `ζ₈ ∈ M`, `θ` unramified at `P | 2` and `|G| ∣ f(P/2)`, it produces
     `HasCorrectingCharAt M f 2 θ` with `a = −1`.  The one case split is on whether the extension
     `ν` of `θ|_I` to `Gal(M/Z)` is trivial: if it is, `χ := 1` and `a := 0` already work.
     What remains to feed it is arithmetic, not algebra — the induction must arrange `ζ₈ ∈ M` and
     `|G| ∣ f(P/2)`, both by enlarging `M` inside a `2`-extension ramified only at `2`.
2. **(F3), the `θ`-relative refactor of `Scholz/RamificationControl.lean`.  DONE** (commit
   `13eb747`): `HasCorrectingCharAt M f p θ` carries the solution as a parameter.
   Historical note: `HasInertiaCancellation`
   currently quantifies over *all* `θ`; at `2` the cancellation holds only for the solution actually
   in hand.  `HasCorrectingChar` must therefore carry the current solution as a parameter, and
   `exists_twist_ramifiedSet_inter` must re-establish it after each twist.  That is sound — twisting
   at `p` multiplies the solution by a character trivial on inertia at every `q ≠ p`, so the
   restriction to inertia at `q` is unchanged — but `exists_twist_ramifiedSet_sdiff` does not
   currently expose the twisting formula `ψ₁ = ψ · χ^a`, so it needs strengthening first.
3. **`Scholz/UnramifiedSolution.lean`.**  `hodd` and `IsInertiaRankOneAt ℓ` enter
   `exists_galEquiv_ramifiedSet_subset` at exactly two points: the call to
   `exists_galEquiv_of_centralStep` (now replaceable by an `ℓ = 2` analogue built on
   `exists_surjective_hom_of_centralStep_two`), and the call to `hasInertiaCancellation_of_isPGroup`
   at `p = ℓ`.  Away from `ℓ`, cyclic inertia already gives the cancellation for free, so the surgery
   is confined to those two lines plus item 2.
4. **§0.16 item 1**, the radicand, unchanged: `RadicalDisjoint`/`NilpotentRadical` are false at `2`
   and the replacement is the dimension count against the quadratic subfields of `A`.

---

## 1. Scholz–Reichardt

### 1.1 Statement

> **Theorem (Scholz 1937, Reichardt 1937).** *Let ℓ ≠ 2 be a prime. Every finite ℓ-group is a
> Galois group over ℚ. Equivalently, every finite nilpotent group of odd order is a Galois group
> over ℚ.*

Serre, *Topics in Galois Theory* (Harvard 1988, notes by H. Darmon, Jones & Bartlett 1992),
**Theorem 2.1.1**, §2.1 (pp. 9–16). Note the section number: the Scholz–Reichardt material is
§2.**1**, not §2.2; §2.2 is the Frattini subgroup. Malle–Matzat, *Inverse Galois Theory*
(Springer Monographs in Mathematics, 1999) treats embedding problems in **Chapter IV**.

Originals:
* A. Scholz, *Konstruktion algebraischer Zahlkörper mit beliebiger Gruppe von
  Primzahlpotenzordnung I*, Math. Z. **42** (1937), 161–188.
* H. Reichardt, *Konstruktion von Zahlkörpern mit gegebener Galoisgruppe von
  Primzahlpotenzordnung*, J. reine angew. Math. **177** (1937), 1–5.

Serre's remarks after Thm 2.1.1, verbatim in substance:
1. It is a special case of Shafarevich's theorem.
2. If |G| = ℓᴺ the extension can be chosen ramified at **at most N primes**.
3. **The proof does not work for ℓ = 2.**
4. **It is not known whether there is a regular Galois extension of ℚ(T) with Galois group G for
   an arbitrary ℓ-group G.** ← *This kills any attempt to reach ℓ-groups through this
   repository's regular-realization machinery; see §5.*

### 1.2 The Scholz condition

Fix an ℓ-group G and N ≥ 1 with sˡ^ᴺ = 1 for all s ∈ G (i.e. ℓᴺ is a multiple of exp G).

> **Definition 2.1.2 (Serre).** A Galois extension L/ℚ has property **(S_N)** if every prime p
> ramified in L/ℚ satisfies:
> 1. p ≡ 1 (mod ℓᴺ);
> 2. for every place v | p of L, the inertia group I_v equals the decomposition group D_v.
>
> Condition 2 says exactly that L_v/ℚ_p is *totally ramified*, i.e. its residue field is 𝔽_p.

### 1.3 The induction

Every ℓ-group is built from a chain of central extensions with kernel of order ℓ. The theorem is
the following statement applied inductively along such a chain:

> **Theorem 2.1.3 (Serre).** Let L/ℚ be Galois with group G, with property (S_N). Let
> 1 → C_ℓ → G̃ → G → 1 be central with C_ℓ cyclic of order ℓ, and assume ℓᴺ is a multiple of
> exp G̃. Then the embedding problem for L and G̃ has a solution L̃ which again satisfies (S_N)
> and is ramified at **at most one more prime** than L. (Moreover that prime may be taken from
> any set of primes of density one.)

The proof splits into the split case G̃ ≅ G × C_ℓ and the non-split case, the latter in three
stages: (i) solve the embedding problem at all; (ii) modify the solution so it is unramified
outside ram(L/ℚ); (iii) modify further so (S_N) holds, at the cost of one new prime.

There is also a profinite corollary (Serre Thm 2.1.11): every *separable pro-ℓ group of finite
exponent* is a Galois group over ℚ. The finite-exponent hypothesis cannot be dropped
(ℤ_ℓ × ℤ_ℓ is not a Galois group over ℚ).

### 1.4 Arithmetic inputs, step by step — the (a)/(b)/(c)/(d) classification

Legend: **(a)** elementary; **(b)** Dirichlet on primes in AP; **(c)** Chebotarev density;
**(d)** class field theory / reciprocity.

| # | Where | What is needed | Class |
|---|---|---|---|
| 1 | Split case, choice of q | ∃ prime q ≡ 1 (mod ℓᴺ), q split completely in L, each ramified pᵢ an ℓ-th power mod q | **(a)** |
| 2 | Non-split, stage (i) | H²(ℚ, C_ℓ) → ∏_p H²(ℚ_p, C_ℓ) injective (Serre Lemma 2.1.5) | **(d)** |
| 3 | Non-split, stage (i) | Local liftability at unramified p (lift a map from Ẑ) | **(a)** |
| 4 | Non-split, stage (i) | Local liftability at ramified p: structure of the maximal abelian tame exponent-ℓᴺ extension of ℚ_p | **(d)**-lite (local) |
| 5 | Non-split, stage (ii) | Glue local abelian characters into one global Dirichlet character (Serre Lemma 2.1.6) | **(d)**, but = Kronecker–Weber over ℚ |
| 6 | Non-split, stage (iii) | Linear disjointness of L, F, ℚ(μ_ℓ, p^{1/ℓ} : p ∈ S) (Serre Lemma 2.1.9) | **(a)** (group theory + ramification) |
| 7 | Non-split, stage (iii) | ∃ prime q with prescribed *non-trivial* Frobenius | **(c)** as written — reducible, see §1.5 |

Detail on each:

**1. The split case is elementary.** Serre reduces the three conditions on q ("q ≡ 1 mod ℓᴺ",
"q splits completely in L", "each of the finitely many ramified pᵢ is an ℓ-th power in 𝔽_q") to
the *single* condition that q split completely in the field
L(μ_{ℓᴺ}, p₁^{1/ℓ}, …, p_m^{1/ℓ}); one then uses:

> **Lemma 2.1.4 (Serre).** If E/ℚ is a finite extension, there are infinitely many primes that
> split completely in E. (The refinement "every set of density one contains such a prime" needs
> Chebotarev; the bare existence statement does not.)

Serre's elementary proof: take E Galois with primitive element having integral minimal polynomial
f of degree n. If only finitely many primes p₁,…,p_k split completely or ramify, then f(x) is of
the form ±p₁^{m₁}⋯p_k^{m_k} for every x ∈ ℤ. For 1 ≤ x ≤ X, f takes ≥ X/n distinct values, but
the number of integers of that shape up to the relevant size is only a power of log X.
Contradiction. **No L-functions, no density.** This is exactly the flavour of the counting
already in `InverseGalois/NumberTheory/PrimeLowerBound.lean`.

**2. Brauer–Hasse–Noether.** Serre proves Lemma 2.1.5 by passing to K = ℚ(μ_ℓ) (degree prime to
ℓ, so H²(ℚ,C_ℓ) ↪ H²(K,C_ℓ)), identifying H²(K,C_ℓ) ≅ Br(K)[ℓ] via C_ℓ ≅ μ_ℓ over K, and
invoking Albert–Brauer–Hasse–Noether: an element of Br(K) that is locally trivial is trivial.
Since ℓ ≠ 2 the archimedean places can be ignored. **This is irreducibly class field theory**:
it *is* the fundamental exact sequence 0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0. The equivalent
formulations (Ш²(ℚ, ℤ/ℓ) = 0, Poitou–Tate) are no cheaper.

**4. Local liftability at ramified p.** Because p ≡ 1 (mod ℓᴺ) we have p ≠ ℓ, so L_v/ℚ_p is
tame; by (S_N) its group D_v = I_v is cyclic. The map G_{ℚ_p} → D_v ⊂ G factors through
Gal(E/ℚ_p) with E the maximal abelian tame extension of ℚ_p of exponent dividing ℓᴺ, and
E = (unramified of degree ℓᴺ)·ℚ_p(p^{1/ℓᴺ}), so Gal(E/ℚ_p) ≅ (ℤ/ℓᴺ)², which is projective in the
category of abelian groups of exponent | ℓᴺ. The preimage of D_v in G̃ is abelian (central
extension of a cyclic group), hence the lift exists. Formally this is local class field theory,
but only the explicit tame/Kummer part of it: it can in principle be done by hand from Kummer
theory (μ_{ℓᴺ} ⊂ ℚ_p) plus the structure of the tame quotient ⟨σ,τ | στσ⁻¹ = τ^p⟩. **Rated
(d)-lite: hard but not the global reciprocity law.**

**5. Gluing local characters — this is Kronecker–Weber.** Serre's Lemma 2.1.6: given continuous
ε_p : Gal(ℚ̄_p/ℚ_p) → C into a finite abelian group, almost all unramified, there is a unique
ε : G_ℚ → C agreeing with each ε_p on inertia I_p. His proof identifies ε_p with a map
ℚ_p^× → C by *local class field theory*, reads off conductors, and builds
ε : (ℤ/Mℤ)^× → C with M = ∏ p^{n_p} and ε(k) = ∏_p ε_p(k^{-1}); the fact that this Dirichlet
character has the required local behaviour is *global* class field theory (equivalently: the
idele decomposition I_ℚ = (∏_p ℤ_p^× × ℝ_+^×) × ℚ^×). **Over ℚ specifically, this is exactly
Kronecker–Weber plus the explicit ramification/Frobenius dictionary for cyclotomic fields**,
which is a strictly smaller target than CFT over a general number field. It is nevertheless
absent from Mathlib.

Proposition 2.1.7 and Corollary 2.1.8 are formal consequences of Lemma 2.1.6 (pure diagram
chasing, class **(a)** once 2.1.6 is granted): a lifting can be prescribed on all inertia groups,
in particular chosen unramified wherever φ is.

**6. Linear disjointness (Lemma 2.1.9).** L and F are linearly disjoint because they ramify at
disjoint sets (F ⊂ ℚ(μ_{ℓᴺ}) is the degree-ℓ^{N−1} part, totally ramified at ℓ). And
ℚ(μ_ℓ, p^{1/ℓ} : p ∈ S) has group V ⋊ 𝔽_ℓ^× over ℚ with V = (ℤ/ℓ)^{|S|} and 𝔽_ℓ^× acting by
scalars; **since ℓ ≠ 2 this group has no quotient of order ℓ**, so it contains no degree-ℓ Galois
subfield and is disjoint from L·F. *This is the only place in the whole argument where ℓ ≠ 2 is
used in an essential, visible way* — and it is pure finite group theory, class **(a)**.

**7. The one genuine Chebotarev use.** At stage (iii) one has, for each p ∈ S (the ramified
primes where the local inertia extension splits), a "defect" c_p ∈ C_ℓ, and one must correct φ̃ by
a Galois character χ : (ℤ/qℤ)^× → C_ℓ with (1) q ≡ 1 mod ℓᴺ, (2) χ(p) = c_p for p ∈ S, (3) q
splits completely in L. Writing S = {p₁,…,p_k} and c_{p_i} = c_{p₁}^{ν_i}, Serre requires a prime
q with

```
Frob_q = 1   in L·F and ℚ(μ_{ℓᴺ});
Frob_q ≠ 1   in ℚ(μ_ℓ, p₁^{1/ℓ});
Frob_q = 1   in ℚ(μ_ℓ, (p₁/p_i^{ν_i})^{1/ℓ}),  i = 2,…,k.
```

and concludes "By the Chebotarev density theorem and Lemma 2.1.9, such a q exists."

### 1.5 How much of (c) is really needed — the important reduction

All but one of the conditions in the display above are *"splits completely in a fixed number
field"*, i.e. Lemma 2.1.4, i.e. class **(a)**. Setting

* A := L · F · ℚ(μ_{ℓᴺ}) · ℚ(μ_ℓ, (p₁/p_i^{ν_i})^{1/ℓ} : i = 2,…,k),
* B := A(p₁^{1/ℓ}),

the whole Chebotarev input of Scholz–Reichardt is exactly:

> **(★)** Let A ⊂ B be number fields, B/ℚ Galois, [B:A] = ℓ. Then infinitely many rational primes
> split completely in A but **not** in B.

And (★) does **not** need Dirichlet's theorem. It follows from nothing more than the *simple pole
of the Dedekind zeta function*: for K/ℚ Galois of degree n,

```
log ζ_K(s) = Σ_{𝔭 of degree 1} N𝔭^{-s} + O(1) = n · Σ_{q splits completely in K} q^{-s} + O(1),
```

so if ζ_K(s) ~ c_K/(s−1) with c_K > 0 as s → 1⁺, then Σ_{q split in K} q^{-s} ~ (1/n)·log(1/(s−1)),
i.e. the Dirichlet density of the completely-split primes of K is 1/[K:ℚ]. Applying this to A and
to B and comparing 1/[A:ℚ] > 1/[B:ℚ] gives (★). **No Dirichlet L-functions, no non-vanishing at
s = 1, no Chebotarev machinery** — only the analytic class number formula, which Mathlib
*already has* as `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`
(`Mathlib/NumberTheory/NumberField/DedekindZeta.lean:75`). The missing piece is the Euler product
for ζ_K over prime ideals; since Mathlib's `dedekindZeta` is defined as the ℕ-indexed L-series of
`n ↦ #{I : absNorm I = n}`, and that coefficient function is multiplicative, this plugs directly
into `ArithmeticFunction.IsMultiplicative.eulerProduct`
(`Mathlib/NumberTheory/EulerProduct/Basic.lean:252`).

**So: the classification for Scholz–Reichardt is (a) + a weak-(c) that is cheaper than (b), plus
two irreducible (d)s (items 2 and 5).** The two (d)s are the blockers, not Chebotarev.

Historical note: Scholz's and Reichardt's original arguments used **ℓ-th power reciprocity** in
ℚ(μ_ℓ) to convert the condition "p_i is an ℓ-th power mod q" into a congruence condition on q
modulo p_i, then applied **Dirichlet's theorem** — i.e. classically item 7 is **(d)+(b)** rather
than (c). Serre's modernization trades reciprocity for Chebotarev. Either way it is item 7 that
is negotiable and items 2 and 5 that are not.

---

## 2. Shafarevich's theorem

### 2.1 Statement and sources

> **Theorem (Shafarevich 1954).** *Let k be a global field and G a finite solvable group. Then
> there is a finite Galois extension K/k with Gal(K/k) ≅ G.*

* I. R. Shafarevich, *Construction of fields of algebraic numbers with given solvable Galois
  group*, Izv. Akad. Nauk SSSR **18** (1954), 525–578; Amer. Math. Soc. Transl. **4** (1956),
  185–237. (Together with the three companion papers Izv. **18** (1954) 261–296, 327–334,
  389–418.)
* I. R. Shafarevich, *Factors of a decreasing central series*, Mat. Zametki **45** (1989),
  114–117 — **the correction**.
* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Grundlehren 323, 2nd ed.,
  **Chapter IX, §6**. (Chapter IX is "The Absolute Galois Group of a Global Field"; its main
  results are Grunwald–Wang and Shafarevich's theorem.)
* A. Schmidt, K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*, preprint,
  <https://arxiv.org/abs/math/9809211> — **the complete, self-contained modern proof**, and the
  primary source used below. All theorem numbers "Thm n" in this section refer to it.
* Serre, *Topics in Galois Theory*, remark 1 after Thm 2.1.1 (Serre explicitly flags the gap and
  the correction; the theorem itself is one of the topics he omits, Foreword item (b)).

### 2.2 The reduction from "all solvable groups" to embedding problems

Two steps, both purely group-theoretic (Ore's argument, Duke Math. J. **5** (1939) 431–460):

> **Prop. 16** (Huppert, *Endliche Gruppen I*, III.3.2(b)). If N ⊴ G and N ⊄ Φ(G), then N has a
> proper supplement U ⊊ G, i.e. G = N·U.
>
> **Prop. 17** (Huppert III.4.2(c)). If G ≠ 1 is finite solvable then Φ(G) ⊊ F(G), where F(G) is
> the Fitting subgroup (the composite of all nilpotent normal subgroups).

Combining: F(G) ⊄ Φ(G), so F(G) has a proper supplement U ⊊ G, hence there is a surjection
**F(G) ⋊ U ↠ G**. F(G) is nilpotent and U is a smaller solvable group, realizable by induction on
|G|. So the theorem follows from:

> **Theorem 14.** Let K/k be a finite Galois extension of global fields with group G and
> φ : G_k ↠ G. Then **every split embedding problem with finite nilpotent kernel H**
> ```
> 1 → H → H ⋊ G → G → 1
> ```
> has a **proper** (= surjective) solution.

This is the exact reduction: **split embedding problems with nilpotent kernel**, nothing more.
Because a finite nilpotent group is the direct product of its Sylow subgroups, and every finite
G-operator p-group is a quotient of F(n)/F(n)^(τ) for the free pro-p G-operator group
F(n) = G ⋉ F_n (F_n free pro-p of rank n), it suffices to treat the *generic kernel*.

### 2.3 The filtration and the actual induction

Shafarevich's 1989 correction is precisely a **refinement of the descending p-central series**:

```
P¹ = P,   P^{i+1} = (P^i)^p [P^i, P];        (descending p-central)
P₁ = P,   P_{j+1} = [P_j, P];                (descending central)
P^{(i,j)} := (P^i ∩ P_j) · P^{i+1},   indices (i,j) ordered lexicographically.
```

> **Theorem 15 (sharpened form of Thm 14).** For every prime p, all n and all τ = (i,j) the split
> embedding problem with kernel F(n)/F(n)^(τ) has a proper solution N_n | k; and for p ≠ char k
> the solution can be chosen so that
> (i) all 𝔭 ∈ Ram(K|k) ∪ S_p ∪ S_∞ split completely in N_n|K; and
> (ii) if 𝔭 ramifies in N_n|K then 𝔭 splits completely in K|k and N_{n,𝔓}|k_𝔭 is a **cyclic
> totally ramified** local extension.

Conditions (i)–(ii) are the modern form of the **"Scholz solution"** — the direct descendant of
Serre's (S_N). The induction is on τ, with n arbitrary, in four substeps:
1. show the problem is locally solvable everywhere (after changing the previous solution);
2. deduce global solvability from a local–global principle;
3.–4. modify the global solution back into a Scholz solution so that step τ+1 is again locally
   solvable.

**The shrinking procedure** is the distinctive idea. Obstructions in step τ are genuinely
non-zero. Shafarevich's device: go back and re-do step τ−1 at a much larger level m ≫ n, then
push forward along a surjective G-equivariant φ : F(m) ↠ F(n) chosen so that all the obstructions
die. The combinatorial engine is:

> **Prop. 2.** Let G be finite, M, N finitely generated 𝔽_p[G]-modules, s,t ∈ ℕ. For r large
> enough: given z₁,…,z_t ∈ (⊕_r M)^{⊗s} ⊗ N there is 0 ≠ a ∈ 𝔽_p^r such that
> φ_a : ⊕_r M → M, (x_i) ↦ Σ a_i x_i is a surjective 𝔽_p[G]-map and the induced map kills every z_i.

Its proof is **Chevalley–Warning** (Serre, *A Course in Arithmetic*, Ch. I §2 Thm 3): the
common-zero set of t polynomials of degree s in r > s·t·dim variables over 𝔽_p contains a
non-trivial point. **Fully elementary.** Mathlib has Chevalley–Warning.

### 2.4 Arithmetic inputs

| Input | Where used | Class |
|---|---|---|
| Chebotarev / Dirichlet density of `cs(Λ\|k)` (density-1 sets of primes) | throughout: the sets S = cs(Λ\|k) ∪ T | **(c)** |
| Hasse principle Ш¹(k_S, T, A) = 0 for trivial modules and density-1 T | step 2 of each induction step | **(d)** (NSW VII 13.6) |
| **Poitou–Tate duality** (global) + **local duality** | Lemma 10, Thm 13 | **(d)** |
| **Grunwald–Wang**: coker(k_S,T,A) = 0 for δ(S) = 1, A trivial, T finite **with no prime above 2** | Prop. 11 (properness of solutions) | **(d)** |
| **Kummer theory**, local Frobenius in H¹(K_𝔓, μ_p)/H¹_{nr} | Thm 13 | (a)/(d)-lite |
| H²(G, 𝔽_p[G]ⁿ) = 0 (induced modules are cohomologically trivial) | Prop. 11 | **(a)** |
| cd_p G_k = 1 for p = char k, hence p-projectivity | the function-field case | **(d)** (Serre, *Cohomologie galoisienne* II §2 Prop. 3) |
| **Chevalley–Warning** | shrinking (Prop. 2) | **(a)** |
| Frattini/Fitting group theory (Ore) | final reduction | **(a)** |

Shafarevich's theorem is therefore **strictly harder** than Scholz–Reichardt in arithmetic
prerequisites: it needs everything Scholz–Reichardt needs *plus* Grunwald–Wang *plus* Poitou–Tate
duality. There is no known route around this.

Note also what Shafarevich's method *cannot* do: unlike Neukirch's strengthening of
Scholz–Reichardt (J. Neukirch, *On solvable number fields*, Invent. Math. **53** (1979) 135–164,
which realizes pro-solvable groups of finite exponent prime to #μ(k) with prescribed completions
at finitely many places), the shrinking procedure destroys prescribed local conditions.

### 2.5 Where the 2-group difficulty lies — precisely

The gap is **the "special case" of Grunwald–Wang**. In Schmidt–Wingberg's Prop. 11 the surjectivity
of

```
H¹(k, A) → ∏_{i=1}^r H¹(k_{𝔭_i}, A)
```

— which is what makes the solution of the embedding problem *proper*, i.e. surjective — is exactly
Grunwald–Wang, and it holds only when the finite set T of primes **contains no prime above 2**
(in the number-field case). That restriction is not removable: it is Wang's counterexample. The
cleanest statement of the obstruction: *in a cyclic degree-8 extension K/ℚ the prime 2 cannot be
inert*, i.e. the unramified degree-8 extension of ℚ₂ is not the completion of any cyclic degree-8
extension of ℚ. Equivalently, 16 is an 8th power mod almost every prime but is not an 8th power in
ℚ. Such obstructions occur only when 8 divides the exponent of the group. (Same phenomenon:
Lenstra's smallest abelian counterexample to Noether's problem over ℚ is ℤ/8ℤ — see §3.3.)

Shafarevich's 1954 argument used the descending p-central series and implicitly assumed a
Grunwald-type surjectivity that fails at p = 2. Alexander Schmidt found the gap; Shafarevich
sketched the correction in the notes to his Collected Papers (p. 752) and in the 1989 Mat. Zametki
note. **The correction is the refined filtration P^(i,j) = (P^i ∩ P_j)P^{i+1} of §2.3**: it makes
the induction step small enough that the auxiliary primes can always be chosen away from 2.
Schmidt–Wingberg's footnote 2 says so explicitly: *"This refinement, which was proposed by
Šafarevič in his correction note, is necessary in order to deal with the case p = 2."*

An independent, Serre-style treatment of just the 2-group case:
P. Schmid, *Realizing 2-groups as Galois groups following Shafarevich and Serre*,
Algebra & Number Theory **12** (2018), 2387–2401,
<https://doi.org/10.2140/ant.2018.12.2387> — every finite 2-group is realizable over ℚ with the
number of (tamely) ramified primes bounded by a polynomial in the rank of G (rather than by n as
for odd ℓ).

---

## 0.22 Status (2026-08-27) — the `ℓ = 2` correction has a *hypothesis*, and it is Schmid's

§0.21 item 3 is done: `Scholz/UnramifiedSolutionTwo.lean` proves
`exists_galEquiv_ramifiedSet_subset_two`, the dyadic analogue of
`exists_galEquiv_ramifiedSet_subset`, with **no** `Odd ℓ` and **no** `IsInertiaRankOneAt 2`.  That
is Schmid's Proposition 2.1 for `p = 2`.  The next link, the dyadic analogue of
`isScholzRealizable_of_centralStep`, turns out **not** to be a matter of removing `Odd ℓ` from
`Scholz/ResidueSpan.lean`.  There is a genuine obstruction, it is sharp, and it is exactly the
hypothesis of Schmid's Proposition 4.2.

### The obstruction, derived from the repository's own statements

Let `f : G ↠ H` be the central step, `Z = ker f` of order `2`, `Z ≤ frattini G`; let `A` be the
Scholz field realizing `H`, `S = ramifiedSet A`, and `L ⊇ A` a solution with `ramifiedSet L ⊆ S`.
For `p ∈ S` let `t_p ∈ 𝔽₂` be the Frobenius defect of `Scholz/FrobeniusDefect.lean` — `t_p = 0`
exactly when the residue degree of `p` in `L` is one, i.e. when `L` too is *busy* at `p`.

The correction twists by a character `χ` of conductor `Q`, a product of auxiliary primes `q`.  Every
such `q` must split completely in `L` (that is what makes the twisted homomorphism busy at `q`).
Now let `v = ∏_{p ∈ S'} p` for some `S' ⊆ S` and suppose `√v ∈ L`.  Then `q` splits in `ℚ(√v)`, so
`(v/q) = 1` for every `q ∣ Q`, so `χ(v) = 1`, and therefore

> **`Σ_{p ∈ S'} t_p = 0` is forced** for every `S'` with `√(∏_{p ∈ S'} p) ∈ L.

Because `Z ≤ frattini G`, the quadratic subfields of `L` are exactly those of `A`; and because every
`p ∈ S` is `≡ 1 mod 4` and `2 ∉ S`, the square classes `d` with `ℚ(√d) ⊆ A` are precisely the
`v = ∏_{p ∈ S'} p` (no factor `−1`, `2` or `−2` survives: each would ramify at `2`).  So the
achievable corrections are the vectors of `𝔽₂^S` orthogonal to

```
W  =  span { 1_{ramifiedSet ℚ(√d)}  :  ℚ(√d) ⊆ A quadratic }   ⊆   𝔽₂^S ,
```

a space of dimension `d(H) = dim H/Φ(H)`.  At odd `ℓ` the corresponding `W` is **zero** — that is
precisely `pow_ne_of_isNilpotent` (`Scholz/AuxPrimeChoice.lean:70`), which says a rational number
that is an `ℓ`-th power in an `ℓ`-extension of `ℚ` is already one, true because `ℚ(m^{1/ℓ})` is not
Galois.  At `ℓ = 2` it *is* Galois, `W` is as large as the number of generators, and the twist
simply cannot reach a defect vector with `Σ_{p ∈ S'} t_p = 1`.

**Consequence.**  `residueVectors_span_eq_top` is false at `2` and no reformulation of
`Scholz/ResidueSpan.lean` repairs it.  What must change is the *induction hypothesis*: the Scholz
field has to be built so that the defect is orthogonal to `W` **by construction**.

### This is Schmid's Proposition 4.2, and the fix is his shrinking process

P. Schmid, *Realizing 2-groups as Galois groups following Shafarevich and Serre*, ANT **12** (2018)
2387–2401 (open access) runs exactly this argument and names exactly this hypothesis.  His
vocabulary maps onto the repository's:

| Schmid | repository |
|---|---|
| `q` is *busy* (fleissig) in `K`: `φ(I_q) = φ(D_q)` | `IsSplitInertia` |
| Scholz field w.r.t. `N`: (S1) `Ram(K) ⊆ 1 + p^N ℤ`, (S2) busy | `IsScholz ℓ N` |
| Proposition 2.1 | `exists_galEquiv_ramifiedSet_subset_two` ✅ landed |
| Scholz obstruction `θ_q ∈ Z(H)` | the defect `z` of `exists_mem_ker_mul_mem_map_inertia` |
| Proposition 4.2 hypothesis `θ_i = Σ_{q ∈ Ram(P_i)} θ_q = 0` | `t ⊥ W` above |

The extra structure Schmid carries is the **strong** Scholz field: the socle
`S(K) = K^{Φ(G)} = P_1 ⋯ P_d`, where the `P_i` are quadratic and the sets `Ram(P_i)` are *pairwise
disjoint and of equal cardinality*.  Then `W` is spanned by the `d` block indicators `1_{Ram(P_i)}`
and the hypothesis is one bit per block — `d` conditions, not `|S|`.  Nothing forces those bits to
vanish; they are made to vanish by **shrinking**:

1. Realize, inductively on the `2`-class `c`, the *disposition group* `G_δ^{c−1} = F_δ/λ_c(F_δ)` for
   a much larger rank `δ = r·d`, where `λ` is the lower `2`-central series
   `λ_{n+1} = [λ_n, G]·λ_n²` and `r` is a polynomial in `d`.
2. Solve the central step (Proposition 2.1) to get `E_δ` with group `G_δ^c`, `Ram(E_δ) = Ram(K_δ)`;
   record the block obstructions `θ_{ij} ∈ λ_c(G_δ^c)` for `i ≤ d`, `j ≤ r`.
3. For `α = (a_j) ∈ 𝔽₂^r` let `π(α) : G_δ^c ↠ G_d^c` send `x_{ij} ↦ x_i^{a_j}`.  The induced map
   `α̃` on `λ_c` depends only on `α`, and each coordinate of `a ↦ Σ_j a_j α̃(θ_{ij})` is a
   polynomial in `a` of degree `≤ c + 1` **with zero constant term**.
4. Choose `r > (c+1)·d·dim λ_c(G_d^c)`.  **Chevalley–Warning** (`Mathlib/FieldTheory/
   ChevalleyWarning.lean`) then produces a *nontrivial* common zero `α`, and the corresponding
   subfield `E(α)`, of group `G_d^c`, has all its block obstructions zero.
5. Proposition 4.2 now applies and produces a strong Scholz field with group `G_d^c`; every
   `2`-group of rank `d` and `2`-class `c` is a quotient of it, and normal subfields of Scholz
   fields are Scholz.

No Poitou–Tate, no Grunwald–Wang, no Kronecker–Weber: the arithmetic inputs are Chebotarev,
quadratic reciprocity, Hecke's ramification criterion for `K(√μ)`, Brauer–Hasse–Noether (already
used by Proposition 2.1) and Chevalley–Warning.

### What that costs here, and the two simplifications worth taking

Schmid's Proposition 3.1 (the Lie-module decomposition `Z(G_d^c) = ⨁_{ν=1}^c L_d^ν` with
`dim L_d^ν = (1/ν) Σ_{k∣ν} μ(k) d^{ν/k}`) is the deepest algebraic input, and it is quoted from a
separate paper.  Two observations remove most of it:

* **Only a degree bound is needed, not the grading.**  Chevalley–Warning needs `Σ deg < #vars` and a
  known zero; `a = 0` is a zero because `π(0)` is the trivial map.  Homogeneity is never used.  So
  `deg ≤ c + 1` suffices and the exact dimensions `ℓ_d^ν` are irrelevant — any finite bound on
  `dim λ_c(G_d^c)` will do.
* **`λ_c` may replace `Z`.**  Schmid works with `Z(G_d^c)`, which equals `λ_c(G_d^c)` by his
  Proposition 3.1; but every use is of the kernel of `G_d^c ↠ G_d^{c−1}`, which *is* `λ_c` by
  definition.

What is genuinely required from the group-theory side is then:

* `lowerPCentralSeries`: `λ_1 = ⊤`, `λ_{n+1} = ⁅λ_n, ⊤⁆ ⊔ (λ_n)^p`; normality, `λ_n/λ_{n+1}`
  central and elementary abelian, surjective functoriality, and `λ_{c+1} = ⊥` for some `c` for every
  finite `p`-group;
* the disposition group `G_d^c = F_d/λ_{c+1}(F_d)`: finite, rank `≤ d`, `2`-class `≤ c`, and
  universal for those two invariants;
* `λ_c(G_d^c)` is generated by the images of `[x_{i_1}, …, x_{i_ν}]^{2^{c−ν}}`, `ν ≤ c` — the
  spanning half of Proposition 3.1 (its direct-sum half is what we drop);
* consequently: the induced map on `λ_c` depends only on `α` mod `Φ`, and is polynomial of degree
  `≤ c` in `a`.

and from the arithmetic side, Proposition 4.2 itself: Hecke's criterion, the factorisation
`(μ) = 𝔟²·𝔇·(e)`, the Shafarevich symbol `{μ/q}` and its Legendre-symbol comparison, and the
Chebotarev choice of `p_χ`.  That is a workstream of the same order as the whole odd-`ℓ`
`ResidueSpan`/`AuxPrimeChoice`/`ResidueCorrection` stack, plus a new free-group layer.

**So the `ℓ = 2` wall is no longer unmapped — it is a finite, elementary, and large plan.**

---

## 0.23 The `ℓ = 2` plan, checked line by line against Schmid's text

§0.22 was written from the abstract and the section headings.  The full text has since been read
(`pdftotext -layout` of the open-access PDF), and three of its details change the shape of the
formalization enough to be worth recording.

### Proposition 4.2 is itself an induction with kernels of order two

Its statement is

> Let `θ_i = Σ_{q ∈ Ram(P_i)} θ_q`, and assume `θ_i = 0` for all `i = 1,…,d`.  Then there exist
> infinitely many pairwise disjoint `t`-sets `{p_1,…,p_t}` of rational primes such that
> `Ê = ∏_{ν=1}^t K(√(p_ν e_ν))` is a strong Scholz field with respect to `N` admitting `G_d^c` as
> Galois group over `ℚ` and having `Ram(Ê) = Ram(K) ∪ {p_1,…,p_t}`,

and its proof runs over a basis `{χ_1,…,χ_t}` of `Hom(Z(H), 𝔽₂)`, one quadratic extension
`K_{ν−1} ↦ K_ν = K_{ν−1}(√(p_ν e_ν))` per basis vector.  **Each step has kernel of order two.**

That settles the question left open in §0.22: the repository does **not** need a residue correction
with elementary abelian kernel.  `Scholz/DyadicResidueCorrection.exists_scholz_solution_two`, whose
kernel hypothesis is `Nat.card ↥f.ker = 2`, *is* Schmid's inductive step; Proposition 4.2 is the
`t`-fold iteration of it.  The pairwise-quadratic-residue machinery is still wanted, but for the
base case (Lemmas 2.2/2.3), not for the correction.

The apparent tension — the base field changes at every one of the `t` steps, while the obstruction
`θ_q` was computed over the field at the bottom — is resolved by Schmid himself, twice:

* `R = R(χ)` is an invariant of the cohomology class, so `q ∈ R ⟺ q ∈ R_0`;
* "let `q ∈ Ram(P_i)` and let `q ∈ R_0`.  Using that `q` is busy in the Scholz field `K_0`, the
  restrictions to `E_χ` of `Φ_q` and of the Frobenius `θ_q` introduced above agree."

Business at `q` is exactly `IsSplitInertia`, which the repository already carries in `IsScholz`.

### The block structure survives the climb for free

`IsBlockSpanned` (`Scholz/DyadicSocle.lean`) is the repository's form of "the square classes of the
field are spanned by the block indicators".  `IsBlockSpanned.of_le_of_ker_le_frattini` transports it
up any Frattini subextension, and every step of the climb — central with kernel inside the Frattini
subgroup — is one.  So the blocks never grow even though `Ram` does, and the defect vector `t` stays
indexed by `Ram(A)` of the field at the bottom.  This is what makes the hypothesis `hdefect` of
`exists_scholz_solution_two` stable along the induction.

### The group-theoretic layer is finished

`Solvable/DispositionShrink.lean` supplies all of §5:

* `FreePClass.genPair`, the generators `x_{ij}` of `G_{d·r}^c`;
* `FreePClass.collapse a`, Schmid's `π(α)`;
* `FreePClass.exists_ne_zero_forall_prod_eq_one`, the Chevalley–Warning conclusion: for
  `r > d · charCount · (c+1)` there is `α ≠ 0` with all `d` block products trivial;
* `FreePClass.exists_rankMultiplier`, the choice of `r`.

Both simplifications promised in §0.22 were taken: `lowerPCentralSeries` replaces `Z(G_d^c)`, so
Schmid's Lemma 3.3 (transgression `Hom(Z(H),𝔽₂) ≅ H²(G,𝔽₂)`) and the direct-sum half of his
Proposition 3.1 are never needed.

### What remains, and in what order

| tag | content | status |
|---|---|---|
| F1 | Lemmas 2.2 + 2.3: a chain of primes each `≡ 1 mod 2^N` and mutually quadratic, and the multiquadratic strong Scholz field they cut out | ✅ `Scholz/StepRamification.lean` + `Scholz/MultiquadraticBase.lean` |
| F2 | `IsStrongScholz`: Scholz, plus pairwise disjoint blocks accounting for the square roots | ✅ `Scholz/StrongScholz.lean` |
| F3 | Proposition 2.1 at `p = 2` | ✅ `exists_galEquiv_ramifiedSet_subset_two` |
| F4 | the Scholz obstruction `θ_q` and its invariance under enlarging the base | ✅ `Scholz/CanonicalDefect.lean` + `Scholz/BlockDefect.lean` + `Scholz/CoverInertia.lean` + `Scholz/CentralDefect.lean` + `Scholz/CoverObstruction.lean` |
| F5 | Proposition 4.2 as the `t`-fold iteration of the order-two step | ✅ `Scholz/DyadicStage.lean` (`ClimbStage`, `nonempty_realization`) |
| F6 | the shrinking: `E(α) = E_δ^{ker(collapse a)}`, `K(α) = E(α) ∩ K_δ`, `Ram(P_i(α)) = ⨆_{j : a_j = 1} Ram(P_{ij})`, and the transport of obstructions along `collapse a` | ✅ `Solvable/DispositionShrink.lean` + `Scholz/DyadicShrink.lean` + `Scholz/ClassStepData.lean` |
| F7 | the induction on the `2`-class, `∀ G` a finite `2`-group, `∀ N`, `IsScholzRealizable G 2 N`, and the removal of the semiabelian-Sylow-`2` hypothesis from `InverseGalois/Shafarevich.lean` | ✅ `Scholz/DyadicInduction.lean` + `Scholz/DyadicInitialStage.lean` |

### The `ℓ = 2` wall is closed

`InverseGalois.CFT.isDyadicClassStepSolvable` (`Scholz/DyadicInitialStage.lean`) is a theorem:

```lean
def IsDyadicClassStepSolvable : Prop :=
  ∀ (c d N : ℕ), 1 ≤ c → (∀ δ M, IsStrongScholzRealizable δ c M) →
    IsStrongScholzRealizable d (c + 1) N

theorem isDyadicClassStepSolvable : IsDyadicClassStepSolvable
```

so `InverseGalois.isInverseGalois_of_isPGroup_two` realises every finite `2`-group and
`IsInverseGalois.of_isNilpotent` (`InverseGalois/Shafarevich.lean`) realises every finite nilpotent
group with no condition on the Sylow `2`-subgroup.  Both depend on `propext`, `Classical.choice`
and `Quot.sound` only.

The proof is F4 + F5 + F6 assembled as follows.  `StrongScholzRealization.exists_centralPart`
(`Scholz/CoverObstruction.lean`) reads, for each prime `q` of each block, a pair `(x, θ)` in
`G_{d·r}^{c+1}` — a generator of the inertia subgroup at `q` and the central part of an arithmetic
Frobenius above it — such that for *every* normal `W`, the obstruction of `q` in the subfield `W`
cuts out vanishes exactly when `θ ∈ ⟨x⟩ ⊔ W`.  The `θ`'s of a row multiply to one element per copy,
`FreePClass.exists_rankMultiplier` supplies a Chevalley–Warning `α` killing the collapse of the
selected products, and `ClassStepData.shrink α` merges the copies.  For the shrunken data the same
reading holds through `V ↦ (collapse α)⁻¹(V)` (`cutField_comap_comp`, `mem_sup_comap_iff`), and
`FreePClass.zpowers_inf_ker_proj` cuts the collapsed inertia subgroup down to `⟨z_i⟩`: a hyperplane
missing `z_i` joins it to the whole kernel, so nothing is obstructed, and a hyperplane containing
`z_i` reads the obstruction of the row as the character of the collapsed product, which `α` made
trivial.  That is exactly the `defect` field of `ClimbStage`, and `ClimbStage.nonempty_realization`
iterates `exists_scholz_solution_two` once per basis vector of the kernel.

`PairwiseResidue.isSquare_natCast_swap` is the brick F1 was missing: `stepPrime` delivers
`(q_j / q) = 1` for the primes already chosen, and reciprocity turns that into `(q / q_j) = 1`
because `q_j ≡ 1 mod 4`.  Putting `ℚ(ζ_{q_j})` into the splitting field, as Schmid does, would give
the same thing at a much higher cost.

---

## 0.24 Status (2026-08-28) — **Grunwald–Wang is landed** for a squarefree exponent

`InverseGalois/CFT/GrunwaldWang.lean`, sorry-free and axiom-free (`#print axioms` gives
`[propext, Classical.choice, Quot.sound]` on all seven results). §4's gap table listed
Grunwald–Wang as **ABSENT** with "zero hits, nothing adjacent"; that row is now out of date.

### What is proved

Let `K` be a number field, `n` an exponent, `S` a finite set of finite places.

| statement | name |
|---|---|
| prescribed classes mod `n`-th powers at finitely many finite places are matched by some `b ∈ Kˣ` | `exists_ne_zero_forall_pow_mul_eq_adicCompletion` |
| … by a `b` that is *not* a global `n`-th power, one prescribed class being no local one | `exists_ne_zero_not_exists_pow_eq_forall_pow_mul_eq_adicCompletion` |
| a radical extension whose radicand is a local `p`-th power outside `S` is trivial | `subsingleton_gal_of_forall_localPow_outside` |
| **Wang, prime exponent, `ζ_p ∈ K`** | `exists_pow_eq_of_forall_localPow_outside` |
| **Wang, prime exponent, arbitrary `K`** | `exists_pow_eq_of_forall_localPow_outside_of_prime` |
| **Grunwald–Wang, `n` squarefree** | `exists_pow_eq_of_forall_localPow_outside_of_squarefree` |
| the same as a Hasse principle, both directions | `exists_pow_eq_iff_forall_localPow_outside_of_squarefree` |

```lean
theorem exists_pow_eq_iff_forall_localPow_outside_of_squarefree {n : ℕ} (hn : Squarefree n)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) {b : K} :
    (∃ y : K, y ^ n = b) ↔ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ c : v.adicCompletion K, c ^ n = algebraMap K (v.adicCompletion K) b
```

### How it dodges the existence theorem

The surjectivity half was already here (`Approximation/PowClass.lean`, weak approximation). The
content is Wang's theorem, and the route uses **only the first inequality**, never reciprocity,
never the Artin map, never the existence theorem:

1. *Prime `p`, with `ζ_p ∈ K`.* If `b` is not a `p`-th power, `X^p − b` is irreducible, its
   splitting field is cyclic of degree `p` and generated by a radical `β`. `Kummer/LocalPower.lean`
   says the decomposition group at a place fixes `β` exactly when the radicand is a local `p`-th
   power there. So the hypothesis makes every place outside a finite set split completely, and
   `Units/SplitOutside.lean` — a solvable extension in which almost every place splits completely
   is trivial, which rests on the first inequality alone — forces `p = 1`.
2. *Removing `ζ_p`.* `K(ζ_p)/K` has degree `d` prime to `p`; transport the local hypothesis up
   (`Units/PlaceComap.lean`), get `y` with `y^p = b` upstairs, take norms to get `N(y)^p = b^d`,
   and read `ud + vp = 1` to get a `p`-th root in `Kˣ`.
3. *Squarefree `n`.* Each prime factor `q ∣ n` inherits the local hypothesis from `c^n =
   (c^{n/q})^q`, and roots of coprime exponents combine by Bezout.

**No case is lost to squarefreeness.** Wang's counterexample — `16` is an `8`-th power in almost
every completion of `ℚ` but not in `ℚ` — needs `8 ∣ n`, and `8 ∣ n` is incompatible with `n`
squarefree; `K` is `s`-special only for `s ≥ 3`, since `K(ζ_4)/K` is always cyclic. §2.5's
description of the obstruction is thereby confirmed from the formal side.

### What this does *not* yet unlock

Honest accounting against §2.4. The Shafarevich application needs

```
H¹(k, A) → ∏_{i=1}^r H¹(k_{𝔭_i}, A)
```

surjective for a **trivial** module `A = 𝔽_p^m`. When `ζ_p ∈ k` that group *is* `k^×/(k^×)^p` and
this is exactly the file's prescription half; over a general base `H¹(k, ℤ/p) = Hom(G_k, ℤ/p)` is
the group of cyclic degree-`p` *characters*, and prescribing those locally is the character form of
Grunwald–Wang. Getting the character form from the power form over a general base is an eigenspace
descent through `k(ζ_p)` — plausible, not written. So:

* the **power-class** Grunwald–Wang for squarefree exponent: **done**;
* the **character** form over a base without `ζ_p`: **not done** (needs the descent, or the
  existence theorem);
* the **special case** (`8 ∣ n`): **not done**, and it is genuinely false without the extra
  hypotheses;
* **Poitou–Tate duality** and the **Ш¹ Hasse principle** of §2.4: **untouched**.

Grunwald–Wang was one of three arithmetic blockers for gap 2 (`ElementaryAbelianKernelEP`), not the
only one. The nilpotent case of Shafarevich (§0.21, §0.22) remains what is actually proved
end-to-end; nilpotent → solvable is still open here.

---

## 0.25 Status (2026-08-28, later) — Ikeda is a theorem, and the Schmidt–Wingberg tower, re-costed

Three things happened after §0.24: the split half of the reduction stopped being a hypothesis, the
Schmidt–Wingberg paper was read end to end, and two of its proof devices turned out to be avoidable.

### The reduction, as it now stands

| statement | status |
|---|---|
| `Shafarevich.cyclicWreathEP` | **theorem** (`Ikeda.lean`, `e81f957`, `ce5e2bb`) |
| `Shafarevich.primeWreathEP` | **theorem** |
| `Shafarevich.splitAbelianEP` — Ikeda | **theorem** |
| `Shafarevich.FrattiniKernelEP` | **the one remaining hypothesis** |

`Shafarevich.isInverseGalois_of_isSolvable_of_frattiniKernelEP` now realizes every finite solvable
group over `ℚ` from `FrattiniKernelEP` alone. Upstream of it the chain is Ore → `SplitNilpotentEP`
→ `SplitPrimePowerEP` → `AbelianKernelEP` → `ElementaryAbelianKernelEP` → `FrattiniKernelEP`.

`Shafarevich/Generic.lean` (`8ddc8d7`) adds the first piece of Schmidt–Wingberg's own reduction: the
relatively free operator group `Generic U n S = FreeGroup (Fin n × U) / ⋂ ker(f : · →* S)` with the
`U`-action induced by left translation on the second coordinate, together with

```lean
theorem splitPrimePowerEP_of_genericSplitEP (h : ∀ ℓ : ℕ, GenericSplitEP ℓ) : SplitPrimePowerEP
theorem genericSplitEP_of_splitPrimePowerEP (hℓ : ℓ.Prime) (h : SplitPrimePowerEP) : GenericSplitEP ℓ
```

so the split `p`-group case is *equivalent* to the case of a generic kernel. Forward: the orbit map
`Generic U (Nat.card P) P ↠ P` is `U`-equivariant and surjective, so `Generic ⋊ U ↠ P ⋊[φ] U`.
Backward: `Generic U n S` is itself a finite `ℓ`-group when `S` is.

### The Schmidt–Wingberg dependency map

Schmidt–Wingberg, *Extensions of profinite duality groups* (arXiv `math/9809211`), Theorem 14: every
split embedding problem with finite nilpotent kernel has a proper solution; Theorem 15 is the same
with Scholz conditions attached. The proof is an induction on a two-index filtration `τ = (i,j)`,
each step of which is a *central* embedding problem with elementary abelian kernel
`E(n,τ) = F(n)^{(τ)}/F(n)^{(τ+1)}`, and it has four steps:

1. local split embedding problems at `Ram ∪ S_p ∪ S_∞` — Prop 6 with `T = Ind_{G_𝔭}^G 𝔽_p`;
2. global solvability: the obstruction lives in `Ш²(k, E(n,τ))` and is killed by Prop 6 with
   `T = Hom(μ_p, ℤ/p)`, after a Claim that needs **Tate–Poitou** `Ш²(k,A) ≅ Ш¹(k,A′)^∨`;
3. properness and Scholz condition (i) — Neukirch's principal homogeneous space over
   `H¹(G_k, E(n,τ))`, Lemma 10's injection `coker ↪ Ш¹`, and Prop 7(i);
4. Scholz condition (ii) — Theorem 13 applied to `N_n`, plus Prop 7(ii).

Underneath sit the shrinking propositions: Prop 2 (Chevalley–Warning), Prop 5 (the surjection
`(P/P²)^{⊗j} ↠ P^{(τ)}/P^{(τ+1)}`), Prop 6 and Prop 7 (shrinking in cohomology).

### The induced-module shortcut does **not** work

It is tempting to hope that `E(n,τ)` is an *induced* `𝔽_p[G]`-module, since `F(n)/F(n)²` is
`𝔽_p[G]^n` and Brauer–Hasse–Noether — which this repository has — gives `Ш²(K, 𝔽_p) = 0`, hence
`Ш²(k, Ind_{1}^{G} 𝔽_p) = 0` by Shapiro; that would delete Tate–Poitou from step 2. It fails. The
graded layers of a free (restricted) Lie algebra on a free `𝔽_p[U]`-module are not free: from
`Λ²(A ⊕ B) = Λ²A ⊕ (A ⊗ B) ⊕ Λ²B` the cross term `A ⊗ B` is free, but `Λ²(𝔽_p[U])` is a sum of
modules induced from subgroups of order ≤ 2, and is not free as soon as `U` has an involution. So
`Ш²(k, E(n,τ))` need not vanish and **Tate–Poitou is genuinely required**.

The Hochschild–Serre route is no substitute either: `Ш²(k,A) ⊆ ker(H²(G_k,A) → H²(G_K,A))` does hold
(because `Ш²(K,𝔽_p) = Ш(Br K)[p] = 0`), but inflation only gives
`H²(G,A) → ker → H¹(G, H¹(G_K,A))`, not a surjection onto `Ш²`.

### Two devices that *can* be dropped

**(a) Tate cohomology and dimension shifting are not needed for Props 6 and 7.** Schmidt–Wingberg
prove Prop 6 for `Ĥ^k(G, E(m,τ) ⊗ T)` by shifting down to `k = −1`, where a class is represented by
a module element and Prop 2 applies directly. But the shrinking map `ψ_a` is `G`-equivariant, so it
acts on *cochains*, and a class dies as soon as one representing cochain is annihilated. For a
**finite** `G` a `k`-cochain is a family of `#G^k` module elements, so Prop 2 with `t·#G^k` targets
kills all of them at once — no complete resolution, no dimension shifting, no `Ĥ`. The two indices
actually used are `k = 2` (ordinary cohomology, `2`-cocycles) and `k = −2`, and for a finite group
`Ĥ^{−2}(G,A) = H_1(G,A)` is ordinary group homology, whose `1`-cycles are again finitely many module
elements. Prop 7's group `F(m)/F(m)^{(τ)} ⋊ G` does grow with `m`, which is exactly why it needs its
own argument; but that argument only ever applies the trick to `H_1(G, −)` and to
`H_1(F(n)/τ, E ⊗ T) ≅ F(n)/F(n)² ⊗ E(n,τ) ⊗ T` (universal coefficients, a module), both fine.
What remains needed from homological algebra is therefore: functoriality of `H²` and `H₁` in the
coefficients, and the five-term Hochschild–Serre sequence in homology for a semidirect product.

**(b) The refined `(i,j)` filtration — and with it Lemma 4(ii) and Witt's theorem — can be
dropped.** The refinement `P^{(i,j)} = (P^i ∩ P_j)P^{i+1}` exists to make each graded layer a
quotient of a *single* tensor power, so that `a ↦ ψ_a(z)` is a *homogeneous* form of degree `j`.
Proving that the layer is exactly the length-`j` part is what forces Lemma 4(ii), and Lemma 4(ii) is
Witt's theorem that `F_j/F_{j+1}` is a free `ℤ_p`-module — which Mathlib does not have. But
Chevalley–Warning never asks for homogeneity: it asks for a bound on the total degree and for
vanishing at the origin. On the coarse layer `P^i/P^{i+1}` the class of
`[x_{α₁},…,x_{α_j}]^{p^{i−j}}` transforms by the monomial `a_{k₁}⋯a_{k_j}`, so `a ↦ ψ_a(z)` is a
polynomial with all monomials of degree between `1` and `i`; it vanishes at `a = 0` and has total
degree `≤ i`. That is exactly the hypothesis of `exists_ne_zero_forall_eval_eq_zero`. Only the
*spanning* statement is then needed — `P^i/P^{i+1}` is generated by the images of the
`[x_{α₁},…,x_{α_j}]^{p^{i−j}}`, `1 ≤ j ≤ i` — and spanning follows by induction from the definition
`P^{i+1} = (P^i)^p[P^i,P]` and elementary commutator calculus (Lemma 4(i)), with no freeness input.

### What has landed

* `Shafarevich/Shrink.lean` (`49e31dc`) — Prop 2. `exists_ne_zero_forall_eval_eq_zero`: finitely
  many polynomials over a finite field, vanishing at the origin, with total degrees summing to less
  than the number of variables, have a common nonzero root (Chevalley–Warning plus the observation
  that the solution count is a positive multiple of the characteristic).
  `exists_ne_zero_forall_sum_prod_smul_eq_zero` is the homogeneous form actually quoted by
  Schmidt–Wingberg, stated without `PiTensorProduct` by using the canonical decomposition
  `⨂^s(⊕_r M) ⊗ N ≅ ⊕_{I ∈ (Fin r)^s} (M^{⊗s} ⊗ N)`, under which `ψ_a` is
  `(w_I) ↦ ∑_I a_{I₁}⋯a_{I_s} • w_I`. `sumSmul_surjective` is the accompanying fact that a nonzero
  coefficient vector combines `r` copies of a module onto it.
* `Shafarevich/PCentral.lean` (`82f4176`) — the descending `p`-central series `pCentral p P n`
  (indexed so `pCentral p P 0 = ⊤`), its characteristicity, naturality (`map_pCentral_le`, and
  `map_pCentral`: a surjection carries the series *onto* the series — this is what lets operators
  act on the layers), the two membership rules, monotonicity, and
  `map_pCentral_le_center`: each layer is central in the corresponding quotient.

### What remains

Group-theoretic: the spanning statement for `pCentral` (the coarse Prop 5), and the polynomiality
of `a ↦ ψ_a(z)` on the layer. Homological: functoriality of `H²`/`H₁` in the coefficients and
Hochschild–Serre in homology for `F/τ ⋊ G`, then Props 6 and 7. Arithmetic, and this is the wall:
Hoechsmann's obstruction criterion, Neukirch's principal homogeneous space, Lemma 10, Theorem 13,
and **Tate–Poitou duality with the `Ш` groups** — none of which is in this repository or in Mathlib.

---

## 0.26 Status (2026-08-28, later still) — §2 of Schmidt–Wingberg is complete, and the wall is narrowed to Tate–Nakayama

### The shrinking propositions are all theorems

Everything Schmidt–Wingberg put in their §2 — the part of Theorem 15 that is pure algebra — is now
in the repository, sorry- and axiom-free.

| Schmidt–Wingberg | repository |
|---|---|
| Prop 2 (Chevalley–Warning) | `Shafarevich/Shrink.lean` |
| Prop 5 (layers spanned by tensor powers) | `Shafarevich/PCentralSpan.lean`, `LayerWord.lean` |
| Prop 6 (shrinking in `Ĥ^k(G, E ⊗ T)`) | `Shafarevich/LayerCohomology.lean`, `LayerHomology.lean` |
| Prop 6, arbitrary acting group and tensor coefficients | `Shafarevich/GenericCohomology.lean` |
| Prop 7 (shrinking in `H¹(F(m)/ν ⋊ G, E ⊗ T)`) | `Shafarevich/GenericHomology.lean` |
| `[1] chap. 13 th. 2` (`σ*(ε_n) = π*(ε_m)`) | `CFT/GroupCohomology/ExtensionMap.lean` |

`GenericCohomology.lean` is the form Step 1 needs: the classes to be killed belong to a finite
group *mapping into* the operator group — the decomposition subgroup of a place — and the
coefficients are a layer tensored with a fixed representation. It subsumes the `T = Ind_{G_𝔭}^G 𝔽_p`
formulation without going through Shapiro, because the count never inspects the acting group; it
solves one scalar equation per value taken by the finitely many cocycles, and a cocycle of a finite
group takes `#H^c` values.

`ExtensionMap.lean` is the compatibility that makes the shrinking usable at all: a morphism of
extensions with abelian kernels identifies the class of the upper extension pushed forward along
the map of kernels with the class of the lower one pulled back along the map of quotients, the
trivialising cochain being the comparison of a transported section with a section below.

### The arithmetic wall, located exactly

Step 2 of Theorem 15 needs precisely one thing, its "Claim":

> there is a surjection `Ĥ^{-2}(G, E(-1)) ↠ Ш²(k, E)`, `G = Gal(K|k)`, `E(-1) = E ⊗ μ_p^∨`.

Schmidt–Wingberg get it from `Ш²(k,E) ≅ Ш¹(k,E′)^∨` (Tate–Poitou) together with `Ш¹(K,E′) = 0`,
which forces `Ш¹(k,E′) ⊆ H¹(G,E′)`; dualising and using `H¹(G,M)^∨ ≅ H₁(G,M^∨)` and
`E′^∨ = E(-1)` gives the Claim. Of the three inputs only the first is out of reach:

* `Ш¹(K,E′) = 0` for a **trivial** module is elementary — a cyclic extension in which every prime
  splits is trivial, which is `subsingleton_gal_of_isSolvable_of_splits_outside` in this
  repository. No Chebotarev density is needed.
* `H¹(G,M)^∨ ≅ H₁(G,M^∨)` over `𝔽_p` is finite-group duality, and `Ĥ^{-2} = H₁` is the
  identification already used throughout `Shafarevich/GenericHomology.lean`.

### Narrowing the wall: Tate–Nakayama in place of the nine-term sequence

The Claim does not need the whole Poitou–Tate machine. Unwinding it with Kummer theory:

1. `Ш²(k,E) ⊆ ker(H²(k,E) → H²(K,E))`, because `Ш²(K,E) = Ш(Br K)[p]^d = 0` by
   Albert–Brauer–Hasse–Noether, which this repository has.
2. Hochschild–Serre sends that kernel into `H¹(G, H¹(K,E))`, and Kummer theory rewrites the
   coefficients as `H¹(K,E) ≅ (K^×/K^{×p}) ⊗ E(-1)`.
3. Localisation embeds `(K^×/K^{×p}) ⊗ E(-1)` into `(∏_w K_w^×/K_w^{×p}) ⊗ E(-1)` — injectively,
   by Grunwald–Wang for a squarefree exponent, which is `CFT/GrunwaldWang.lean` — and semi-local
   Shapiro identifies the right-hand `H¹(G, −)` with `∏_𝔭 H¹(G_𝔭, −)`.
4. So the locally trivial classes are the image of the connecting map from `H⁰(G, C ⊗ E(-1))`,
   where `C` is the idele class group modulo `p`-th powers.
5. **Tate–Nakayama** — cup product with the fundamental class — turns `Ĥ⁰(G, C ⊗ E(-1))` into
   `Ĥ^{-2}(G, E(-1))`, which is exactly Schmidt–Wingberg's group.

That is a genuinely smaller target than the nine-term sequence: it needs Tate's theorem for the
*global* class formation, not local Tate duality and not the compact-discrete duality of restricted
products.

### What the repository's class field theory already supplies for that route

| ingredient | status |
|---|---|
| the idele group and the idele class group | `CFT/Units/Idele*.lean` |
| `H¹(Gal(K/k), C_K) = 0`, no hypothesis on the group | `Units/IdeleClassH1Full.lean` |
| first inequality (`#Ĥ⁰(G,C_K) = [K:k]` for cyclic `G`) | `Units/IdeleClassIndex.lean` |
| second inequality | `Kummer/SecondInequality.lean` |
| Hasse norm theorem, Albert–Brauer–Hasse–Noether | `Units/HasseNorm.lean`, `Units/ABHN.lean` |
| Tate cohomology of finite groups, Herbrand, Shapiro, hexagon | `CFT/Tate/` (57 modules) |
| **cup products in group cohomology** | absent |
| **the fundamental class of a class formation** | absent |
| **Tate's cohomological triviality theorem** | absent |
| **Tate–Nakayama** | absent |

The first six rows are the axioms of a class formation, so the missing four are a self-contained
project rather than a new theory: cup products (Mathlib has none for `groupCohomology`), then
Tate's theorem, then the fundamental class, then Tate–Nakayama.

### Two more shortcuts that do not work

* **Inflating the obstruction from a large finite quotient of `G_k`.** One might hope to replace
  `G_k` by a finite quotient `G̃` through which the obstruction is inflated, and then shrink with
  Prop 6 applied to `G̃`. The shrinking bound is `(j+1) · t · #G̃^c · dim(layer ⊗ T) < r`, so the
  rank `r`, hence `m = r·n`, grows with `#G̃`; but the quotient through which a class in `H²(G_k, E(m,ν))`
  is inflated depends on `m`. The argument is circular. This is exactly why Schmidt–Wingberg need a
  source for `Ш²` that lives on the *fixed* finite group `G`.
* **Making the layers induced or projective.** Already refuted in §0.25 for `Λ²`; three further
  attempts fail for the same reason. A free product over a free `G`-set has unordered-pair
  stabilisers of order 2; `Map(G,P) ↠ P` is not equivariant for nonabelian `P`, so
  Kaloujnine–Krasner only embeds; and `𝔽_p[U]` is semisimple only when `p ∤ #U`, a case the
  reduction cannot be steered into.

---

## 0.27 Status (2026-08-29) — three of the four missing rows are theorems; Tate–Nakayama is unconditional for flat coefficients

The four rows marked *absent* in the table of §0.26 have been reduced to one and a half.

### Cup products: bypassed, not built

Mathlib has no cup product for `groupCohomology`, and none was written. Instead of cupping with a
2-cocycle, dimension-shift once and cup with a **1-cocycle**, which is nothing but an extension:
`TateCohomology/CocycleExtension.lean` builds `cocycleObj A b` with carrier `A.V × k` and action
`ρ τ (m,c) = (A.ρ τ m + c · b τ, c)`, sitting in a short exact sequence `0 → A → cocycleObj → k → 0`
whose connecting map sends the canonical generator of `Ĥ⁰(H,ℤ)` to the class of `b`. Every use of a
cup product in Tate's theorem and in Tate–Nakayama goes through that extension instead.

### Tate's theorem and cohomological triviality

* `TateCohomology/SylowTrivial.lean`: `isZero_tateModule_of_sylow` — vanishing in **two consecutive
  degrees on a Sylow subgroup for every prime** forces vanishing in every degree. This is Tate's
  cohomological-triviality theorem; the `p`-group core is `CohomTrivial.lean` + `TorsionFree.lean` +
  `PTorsionTrivial.lean` + `PGroupTrivial.lean`.
* `TateCohomology/TateTheorem.lean`: `IsTateClass H A b` (the classical hypotheses in degrees zero
  and one on the restriction) on every Sylow gives `tateTheoremEquiv : Ĥⁿ(G,ℤ) ≅ Ĥⁿ⁺¹(G,A)`.
* `TateCohomology/TateDegreeTwo.lean`: the classical degree-two form, `IsTateClassTwo H A α` and
  `tateTheoremTwoEquiv : Ĥⁿ(G,ℤ) ≅ Ĥⁿ⁺²(G,A)`.

### Tate–Nakayama

`TateCohomology/TateNakayama.lean` gives `tateNakayamaEquiv : Ĥⁿ(G,M) ≅ Ĥⁿ⁺²(G, A ⊗ M)` under the
single hypothesis that the splitting extension stays cohomologically trivial after tensoring with
`M`. `TateCohomology/TensorFunctor.lean` and `TateCohomology/TensorTrivial.lean` discharge that
hypothesis whenever `M` is **flat over ℤ**:

* multiplication by a natural number commutes with tensoring, so the reduction sequence modulo `p`
  stays short exact after tensoring with a flat module;
* the reduction of a cohomologically trivial representation is killed by `p` and has no first
  cohomology, hence is the functions on the group, and those stay acyclic after tensoring
  (projection formula);
* the torsion hypothesis is removed by covering with a free induced representation, whose kernel is
  automatically torsion-free;
* restriction commutes with tensoring, so the argument runs on the Sylow subgroups.

The upshot is `tateNakayamaFlatEquiv`: for `M` flat over ℤ, **no hypothesis is left over**.

### The remaining half-row, stated exactly

Let `E` be cohomologically trivial with `pd_{ℤ[G]} E ≤ 1` and `0 → P₁ → P₀ → E → 0` a projective
resolution. Tensoring over ℤ with `M` gives `Ĥⁿ(E ⊗ M) ≅ Ĥⁿ⁺²(Tor₁^ℤ(E,M))`, so

> `E ⊗ M` is cohomologically trivial **iff** `Tor₁^ℤ(E,M)` is.

That is why the classical statement assumes `M` torsion-free, and it is what the flat case above
proves. Step 5 of the route in §0.26 applies Tate–Nakayama with `M = E(-1)`, which is **finite
`p`-torsion**, so `Tor₁(C_K, M) = C_K[p] ≠ 0` and the flat theorem does not apply. Two outs, neither
explored:

* only a **surjection** `Ĥ^{-2}(G,E(-1)) ↠ Ĥ⁰(G, C ⊗ E(-1))` is needed, and by the long exact
  sequence that needs only the single vanishing `Ĥ²(Tor₁(C_K,M)) = 0`;
* prove Serre's `cohomologically trivial ⟺ pd ≤ 1` and run the argument on a ℤ-free lift of `E(-1)`.

### Next target

The **fundamental class of the global class formation**: `Ĥ¹(H,C_K) = 0` is in
`Units/IdeleClassH1Full.lean`, and what is missing is that `Ĥ²(H,C_K)` is cyclic of order `#H`
generated by the restriction of a global class — that is, the invariant map. The repository has
`Local/UnramifiedInvariant.lean` (the unramified cyclic case), `Units/ABHN.lean`,
`Units/HasseNorm.lean`, `Units/FirstInequality.lean`, `Kummer/SecondInequality.lean` and the 43
modules of `Brauer/`. Once `IsTateClassTwo` is verified for `C_K`, `tateNakayamaFlatEquiv` applies
verbatim to every lattice of coefficients.

---

## 0.28 Status (2026-08-29, later) — Tate–Nakayama for `p`-torsion coefficients, and the reason it cannot be made unconditional

§0.27 left the flat case as the only reachable one. It is not: the *opposite* extreme — coefficients
killed by a prime, which is exactly what step 5 of the §0.26 route needs — is now also a theorem,
`InverseGalois/CFT/TateCohomology/TensorPTorsion.lean`, modulo **one** concrete vanishing.

### What landed

* `nsmul_tensorObj_eq_zero`, `nsmul_tensorObj_eq_zero'` — a tensor product one of whose factors is
  killed by `m` is killed by `m` (the number moves onto that factor).
* `isZero_tateModule_of_nsmul_eq_zero_coprime` — a representation killed by `m` with
  `gcd(m, #G) = 1` has no complete cohomology: `#G` annihilates every degree too, and Bézout
  finishes. So for coefficients killed by `p`, only the Sylow `p`-subgroup can carry anything.
* `isoOfBijective`, `bijective_tensorHomLeft_nsmulSeq_g`, `tensorModNsmulIso` — **reduction modulo
  `m` becomes an isomorphism after tensoring with a representation killed by `m`**: right exactness
  keeps it surjective, and its kernel is the image of multiplication by `m`, which is zero on the
  tensor product. So `E ⊗ M ≅ (E/mE) ⊗ M` whenever `mM = 0`.
* `isZero_tateModule_tensorObj_of_nsmul` — a representation `N` killed by `p` whose restriction to
  a Sylow `p`-subgroup has `H¹ = 0` satisfies: `N ⊗ M` is cohomologically trivial **for every** `M`.
  (`p`-Sylow: `N` is the functions on the group, and the projection formula; other Sylows: coprime
  orders.)
* `isZero_tateModule_tensorObj_of_nsmul_eq_zero` — combining the two: if `Ĥ¹(P, E/pE) = 0` for a
  Sylow `p`-subgroup `P`, then `E ⊗ M` is cohomologically trivial for every `M` killed by `p`.
* `isZero_tateModule_tensorObj_of_torsionFree_nsmul` — when `p` acts on `E` without torsion the
  hypothesis is automatic: `0 → E →ᵖ E → E/pE → 0` is short exact, so `E` cohomologically trivial
  forces `Ĥ¹(E/pE) = 0`.
* `tateNakayamaPTorsionEquiv` — **Tate–Nakayama for coefficients killed by a prime**, with the
  single hypothesis `Ĥ¹(P, Ê/pÊ) = 0` on the splitting module `Ê = cocycleObj (shiftObj A) b`.

### The hypothesis is genuine — an explicit counterexample

It is tempting to hope that `E` cohomologically trivial already forces `E/pE` cohomologically
trivial, which would make Tate–Nakayama unconditional for `p`-torsion coefficients. **It does not.**

Take `G = ℤ/2 = ⟨σ⟩`, `R = ℤ[G]`, and `r = 1 + 3σ`. Multiplication by `r` on `R` has matrix
`[[1,3],[3,1]]` in the basis `1, σ`, of determinant `-8 ≠ 0`, so it is injective, and

```
0 → R --·r--> R → E → 0,      E := R/rR
```

is a projective resolution of length 1. Hence `Ĥⁿ(H,E) = 0` for every `H ≤ G` and every `n`: `E` is
cohomologically trivial. Smith normal form gives `E ≅ ℤ/8` as an abelian group, with `σ` acting by
multiplication by `5` (from `x + 3σx = 0` and `3⁻¹ = 3` mod `8`). Checked directly: `E^G = 2ℤ/8`,
`N E = 6·ℤ/8 = 2ℤ/8`, so `Ĥ⁰ = 0`; `ker N = {0,4} = (σ-1)E`, so `Ĥ¹ = 0`.

But `E/2E = R/(r,2) = 𝔽₂[σ]/(1+σ) ≅ 𝔽₂` with **trivial** action (`5 ≡ 1` mod `2`), and
`Ĥ⁰(ℤ/2, 𝔽₂) = 𝔽₂/N𝔽₂ = 𝔽₂ ≠ 0`. So `E/2E` is *not* cohomologically trivial.

Consequences:

* out (b) of §0.27 is dead in its naive form: no lifting trick will remove the hypothesis, because
  the statement it would prove is false;
* the classical Tor hypothesis in Tate–Nakayama is not an artefact of the classical proof;
* what remains for step 5 of §0.26 is therefore an honest arithmetic question, and it is now a
  *single* one: `Ĥ¹(P, Ê/pÊ) = 0` for `Ê` the splitting module of the global fundamental class.
  Equivalently (dimension shift) `Ĥ³(P, Ê[p]) = 0`, and `Ê[p]` is a shift of `C_K[p]`.

### Next target, unchanged

Still the **fundamental class of the global class formation** (§0.27). Everything downstream of it
is now in place for both flat and `p`-torsion coefficients.

---

## 0.29 Status (2026-08-29, later still) — Tate's hypotheses reduced to a count, and a map of the remaining arithmetic

### What landed

`InverseGalois/CFT/TateCohomology/TateClassCount.lean` — the *abstract* half of the fundamental
class. It removes every mention of the restricted class from the hypotheses of Tate's theorem:

| name | statement |
| --- | --- |
| `exists_zsmul_of_card_eq` | an element of a finite commutative group annihilated by exactly the multiples of `Nat.card M` generates `M` |
| `dvd_of_zsmul_tateRes_eq_zero` | if `m • α = 0 ⟹ #G ∣ m`, then `m • res_H α = 0 ⟹ #H ∣ m` |
| `isTateClassTwo_of_card` | `IsTateClassTwo H A α` from `Ĥ¹(H,A) = 0`, `#Ĥ²(H,A) = #H` (finite), and `m • α = 0 ⟹ #G ∣ m` |
| `tateTheoremTwoEquivOfCard` | Tate's theorem from that count |
| `tateNakayamaFlatEquivOfCard` | Tate–Nakayama (flat coefficients) from that count |

The order transfer in `dvd_of_zsmul_tateRes_eq_zero` needs **no** Sylow-specific input, only that
`tateRes` is linear and that `cor ∘ res = ·[G:H]`: from `m • res α = 0` one gets
`res (m • α) = 0`, hence `[G:H] • (m • α) = 0` by `index_smul_eq_zero_of_tateRes_eq_zero`, hence
`#G ∣ [G:H]·m`, and `#H · [G:H] = #G` cancels the index. So the hypothesis of Tate's theorem on
*every* subgroup at once follows from one global order statement plus one count per subgroup.

That is exactly the shape in which a class formation presents its fundamental class, so what is
left of §0.27 is now a purely arithmetic list:

1. `Ĥ¹(H, C_K) = 0` — **the repo has this** (`eq_zero_H1_res_subgroup`,
   `eq_zero_H1_ideleClassRep_general`, `subsingleton_H1_ideleClassRep_general`), modulo the
   transport `resObj H (ideleClassRep k K) ↔ ideleClassRep (fixedField H) K`, whose pattern is
   already written out inside `eq_zero_H1_res_subgroup`.
2. `#Ĥ²(H, C_K) = #H` — **missing**.
3. a global `α ∈ Ĥ²(Gal(K/k), C_K)` annihilated only by multiples of `#Gal(K/k)` — **missing**.

Both missing items are the **invariant map**, and nothing weaker will do: see below.

### Counting cannot replace the invariant map

It is tempting to hope that `#Ĥ²(H,C_K) = #H` plus Sylow bookkeeping gives cyclicity for free.
It does not. Two observations, both negative:

* For a Sylow `p`-subgroup `P ≤ G` with `#Ĥ²(H,C) = #H` for all `H`, restriction *is* an
  isomorphism `Ĥ²(G,C)(p) ≅ Ĥ²(P,C)` (because `cor ∘ res` is multiplication by an index prime to
  `p`), and a global `α` of order `#G` restricts to an element of order `#P` (the other primary
  parts restrict to zero). So the global statement and the Sylow statements are equivalent — but
  that is a *transfer*, not a *proof*: something still has to produce cyclicity somewhere.
* Cyclicity of `Ĥ²(P,C_K)` itself does not follow from counting. Inflation–restriction on a chain
  `1 ◁ P' ◁ P` only exhibits `Ĥ²(P,C)` as an extension of `ℤ/#P'` by `ℤ/p`; every group of order
  `p²` is such an extension. One genuinely needs a homomorphism `Ĥ²(P,C) → (1/#P)ℤ/ℤ` that is
  injective, i.e. the **invariant map**.

### The one local brick that is missing

The invariant map is built from the local ones, and the repo's local half is already substantial:

* `unramifiedInvariant`, `unramifiedInvariant_surjective/_injective`, `unramifiedInvariantEquiv`
  (`CFT/Local/UnramifiedInvariant.lean`) — the invariant on the *unramified* part;
* `subsingleton_tateH0_kerUnitValAut`, `subsingleton_tateHm1_kerUnitValAut`
  (`CFT/Local/UnramifiedUnits.lean`), `herbrand_kerUnitValAut_eq_one`,
  `herbrand_smulUnitsAut_eq_card` (`CFT/Local/UnitHerbrandChain.lean`),
  `index_normSubgroup_eq_finrank_of_complete` (`CFT/Local/CompleteNormIndex.lean`) — the local norm
  index and the Herbrand quotient of the units;
* `brauerHom`, `brauerHom_injective` (`CFT/Brauer/H2Brauer.lean`), `cyclicBrauerHom`,
  `mem_ker_cyclicBrauerHom_iff` (`CFT/Brauer/CyclicBrauer.lean`),
  `exists_intermediateField_mem_relative`, `iSup_relative_eq_top`
  (`CFT/Brauer/MaximalSubfield.lean`), `card_relative_le_finrank_of_isLocalExtension`
  (`CFT/Brauer/LocalBrauerBound.lean`) — the Brauer-group dictionary.

The brick that is absent, and on which the whole invariant map rests, is:

> **every Brauer class over a complete discretely valued field with finite residue field is split
> by an unramified extension.**

The classical proof is by division algebras: extend the valuation of the base to a central division
algebra `D`, observe that the residue division ring is finite hence a field by Wedderburn, deduce
`e = f = d` for `d² = dim D`, and conclude that an unramified maximal subfield splits `D`. That is
a self-contained project of a few files, and it is the *only* remaining input for item 2 above; the
global invariant then follows from `⊕_v Br(K_w/k_v)` with semi-local Shapiro,
`exists_sub_add_eq_globalUnits` (ABHN, `CFT/Units/ABHN.lean`) and Hilbert reciprocity, plus the
surjection `H²(G, I_K) ↠ H²(G, C_K)`.

### A re-analysis of §0.26 step 5 — and why "out (a)" is *not* free

Two structural findings about the Schmidt–Wingberg argument, recorded so they are not rediscovered.

**(i) Steps 3–5 can be run entirely over `𝔽_p`.** The sequence

```
0 → K^× / p → I_K / p → C_K / p → 0
```

is exact — left exactness is precisely Grunwald–Wang, which the repo already has in power-class
form (`CFT/GrunwaldWang.lean`). All three terms are `𝔽_p`-vector spaces, so `⊗_{𝔽_p} E(-1)` is
exact on it, and one gets `Ш²(k, E) ⊆ im δ` with `δ` the connecting map out of
`Ĥ⁰(G, C_K ⊗ E(-1))`. No integral bookkeeping is needed anywhere in steps 3–5.

**(ii) The lattice-presentation route needs only the *flat* Tate–Nakayama — but it does not close.**
Choose a free presentation of `𝔽_p[G]`-modules over `ℤ[G]`,

```
0 → N → ℤ[G]^r → E(-1) → 0,
```

with `N` a lattice. Dimension shifting gives `Ĥ^{-2}(G, E(-1)) ≅ Ĥ^{-1}(G, N)`, and since
`ℤ[G]^r ⊗ C_K` is induced hence acyclic, `Ĥ⁰(G, E(-1) ⊗ C_K) ≅ Ĥ¹(G, Q)` where
`Q = ker(ℤ[G]^r ⊗ C_K → E(-1) ⊗ C_K)`. Surjectivity of `Ĥ¹(N ⊗ C_K) → Ĥ¹(Q)` — which is what the
Claim of §0.26 asks for — would then need only

```
Ĥ²(G, T) = 0,   T = Tor₁^ℤ(E(-1), C_K).
```

Every module in sight is a lattice, so this route uses **only** `tateNakayamaFlatEquiv` (§0.27) and
never the `p`-torsion version of §0.28. That is the good news. The bad news is that the required
vanishing is generally **false**:

```
T ≅ C_K[p] ⊗_{𝔽_p} E(-1),      C_K[p] ≅ (∏_v μ_p(K_v)) / μ_p(K)
```

(the term `ker(K^× / p → 𝔸^× / p)` dies by Grunwald–Wang), and
`∏_v μ_p(K_v) = ∏_𝔭 Ind_{G_𝔭}^G μ_p`, so by Shapiro

```
Ĥ²(G, C_K[p] ⊗ E(-1)) = ∏_𝔭 Ĥ²(G_𝔭, E)   (up to the μ_p(K) correction),
```

which is a product of *local* `Ĥ²`'s and is nonzero in general. **So "out (a)" of §0.26 is not
free**, and the lattice route does not shortcut Poitou–Tate.

**(iii) The Claim really is Poitou–Tate.** The statement `Ĥ^{-2}(G, E(-1)) ↠ Ш²(k, E)` is exactly
the dual of the inclusion `Ш¹(k, E′) ⊆ H¹(G, E′)`. There is no cheaper reformulation hiding in it;
the nine-term Poitou–Tate sequence (or at least the `Ш¹`–`Ш²` duality inside it) is a genuine
prerequisite for Schmidt–Wingberg Theorem 15, and is a separate project from the fundamental class.

### Consequence for the plan

The dependency graph for the last hypothesis (`FrattiniKernelEP` ≡ SW Thm 14/15) is therefore:

```
                       local: unramified splitting of a Brauer class   [MISSING, ~few files]
                                          ↓
                       invariant map → #Ĥ²(H,C_K) = #H, α of order #G
                                          ↓  (TateClassCount.lean — DONE)
                       fundamental class = IsTateClassTwo on every Sylow
                                          ↓  (TensorTrivial / TensorPTorsion — DONE)
                       Tate–Nakayama for the coefficient modules of SW §2
                                          ↓
     Poitou–Tate / Ш¹⊆H¹ duality  [MISSING, separate project]  →  SW Thm 13 → Thm 15
```

Two independent missing bricks, both classical, neither small. The abstract cohomological
machinery between and after them is now complete and unconditional.

---

## 0.30 Status (2026-08-29, night) — **the degree-two count is done**: two of the three class-formation conditions are unconditional

Item 2 of §0.29 — `#Ĥ²(H, C_K) ≤ #H` for **every** subgroup `H ≤ Gal(K/k)` and **every** Galois
extension of number fields — is now a theorem, sorry- and axiom-free. Note that the *inequality* is
all that `isTateClassTwo_of_card_le` wants: the reverse inequality comes for free from a class `α`
of order `#G`, whose multiples already fill `#G` elements. So §0.29's list now reads

1. `Ĥ¹(H, C_K) = 0` — **done** (`isZero_tateModule_resObj_ideleClassRep_one`);
2. `#Ĥ²(H, C_K) ≤ #H` — **done** (`card_tateModule_resObj_ideleClassRep_two_le`);
3. a global `α ∈ Ĥ²(Gal(K/k), C_K)` annihilated only by multiples of `#Gal(K/k)` — **missing**, and
   still exactly the invariant map, resting on the one local brick of §0.29.

`isTateClassTwo_ideleClassRep`, `tateIdeleClassEquiv` and `tateNakayamaIdeleClass`
(`CFT/Units/IdeleClassTate.lean`) therefore now carry **`hα` as their only hypothesis**.

### The two dévissages

Everything is bootstrapped from the cyclic count `#Ĥ²(C_K) = #Gal(K/k)`
(`card_H2_ideleClassRep_cyclic`, §0.24 era) by two reductions, each split into an abstract module
and its arithmetic instance.

| module | content |
| --- | --- |
| `CFT/GroupCohomology/H2Transport.lean` | `H²` transported along `e : G ≃* G'` compatible with `φ : A ≃+ B`; gives `card_H2_eq_of_addEquiv`, `finite_H2_of_addEquiv` (and the `Rep k G` universe-polymorphic versions) |
| `CFT/GroupCohomology/H2Devissage.lean` | counting inflation–restriction: `finite_and_card_H2_le_of_devissage` — for `π : G ↠ G'` with `B ↪ A` identifying `B` with `A^{ker π}`, and `Ĥ¹(ker π, A) = 0`, one has `#H²(G,A) ≤ #H²(G',B) · #H²(ker π, A)` |
| `CFT/GroupCohomology/H2Sylow.lean` | `finite_and_card_H2_le_of_sylow` — `H²(G,A) ↪ ∏_p H²(P_p, A)` by `eq_zero_of_forall_prime_res`, and `∏_p #P_p = #G` |
| `CFT/Units/IdeleClassH2Tower.lean` | the arithmetic instance of the dévissage: `galRestrictKerEquiv` identifies `Gal(K/F)` with `ker(Gal(K/k) ↠ Gal(F/k))`, `ideleClassComapLin` identifies `C_F` with `C_K^{Gal(K/F)}`, giving `finite_and_card_H2_ideleClassRep_of_tower` |
| `CFT/Units/IdeleClassH2Full.lean` | the induction: prime-power degree by `Sylow.exists_subgroup_card_pow_prime` + `Subgroup.normal_of_index_eq_minFac_card` (cyclic degree `p` at the bottom, `p^n` on top, and `p · p^n = p^{n+1}` is *exact*, so no slack accumulates), then the general case by Sylow, since `Ĥ²` restricted to `S` is `Ĥ²` over `fixedField S` |

The shape deliberately mirrors the degree-one story of §0.24 (`H1Transport` / `IdeleClassTower` /
`IdeleClassH1Full`); the only genuinely new ingredient is that the tower step now needs the
*vanishing* of `Ĥ¹` over the middle field as an input, which is exactly what the degree-one story
delivers.

### Two Lean gotchas worth keeping

* **`Rep.ρ` vs `Action.ρ`.** Writing the type `((Action.res _ S.subtype).obj A).ρ s a` makes `.ρ`
  resolve to `Action.ρ`, whose value is a `CategoryTheory.End` and is *not* a function. The fix used
  throughout is a `noncomputable abbrev` whose **declared type** is `Rep ℤ ↥S` (`ideleClassRepRes`,
  `ideleClassRepKer`); being an `abbrev` it still unifies with the unfolded form.
* **`Module ℤ` diamonds.** Relating a `Rep ℤ` carrier to an invariants submodule through `≃ₗ[ℤ]`
  produces mismatched `Module ℤ` instances; stating the transport with `≃+` and converting via
  `AddEquiv.toIntLinearEquiv` (whose `Module ℤ` argument is implicit) avoids it.

---

## 0.31 Status (2026-08-29, later) — the local brick is closed, and the route to `α` is re-planned (one claim of §0.29 was wrong)

### What landed

| module | content |
| --- | --- |
| `CFT/Local/NormValued.lean` | **going up.** `normValuation K L` is the valuation `y ↦ v(N_{L/K} y)`; carried on `spectralNorm.uniformSpace K L` it is a *topological* valuation (`normValued`), so a finite extension of a complete, discretely valued, locally compact field is again one. Plus: `valued_algEquiv_of_norm` (automorphisms preserve it, free from `Algebra.norm_eq_of_algEquiv`), `hasResidueChar_of_norm`, `isUnramifiedValued_of_norm`, and `finite_gradedAdd_of_properSpace` — the graded pieces are finite because `valAddSubgroup` is a **closed ball** (compact by `ProperSpace`) whose next step is **open**, so the quotient is discrete and compact. The old `GradedFinite.finite_gradedAdd` is unusable here: it wants a uniformizer of value exactly `exp(-1)`, and the norm valuation's value group is a proper subgroup of `ℤ`. The package is `exists_valued_of_spectralNorm`. |
| `CFT/Brauer/LocalBrauerOrder.lean` | `card_relative_eq_finrank_of_spectralNorm`, `exists_cyclic_relative_card_eq_finrank`, `..._adicCompletion`: **every Brauer class over a complete, discretely valued, locally compact field lies in a relative Brauer group of exactly the order of the degree.** |

So the node §0.29 called *"local: unramified splitting of a Brauer class"* is closed: the splitting
field exists (`exists_cyclic_unramified_mem_relative`, §0.29 era) **and** it is a local field again
with `#Br(L/K) = [L:K]`.

### The base field is `ℚ`, and that is a large simplification

Every hypothesis in the reduction chain is stated over `ℚ`: `GenericSplitEP`, `SplitPrimePowerEP`,
`ElementaryAbelianKernelEP`, `FrattiniKernelEP` all quantify over `IsInverseGalois` (Galois group
**over `ℚ`**). And `isTateClassTwo_ideleClassRep` takes `hα` **only for the full group** — the
subgroup conditions are derived from the counting. So the single missing statement is

> `∃ α ∈ Ĥ²(Gal(K/ℚ), C_K)` with `∀ m : ℤ, m • α = 0 → ([K:ℚ] : ℤ) ∣ m`, for every Galois `K/ℚ`,

equivalently `Ĥ²(Gal(K/ℚ), C_K) ≅ ℤ/[K:ℚ]` (the order is already `≤ [K:ℚ]`). Consequently the
**local invariant maps that are needed are only `inv_p : Br(ℚ_p) → ℚ/ℤ` and `inv_∞ : Br(ℝ) → ℚ/ℤ`**
— not local class field theory over an arbitrary local field. Over `ℚ_p` the unramified extensions
are `ℚ_p(ζ_m)`, `p ∤ m`, with Frobenius `ζ ↦ ζ^p`, and every abelian extension of `ℚ` is cyclotomic
(`CFT/KroneckerWeber.lean`), so the whole invariant/reciprocity layer can be kept cyclotomic.

### A correction to §0.29: `Ĥ²(G, I_K) ↠ Ĥ²(G, C_K)` is **false** in general

§0.29 lists "plus the surjection `H²(G, I_K) ↠ H²(G, C_K)`" as if it were free. It is not, and it is
not even true. From `1 → K^× → I_K → C_K → 1` the cokernel of that map injects into
`H³(G, K^×)`, and `H³(G, I_K) = ⊕_v H³(G_w, K_w^×) = 0` (local duality: `Ĥ³ ≅ Ĥ¹(G_w, ℤ) = 0`), so

```
coker( Ĥ²(G, I_K) → Ĥ²(G, C_K) )  ≅  H³(G, K^×)  ≅  ℤ/(n/m),   m = lcm_v [K_w : k_v].
```

**Counterexample.** `K = ℚ(√5, √41)`, `G = (ℤ/2)²`, `n = 4`. Both `5` and `41` are `≡ 1 mod 4`, and
`41 ≡ 1 mod 5` makes `41` a square mod `5` (hence `5` a square mod `41`), so at `5` and at `41`
only one of the two quadratic subfields ramifies and the decomposition group has order `2`; at `2`
and at `∞` the extension is unramified/split. So every `n_v ≤ 2`, `m = 2 < 4 = n`, and the map is
not onto. The fundamental class of such a `K/ℚ` genuinely does **not** come from ideles at level
`K`.

It *is* onto when `G` is **cyclic**, since then `H³(G, K^×) ≅ Ĥ¹(G, K^×) = 0` by Hilbert 90 and
two-periodicity. That is the only case in which the idele-theoretic description may be used
directly.

### The corrected route to `α`

Write `Inv : Ĥ²(G_ℚ, C) → ℚ/ℤ` for the map induced by `Σ_p inv_p` on ideles. The two properties to
prove are **well-definedness (reciprocity)** and **injectivity**, and then everything follows
formally:

* `inv_K ∘ res^{G_ℚ}_{G_K} = [K:ℚ] · Inv` (from `inv_w ∘ res = [K_w:k_v] · inv_v` locally);
* pick `x` with `Inv x = 1/n`; then `inv_K(res_K x) = 0`, so `res_K x = 0` by injectivity over `K`,
  i.e. `x ∈ H²(K/ℚ) = Ĥ²(Gal(K/ℚ), C_K)` (inflation is injective because `Ĥ¹ = 0`);
* `x` has order `n` because `Inv` is injective. **That is `α`.**

Injectivity can be bought by **counting** rather than by the Hasse principle: for a *cyclic* `L/F`
of degree `d`, `#Ĥ²(Gal(L/F), C_L) = d` exactly — the second inequality gives `≤` and the **first
inequality is already in the repo** (`CFT/Units/FirstInequality.lean`:
`herbrand_ideleClassAut_eq_degree`, `first_inequality`, plus two-periodicity `CFT/Tate/Hexagon.lean`)
gives `≥`. Since `Ĥ²(G, I_L) ↠ Ĥ²(G, C_L)` in the cyclic case and `Inv` is onto `(1/m)ℤ/ℤ`, a place
of full local degree forces `Inv` to be an isomorphism on `Ĥ²(Gal(L/F), C_L)`, hence injective
there. Every element of `Ĥ²(G_ℚ, C)` is split by a cyclic cyclotomic extension, which is where
`CFT/Cyclotomic/Chebotarev.lean` (cyclotomic Chebotarev over `ℚ`) and the classical device
"`ord_{p^r}(ℓ) → ∞`, so the cyclic degree-`p^r` subfield of `ℚ(ζ_{p^{r+1}})` has large local degree
at any fixed finite set of primes" come in.

So **ABHN is not needed for `α`**; reciprocity is. There is no way around reciprocity: the
statement "`a ∈ ℚ^×` is a local norm from a cyclic `K` at every place but one, hence at that one
too" is equivalent to it, and it is exactly what makes `C_ℚ / N C_K` *cyclic* rather than merely of
order `n` (see §0.29's two negative observations).

### Next targets, in order

1. `inv_p : Br(ℚ_p) → ℚ/ℤ`, built on the unramified tower `ℚ_p(ζ_{p^n-1})` with its Frobenius
   normalization, together with `inv ∘ res = f · inv`; and `inv_∞` on `Br(ℝ) = ℤ/2`.
2. Reciprocity `Σ_v inv_v = 0` on `Br(ℚ)`, by Kronecker–Weber: every class is a cyclotomic cyclic
   algebra, and the product formula for the cyclotomic norm-residue symbol is explicit.
3. The assembly above, giving `hα` and therefore the class formation.
4. Poitou–Tate / `Ш¹ ⊆ H¹` duality — still a separate project.

---

## 0.32 Status (2026-08-29) — the Frobenius normalization: what landed and what is left

Target 1 of §0.31 needs a **canonical** generator of `Gal(L/K)` for an unramified local extension:
`brauerInvariant hσ₀ hur hm` depends on the chosen generator `σ₀`, and replacing `σ₀` by `σ₀^k`
rescales the invariant.  (`normQuotientValInvariant : Kˣ/N(Lˣ) ≅ (1/n)ℤ/ℤ` is already canonical,
so the whole canonicity gap is the choice of `σ₀`.)  This section records the reduction.

### The local formalism to work in

There are two parallel local layers in the repo.  The Brauer-invariant layer lives in the **normed**
one — `[NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]`, `divisionNorm`,
`spectralNorm` — and *unramifiedness* there is the statement produced by the splitting theory of
division algebras,

```
hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖
```

("every absolute value is already the absolute value of a scalar", i.e. `e = 1`).
`Brauer/AdicUnramified.lean` bridges this to the `Valued A ℤᵐ⁰` layer.  The Teichmüller lift is
`Brauer/DivisionTeichmuller.lean`'s `exists_rootOfUnity_pow_divisionNorm_sub_lt_one`, in the normed
layer already — a duplicate in the `Valued` layer is not needed.

### Landed

* `Brauer/UnramifiedAdjoin.lean`
  * `isDivisionUniformizer_algebraMap` — under `hur` a uniformizer of `K` **is** a uniformizer of
    `L`.  (This is the whole force of `e = 1`: an element of absolute value `< 1` has the absolute
    value of a scalar of absolute value `< 1`.)
  * `exists_adjoin_rootOfUnity_eq_top_of_unramified` — **`L = K(ζ)`** for the Teichmüller root of
    unity `ζ` of order `N := #𝓀_L − 1`.  Proof: the powers of `ζ` cover every residue, so
    `finrank_le_mul_of_divisionNorm_eq_pow` (`Brauer/DivisionMaximal.lean`, which needs **no**
    centrality) applies to the subalgebra `M = K[ζ]` with `m = 1`, giving `[L:K] ≤ [M:K]`.
  * `algEquiv_eq_of_apply_eq_of_adjoin_eq_top` — an automorphism is determined by its value on `ζ`.
* `Brauer/UnramifiedAut.lean`
  * `exists_isPrimitiveRoot_adjoin_eq_top_of_unramified`, and `autToPow_injective`: the Mathlib
    monoid hom `IsPrimitiveRoot.autToPow K hζ : (L ≃ₐ[K] L) →* (ZMod N)ˣ` is **injective**.
  * `mul_comm_algEquiv_of_unramified` — the automorphism group of an unramified local extension is
    **commutative**.
  * `isCyclic_algEquiv_of_unramified` — it is in fact **cyclic**.  This one is a two-line corollary:
    `Brauer/DivisionCyclic.lean` already had the residue functor and the faithfulness of the action
    on the residue field (`divisionResidueHom`, `divisionResidueHom_comp`, `divisionResidueAut`,
    `divisionResidueAut_injective`, `isCyclic_algEquiv_of_rootOfUnity`,
    `norm_natCast_card_divisionResidue_sub_one`), and was missing only the input `L = K(ζ)`.
    ⚠️ Do **not** re-derive the residue functor: a from-scratch `Brauer/DivisionResidueAut.lean`
    written on 2026-08-29 was an exact duplicate of `DivisionCyclic.lean:126-190` and was deleted.

So `Gal(L/K) ↪ (ℤ/N)ˣ` canonically (the exponent `a(σ)` with `σζ = ζ^{a(σ)}` does not depend on the
choice of the generator `ζ` of `μ_N`), and the Frobenius is *by definition* the element with
`a(σ₀) = q`, where `q := #𝓀_K`.

### The one remaining input

That `σ₀` **generates** `Gal(L/K)`, equivalently the fundamental identity in the unramified case

```
f := [𝓀_L : 𝓀_K] = [L : K] =: n      (given e = 1)
```

Two half-arguments are available and neither is free:

* `n ≤ f`.  `divisionResidueAut_injective` already gives `Gal(L/K) ↪ RingAut 𝓀_L`, whose order is
  `f' := log_p #𝓀_L`; that only yields `n ≤ f'`.  Sharpening to `n ≤ f` needs the *relative*
  statement, i.e. a `𝓀_K`-algebra structure on `DivisionResidue K L` coming from
  `DivisionResidue K K → DivisionResidue K L`, plus `Gal(𝓀_L/𝓀_K) ≅ ℤ/f`.
* `f ≤ n`.  `𝓀_L = 𝓀_K[z]` and `z` kills the reduction of `minpoly K ζ`, whose coefficients are
  integral because `spectralNorm = spectralValue (minpoly K ·)`.

An alternative that avoids the residue-field functor: Mathlib's
`Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`
(`Mathlib/NumberTheory/RamificationInertia/Basic.lean:966`) is exactly `e · f = n` for a local
`S`, but it wants `IsDedekindDomain`, `IsIntegralClosure S R L` and `Module.Finite R S` — i.e. the
DVR packaging of `𝒪_K ⊆ 𝒪_L`, which is a comparable amount of plumbing in the *other* formalism.

Note that canonicity does **not** actually need `f = n`: `Gal(L/K) ↪ (ℤ/N)ˣ` already pins every
element down, and the unique preimage of `Frob_q^{f/n}` is a canonical generator.  What `f = n`
buys is that this generator is the *Frobenius*, which is what makes `inv ∘ res = f · inv` come out
right on a tower.

---

## 0.33 Status (2026-08-29, night) — `f = n` is a theorem, the Frobenius is canonical, and the normalized invariant exists

§0.32's "one remaining input" is **closed**, and the normalization it was blocking is landed.

### Landed

* `Brauer/DivisionResidueBase.lean` — `divisionResidueBase D : DivisionResidue K K →+* DivisionResidue K D`
  and its injectivity.  This is the `𝓀_K`-algebra structure on `𝓀_L` that §0.32 said was missing.
* `Brauer/ResidueDegree.lean` — `linearIndependent_of_linearIndependent_divisionResidue` (rescale a
  relation so its coefficients are integers and one of them is a unit, then reduce) and hence
  `card_divisionResidue_le_pow_finrank : #𝓀_L ≤ #𝓀_K ^ [L:K]`, i.e. **`f ≤ n`** for an arbitrary
  finite extension.
* `Brauer/ResidueGalois.lean` — the other half.  `isCyclotomicExtension_of_unramified` and
  `isGalois_of_unramified` (an unramified extension is `K(ζ_N)`, hence cyclotomic, hence Galois);
  `residueAlgAut` (the action on `𝓀_L` **over `𝓀_K`**) and `card_algEquiv_le_finrank_divisionResidue`
  give `n ≤ f`.  Together: `card_divisionResidue_of_unramified` and
  `finrank_divisionResidue_of_unramified` — **`f = n`** — and then
  `exists_frobenius_of_unramified`: there is a `σ` with `zpowers σ = ⊤` raising every residue to
  the `q`-th power.
* `Brauer/Frobenius.lean` — `IsDivisionFrobenius σ` as a predicate, `eq_of_isDivisionFrobenius`
  (**uniqueness**, via `divisionResidueAut_injective`), the choice-based `divisionFrobenius K L hur`
  with `divisionFrobenius_zpowers`, `forall_mem_zpowers_divisionFrobenius` (exactly the shape
  `brauerInvariant`'s `hσ₀` wants) and `eq_divisionFrobenius`.
* `Brauer/FrobeniusTower.lean` — for `K ⊆ L ⊆ L'`: `divisionNorm_algebraMap_tower` (both sides are
  the spectral norm, which is `spectralValue ∘ minpoly K`, and `minpoly.algebraMap_eq` says the
  minimal polynomial does not change — Mathlib even has `spectralNorm.eq_of_tower` outright);
  `unramified_of_unramified_tower`; `divisionIntegersTower`, `divisionResidueTower` and its
  injectivity; and the payoff `restrictNormal_divisionFrobenius`:
  **`(Frob_{L'/K}).restrictNormal L = Frob_{L/K}`.**
* `Brauer/LocalInvariant.lean` — `localInvariant K L hur hm : Br(L/K) →* Multiplicative (ℚ/ℤ)`,
  the invariant taken with respect to `divisionFrobenius`, with
  `localInvariant_apply_cyclicBrauerHom`, `exists_localInvariant_eq` (**it attains `1/n`**) and
  `localInvariant_tower` (**independent of the level of the unramified tower**, assembled from
  `brauerInvariant_tower` + `restrictNormal_divisionFrobenius` + a `brauerInvariant_congr_apply`
  that transports the implicit generator).

### What target 1 of §0.31 still needs

`localInvariant` is a map on `Br(L/K)` for **one** unramified `L`.  To get `inv_K : Br(K) → ℚ/ℤ`
one needs well-definedness across splitting fields: if `x ∈ Br(L₁/K) ∩ Br(L₂/K)` with both `Lᵢ/K`
unramified, the two invariants agree.  `localInvariant_tower` settles this **as soon as `L₁` and
`L₂` both embed in a common unramified `L₃`**, because `Br(Lᵢ/K) ≤ Br(L₃/K)` by
`BrauerGroup.relative_le_relative`.  So the remaining brick is the *standard unramified tower*:

* the extension `K_n := K(ζ_{q^n−1})` inside a fixed algebraic closure, and `K_n ⊆ K_m` for `n ∣ m`;
* `K_n/K` is **unramified** — this is the direction the repo does *not* have.  It needs a Hensel
  lift of a root of unity from `𝓀_K` (equivalently `f ≥ n` for `K(ζ_m)`, `m` prime to `p`);
  `exists_adjoin_rootOfUnity_eq_top_of_unramified` is the converse and does not help.
* transport of `localInvariant` along a `K`-isomorphism of splitting fields (Frobenius goes to
  Frobenius, so this should be routine once stated).

### The route to `α`, re-examined — what does *not* work

`hα` (`Units/IdeleClassTate.lean:89`) is exactly "`Ĥ²(Gal(K/ℚ), C_K)` has an element of order `n`";
the `≤ n` half and `Ĥ¹ = 0` are already in the repo.  Four shortcuts were checked and all fail:

1. **Sylow restriction on the `p`-parts.**  Gives an element of order the `p`-part in
   `Ĥ²(Gal(K/K^{S_p}), ·)`, not in `Ĥ²(Gal(K/ℚ), ·)`.
2. **Corestriction from a cyclic subgroup `H ≤ G`.**  `cor ∘ res = [G:H]`, so the class produced
   has order `|H|`, not `n`.
3. **"An element of order `d` for every `d ∣ n` ⇒ cyclic of order `n`."**  False: `(ℤ/2)²` has an
   element of order `d` for every `d ∣ 2`.
4. **"Pick a place of full local degree."**  Circular: knowing the local factor injects into
   `Ĥ²(G, C)` is what reciprocity provides, and `n_v = n` forces `G_v = G`, hence `G` cyclic.
   A place of full local degree exists only when `G` is cyclic.

Two positive facts worth keeping:

* **An elementary special case.**  For `E ⊆ ℚ(ζ_q)` the cyclic degree-`n` subfield with `q ≡ 1
  (mod n)` prime, `E/ℚ` is ramified only at `q`, and totally (tamely) ramified there.  Using
  `I_ℚ = ℚ^× × (ℝ_{>0} × ∏_p ℤ_p^×)` (valid because ℚ has class number one and
  `ℚ^× ∩ (ℝ_{>0} × ∏ ℤ_p^×) = 1`), the map `θ : C_ℚ → (ℤ/q)^×`, `(r,(u_p)) ↦ ∏_{p ∣ q} [u_p]^{-1}`,
  kills `ℚ^×` *by construction*, restricts at an unramified `p` to `Frob_p^{v_p}`, and at `∞` to
  complex conjugation.  It kills local norms at `∞` and at unramified `p` (because `Frob_p^{f_w} =
  1`), and at `q` because in a totally ramified extension all conjugates of a unit are congruent
  mod the maximal ideal, so `N(u) ≡ ū^n`, while `N(π) = q`.  Hence `C_ℚ/N C_E ≅ ℤ/n` for these `E`
  with no reciprocity input at all.
* **An inflation–restriction bootstrap.**  For `ℚ ⊆ K ⊆ L` Galois, `H¹(Gal(L/K), C_L) = 0` makes
  `0 → H²(K/ℚ) → H²(L/ℚ) → H²(L/K)` exact, so
  `|H²(K/ℚ)| ≥ |H²(L/ℚ)| / |H²(L/K)| ≥ [L:ℚ]/[L:K] = [K:ℚ]`.
  Hence **it suffices to find, for each Galois `K/ℚ`, one Galois `L ⊇ K` with `H²(L/ℚ)` cyclic of
  order `[L:ℚ]`** — cyclicity of `H²(K/ℚ)` then comes for free, being a subgroup of a cyclic group.

What is *not* avoidable: `C_ℚ ⊄ N_{L/K} C_L` place by place (already at an unramified `v` with
`e(w/v) = 1`, `ℚ_v^× ⊆ N_{L_W/K_w}` fails), even though the global Artin map does kill `C_ℚ`.  So
the everywhere-local-norm test only works on a cleverly chosen representative, and the general case
genuinely needs the invariants `inv_v` together with `Σ_v inv_v = 0`.

---

## 0.34 Status (2026-08-29, late) — **target 1 of §0.31 is done: the invariant map `inv_K : Br(K) → ℚ/ℤ` exists**

Both bricks §0.33 listed as missing turned out to be cheaper than advertised, and one of its claims
was wrong.

### §0.33's "this is the direction the repo does *not* have" was wrong

§0.33 said unramifiedness of `K(ζ_m)` "needs a Hensel lift of a root of unity".  It does not.  The
`f ≤ n` bound of §0.33 is already an equality-forcing device: if the residue field is *as large as
the degree allows* then the extension is unramified, and the residue field of `K(ζ_m)` is large
enough for purely multiplicative reasons.  Landed as commit `b271a34`:

* `Brauer/ResidueDegree.lean` — `divisionNorm_eq_one_of_divisionResidue_ne_zero`,
  `exists_divisionNorm_sum_eq` and **`unramified_of_card_divisionResidue`**: an extension with
  `#𝓀_L = #𝓀_K ^ [L:K]` is unramified.  (A basis of `𝓀_L` over `𝓀_K` lifts to integers whose
  `𝓀_K`-combinations exhaust every value of the norm; each such combination has norm `‖c‖` for a
  scalar `c`.)
* `Brauer/ResidueGalois.lean` — **`unramified_of_rootOfUnity`** and
  **`unramified_of_isCyclotomicExtension`**: a Galois extension generated by a root of unity whose
  order is invertible in `𝓀_K` has residue degree `n`, hence is unramified.  No Hensel lift.
* `Brauer/UnramifiedCompositum.lean` (new) — `norm_natCast_lcm_eq_one` (`gcd · lcm = a · b` plus
  `‖ℕ‖ ≤ 1`) and **`unramified_sup`**: each `L_i` is `K(ζ_{q_i−1})` by the *converse* direction, the
  compositum is cyclotomic of order `lcm(q₁−1, q₂−1)` via Mathlib's
  `IntermediateField.isCyclotomicExtension_lcm_sup`, and that order is still invertible.  **The
  compositum of two unramified extensions is unramified.**

So the standard unramified tower `K(ζ_{qⁿ−1})` never has to be constructed at all: *directedness*
is all that well-definedness needs, and `unramified_sup` gives it for the unramified subfields of a
fixed algebraic closure, ordered by inclusion.

### Transport along an isomorphism is free

§0.33's third bullet ("transport of `localInvariant` along a `K`-isomorphism … routine once
stated") needs **no new machinery at all**: `localInvariant_tower` already covers *isomorphisms as
degenerate towers of height one*.  Given `e : L ≃ₐ[K] L'`, make `L'` an `L`-algebra via `e`; then
`IsScalarTower K L L'` holds by `e.commutes`, and `divisionNorm_algebraMap_tower` transports
unramifiedness (`unramified_of_algEquiv`) while `localInvariant_tower` transports the invariant.
This collapses what looked like a separate `brauerInvariant`-congruence project.

### Landed: `Brauer/InvariantMap.lean`

* `unramified_of_algEquiv` — an extension isomorphic to an unramified one is unramified.
* `UnramifiedSubfield K` — a finite unramified `IntermediateField K (AlgebraicClosure K)`, bundled
  with its finiteness and unramifiedness; `isGalois` instance; `sup` (via `unramified_sup`).
* `UnramifiedSubfield.invariant` = `localInvariant` at that level; `invariant_mono` (a bigger
  unramified subfield computes the same invariant — one line from `localInvariant_tower`, using
  definitional proof irrelevance for the two unramifiedness proofs) and hence **`invariant_eq`**:
  two unramified splitting fields give the same invariant, because both sit in their compositum.
* **`exists_unramifiedSubfield_mem_relative`** — every class is split by one of these.  Take the
  cyclic unramified splitting field of `exists_cyclic_unramified_mem_relative`, embed it by
  `IsAlgClosed.lift`, and move unramifiedness across `AlgEquiv.ofInjectiveField`.
* **`localInvariantMap K hm`** and **`localInvariantHom K hm : Br(K) →* Multiplicative (ℚ/ℤ)`**,
  with `localInvariantMap_eq` (it is computed by *any* unramified splitting field) and
  **`localInvariantHom_apply_of_unramified`**: it agrees with `localInvariant K L hur hm` for every
  unramified `L`, whether or not `L` sits in the chosen algebraic closure.

Two Lean notes worth keeping.  `BrauerGroup` has **two** universe parameters and
`BrauerGroup.relative` pins only the first, so a binder `(x : BrauerGroup K)` whose type does not
otherwise pin the second auto-binds a fresh universe and every later instance search runs on the
wrong type — write `BrauerGroup.{0, 0} K`.  And `exact map_mul f ⟨x, hx⟩ ⟨y, hy⟩` elaborated
*against the goal* diverges (deterministic timeout at whnf even at 10⁶ heartbeats) while the same
term with an explicit type ascription elaborates in milliseconds; state it as a `have` and finish
with `rw`.

### What target 1 still does not give

`localInvariantHom` is a homomorphism, but nothing yet says it is **injective on `Br(L/K)` with
image `(1/n)ℤ/ℤ`**.  That is the next step and both halves are in hand:
`card_relative_eq_finrank_of_spectralNorm` (`|Br(L/K)| = [L:K]`) plus `exists_localInvariant_eq`
(the invariant attains `1/n`) force the map `Br(L/K) → (1/n)ℤ/ℤ` to be a bijection between two sets
of size `n`.  Then `inv ∘ res = f · inv` from `finrank_divisionResidue_of_unramified` +
`localInvariant_tower`, then reciprocity `Σ_v inv_v = 0` over ℚ, then the assembly giving `hα`.

---

## 0.35 Status (2026-08-30) — **the fundamental class is reachable without reciprocity**: the cyclotomic-auxiliary route

The chain at the end of §0.34 ("… then reciprocity `Σ_v inv_v = 0` over ℚ, then the assembly giving
`hα`") is **no longer the plan**.  A survey of what the repository already owns turned up a route to
`hα` that never mentions the Brauer group, never mentions the Artin map, and needs neither
Kronecker–Weber, nor Chebotarev, nor local class field theory, nor the *ramified* local restriction
formula.  It costs one genuinely number-theoretic argument (step 6 below) and a stack of plumbing.

### The wall, restated

`InverseGalois/CFT/Units/IdeleClassTate.lean:89`:

```lean
theorem isTateClassTwo_ideleClassRep {α : tateModule (ideleClassRep k K) 2} (S : Subgroup Gal(K/k))
    (hα : ∀ m : ℤ, m • α = 0 → (Nat.card Gal(K/k) : ℤ) ∣ m) :
    IsTateClassTwo S (ideleClassRep k K) α
```

Everything else in Tate–Nakayama for the idele class group is landed: `Ĥ¹ = 0` for every subgroup
(`Units/IdeleClassH1Full.lean`), `|Ĥ²(S)| ≤ |S|` for every subgroup
(`Units/IdeleClassH2Full.lean`), and `isTateClassTwo_of_card_le` turns "`α` has order exactly `n`"
into the Tate class.  So the *only* missing input is an element of order `|Gal(K/ℚ)|` in
`H²(Gal(K/ℚ), C_K)` — the fundamental class.

### Why counting cannot do it

Recorded so nobody re-tries it.  `Ĥ¹(S) = 0` together with `|Ĥ²(S)| ≤ |S|` for *all* subgroups `S`
does **not** force an element of order `|G|`: for `G = (ℤ/2)²` the data `Ĥ²(G) = (ℤ/2)²`,
`Ĥ²(S) = ℤ/2` for each of the three subgroups of order two, satisfies every inequality and has
exponent `2 < 4`.  Two related tricks also fail:

* "`|ker(res : Ĥ²(K'/ℚ) → Ĥ²(K'/K))| ≥ n` for a big enough `K'`" needs a `K' ⊇ K` carrying a place
  of full local degree, which forces `Gal(K'/ℚ)` solvable — no good for general `K`.
* `K ⊆ K'` with `K'/ℚ` cyclic forces `K/ℚ` cyclic, so one cannot simply enlarge to a cyclic field.

Some genuine arithmetic input is required.  The route below is the cheapest one found.

### The route

Let `K/ℚ` be finite Galois, `n = [K : ℚ]`.

1. **Auxiliary prime `q`.**  Pick a prime `q ≡ 1 (mod 2n)` with `q ∤ disc K`.  Available:
   `Nat.exists_prime_gt_and_pow_dvd_sub_one` (`Cyclotomic/CyclicSubfield.lean`).
2. **Auxiliary cyclic field `L`.**  `L` = the degree-`n` subfield of `ℚ(ζ_q)`.  It is cyclic,
   totally ramified at `q`, unramified everywhere else, and **totally real** (`n ∣ (q−1)/2` forces
   `−1` into the index-`n` subgroup `H ≤ (ℤ/q)ˣ`, and `H` is exactly the `n`-th powers).  Available:
   `exists_cyclic_totallyRamified`, `exists_intermediateField_cyclic_totallyRamified`
   (`Cyclotomic/TotallyRamified.lean`), `Subgroup.exists_index_eq_of_isCyclic`,
   `IsCyclic.exists_intermediateField_finrank_eq` (`Cyclotomic/CyclicSubfield.lean`).
3. **Auxiliary prime `p`.**  Pick `p ∤ disc K`, `p ≠ q`, with `p mod q` a primitive root of
   `(ℤ/q)ˣ`; then `Frob_p` generates `Gal(L/ℚ) ≅ (ℤ/q)ˣ / H ≅ ℤ/n`, i.e. `p` is inert in `L`.
   Needs Dirichlet on primes in arithmetic progressions — Mathlib
   `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`.
4. **Linear disjointness is automatic.**  `K ∩ ℚ(ζ_q) = ℚ`, because `ℚ(ζ_q)/ℚ` is totally ramified
   at `q` while `K` is unramified at `q`.  Hence `Gal(KL/K) ≅ Gal(L/ℚ) = Δ`, cyclic of order `n`.
5. **The two quotients have order `n`.**  `Q_ℚ := I_ℚ / (ℚˣ ⊔ N_{L/ℚ} I_L)` and
   `Q_K := I_K / (Kˣ ⊔ N_{KL/K} I_{KL})` both have order exactly `n`, from
   `card_H2_ideleClassRep_of_generator` (`Units/IdeleClassH2.lean`) transported by
   `ideleQuotEquivTateH0` (`Units/IdeleClassIndex.lean:175`) and `tateH0AddEquivH2`
   (`GroupCohomology/CyclicTate.lean:229`).
6. **(α) The idele `j` has order exactly `n` in `Q_ℚ`.**  Here `j` is `p` at the place `p` and `1`
   everywhere else.  *Proof by relation-chasing.*  Suppose `j^d = r · N(y)` with `r ∈ ℚˣ`,
   `y ∈ I_L`.  Compare place by place:
   * at `ℓ ∉ {p, q}`: `f_ℓ ∣ v_ℓ(r)`, because `v_ℓ` of a local norm lies in `f_ℓ ℤ`;
   * at `p`: `d ≡ v_p(r) (mod f_p = n)`, because `p` is inert in `L`;
   * at `q`: `r = N(y_w)^{-1}`, and `N(L_w^×) ⊆ ⟨q⟩ · U_H` where `U_H` = the units whose residue
     lies in `H` (`L_w/ℚ_q` is totally ramified of degree `n`, so `N(u) ≡ ū^n mod q`).

   Reducing the `q`-unit part of `r` mod `q` gives
   `sign(r) · ∏_{ℓ ≠ q} (ℓ mod q)^{v_ℓ(r)} ∈ H`.  Since `−1 ∈ H` (totally real!) and
   `(ℓ mod q)^{f_ℓ} ∈ H`, all the terms with `ℓ ≠ p` die, leaving `Frob_p^{v_p(r)} = 1` in
   `(ℤ/q)ˣ/H`, i.e. `n ∣ v_p(r) ≡ d`.  ∎
7. **(β) `[u_q^p] = [j]^{-1}` in `Q_ℚ`**, where `u_q^p` is `p` at the place `q` and `1` elsewhere.
   Indeed `j · u_q^p · (diag p)^{-1}` is `p^{-1}` outside `{p, q}` and `1` at `p, q`; every such
   place is unramified in `L` (or is `∞`, where `L_u = ℝ` and the norm is the identity), and units
   are norms in unramified local extensions.
8. **The norm map `N_{K/ℚ} : Q_K → Q_ℚ` is an isomorphism.**  Well defined because
   `N_{K/ℚ} ∘ N_{KL/K} = N_{KL/ℚ} = N_{L/ℚ} ∘ N_{KL/L}`.  **Surjective** because at the place `q`
   the extension `K_w/ℚ_q` is unramified, so the norm is onto the units (`exists_normHom_kerUnitVal`,
   `Local/UnramifiedUnits.lean`), and hitting `u = p` produces `[j]^{-1}`, a generator by (α)+(β).
   Equal finite orders `n` then give injectivity.
9. **`[j_K] = 0` in `Q_K`.**  `N_{K/ℚ}([j_K]) = [j]^n = 0` by `ideleNorm ∘ ideleComap = (·)^{[K:ℚ]}`,
   and `N_{K/ℚ}` is injective by step 8.
10. **Translate to cohomology.**  The class `x ∈ H²(Δ, C_L)` matching `[j]` has order `n`;
    `res(inf x) ∈ H²(Gal(KL/K), C_{KL})` matches `[j_K] = 0`.
11. **Inflation–restriction in degree two** (legitimate here because `Ĥ¹` of the idele class group
    vanishes — already proven) produces a unique `α ∈ H²(Gal(K/ℚ), C_K)` with `inf α = inf x`, of
    order `n`.  That is exactly `hα`.

### What this retires

* **Artin reciprocity in general form is off the critical path.**  Cyclicity of `C_ℚ / N C_L` is
  *equivalent* to reciprocity, but the elementary cyclotomic construction above supplies the one
  instance of it that is needed, directly.
* **The ramified local restriction formula `inv_L ∘ res = [L:K] · inv_K` is not needed.**  Because
  the auxiliary prime `p` is chosen unramified in `K`, only the already-landed unramified case
  (`localInvariant_baseChange`, `Brauer/LocalInvariantRestrict.lean`) would ever be used — and in
  fact the route above does not use the Brauer group at all.  §0.31's "next targets, in order" is
  superseded from its reciprocity bullet onward.
* Kronecker–Weber, Chebotarev density and local class field theory are all unnecessary; the only
  analytic input is Dirichlet's theorem, which Mathlib has.

### Bricks to build, in order

1. Local: `N(u) ≡ ū^n (mod 𝔪)` for a totally ramified extension of degree `n`, and hence
   `N(L_w^×) ⊆ ⟨π⟩ · U_H` once a uniformizer with `N(π_L) = π` is known.  Globally
   `π_L = N_{ℚ(ζ_q)/L}(1 − ζ_q)` has `N_{L/ℚ}(π_L) = q`.
2. Local: `v(N_{L_w/k_v}(y)) = f · v_w(y)` in the unramified case — check whether
   `valued_algebraMap_norm` (`Local/UnramifiedNormValue.lean`) already covers it.
3. The reduction identity for `r ∈ ℚˣ`:
   `r · q^{−v_q(r)} mod q = sign(r) · ∏_{ℓ ≠ q} (ℓ mod q)^{v_ℓ(r)}` — reuse whatever generation of
   `ℚˣ` by `−1` and the primes `Global/Reciprocity.lean` / `RationalSquareClasses.lean` used.
4. `f_ℓ(L/ℚ)` = order of `ℓ mod q` in `(ℤ/q)ˣ / H`, from `orderOf_arithFrobAt`
   (`Cyclotomic/Frobenius.lean`) plus the subfield dictionary.
5. Statement (α): `j^d ∈ ℚˣ ⊔ N I_L → n ∣ d`.
6. Statement (β): `[u_q^p] = [j]^{-1}`.
7. Bijectivity of `N_{K/ℚ} : Q_K → Q_ℚ`, and `[j_K] = 0`.
8. Cohomological plumbing: naturality of `tateH0ToH2` along a compatible pair (group homomorphism
   plus equivariant coefficient map), and inflation–restriction exactness in degree two for the
   idele class representation.  Check `Units/InflationDescent.lean`,
   `Units/IdeleClassH2Tower.lean`, `Units/IdeleClassTower.lean` first.

### Inventory of the repository assets this route uses

`card_H2_ideleClassRep_of_generator`, `card_H2_ideleClassRep_cyclic` (`Units/IdeleClassH2.lean`);
`tateH0AddEquivH2`, `card_H2_eq_card_tateH0`, `tateH0ToH2`, `ker_tateH0ToH2`
(`GroupCohomology/CyclicTate.lean`); `ideleQuotEquivTateH0`, `toTateH0`, `first_inequality_index`,
`mem_ker_toTateH0_iff`, `toTateH0_surjective` (`Units/IdeleClassIndex.lean`);
`finite_and_card_H2_res_subgroup` (`Units/IdeleClassH2Full.lean`); `eq_zero_H1_res_subgroup`
(`Units/IdeleClassH1Full.lean`); `exists_normHom_kerUnitVal` (`Local/UnramifiedUnits.lean`);
`unramifiedInvariantUnits_surjective`, `valued_algebraMap_norm` (`Local/UnramifiedNormValue.lean`);
`exists_cyclic_totallyRamified` (`Cyclotomic/TotallyRamified.lean`); `orderOf_arithFrobAt`,
`galEquivZMod_arithFrobAt` (`Cyclotomic/Frobenius.lean`);
`Nat.exists_prime_gt_and_pow_dvd_sub_one`, `exists_prime_and_cyclic_intermediateField`
(`Cyclotomic/CyclicSubfield.lean`); `hilbert_reciprocity`, `exists_sub_sq_iff_forall_local`
(`Global/Reciprocity.lean`, `Global/HasseNorm.lean` — quadratic reciprocity and the quadratic Hasse
norm theorem over ℚ are already done, and are the `n = 2` shadow of exactly this argument).

### Landed since §0.31

`84303e3`, `7e65083`, `bb7e06e`, `f859ac7`, `4126374`, `7f47e58` (the last being the base change of
a cyclic algebra along a compositum: `Brauer/CyclicCompositum.lean` +
`Brauer/InvariantCompositum.lean`, giving `brauerInvariant_baseChange_compositum` — the invariant is
multiplied by the ratio of the two valuations).

---

## 0.36 Status (2026-08-30) — the class formation is **done**, §2 of Schmidt–Wingberg is **done**, and the two remaining walls are *global duality* and *Chebotarev*

Three things happened since §0.35.  A fourth, an attempt to remove Poitou–Tate from step 2, was
tried and **refuted**; the refutation is in (c) and is worth keeping, because the argument is
seductive.

### (a) The class formation over `ℚ` is unconditional; `GlobalTate.lean` has landed

`InverseGalois/CFT/Units/GlobalFundamental.lean` supplies the third class-formation condition
(`exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_global`) for **every** Galois extension of `ℚ`, and
`InverseGalois/CFT/Units/GlobalTate.lean` names the fundamental class and derives, with no
hypotheses at all,

* `globalFundamentalClass` and `isTateClassTwo_globalFundamentalClass`,
* `globalTateEquiv` — Tate's theorem, `Ĥⁿ(G, ℤ) ≅ Ĥⁿ⁺²(G, C_K)`,
* `globalReciprocityEquiv` — the case `n = -2`, i.e. reciprocity,
* `globalTateNakayamaEquiv` — Tate–Nakayama for coefficients flat over `ℤ`.

Note for the future: **only the construction of the auxiliary cyclic field is specific to the base
`ℚ`.** `Units/IdeleClassTate.lean` already states conditions (1) and (2) for an arbitrary number
field base `k`, and `exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep` (the core of
`Units/RatFundamentalClass.lean`) is already general in `k`; `Units/CompositumEmbed.lean` is
base-agnostic except for the literal `ℚ`.  A general base needs only:

* the compositum `k·F₀` of `k` with a cyclic totally real `F₀ ⊂ ℚ(ζ_q)` of degree `n`, with `q`
  chosen to split completely in the Galois closure of `K/ℚ` and `≡ 1 mod 2n`;
* that this compositum is cyclic of degree `n` over `k` (every nontrivial subfield of `ℚ(ζ_q)` is
  ramified at `q`, while `q` is unramified in `k`), totally ramified at the places above `q`,
  unramified elsewhere, and archimedean-trivial (because `F₀` is totally real).

That is a bounded, mechanical project, and it is what a Chebotarev-over-`K` statement would need.

### (b) §2 of Schmidt–Wingberg is complete in Lean

The group-theoretic half of the Schmidt–Wingberg proof (arXiv `math/9809211`, = NSW ch. IX §6) is
already formalized:

| SW | Lean |
| --- | --- |
| Prop 2 (Chevalley–Warning shrinking) | `Shafarevich/Shrink.lean`, `exists_ne_zero_forall_sum_prod_smul_eq_zero` |
| Def 3 (`p`-central series, `P^{(i,j)}`) | `Shafarevich/PCentral.lean` |
| Prop 5 (`θ_τ` surjective, `G`-invariant) | `Shafarevich/PCentralSpan.lean`, `Shafarevich/Layer.lean` |
| Prop 6 (shrinking in `Ĥ^k(G, E(m,τ) ⊗ T)`) | `Shafarevich/GenericCohomology.lean`, `exists_operatorHom_res_cohomology_eq_zero` |
| Prop 7 (Ishanov, the `k = -2` variant) | `Shafarevich/GenericHomology.lean`, `exists_operatorHom_h1_eq_zero` |

Hoechsmann's criterion ([3] Satz 1.1 in SW) is *also* already there, at finite level:
`GroupExtension.exists_lift_iff_cohomologyClass_pullback_eq_zero`
(`CFT/GroupCohomology/Pullback.lean`), together with the whole `H²`-classifies-extensions
dictionary (`Classification.lean`, `OfCocycle.lean`, `ToCocycle.lean`, `ExtensionMap.lean`).

### (c) §0.29(iii) stands: **Poitou–Tate *is* needed for step 2 of SW Theorem 15**

An earlier revision of this section claimed the Claim could be bypassed by running the
Chevalley–Warning count directly against `Ш²(k, E(n,τ))`.  That is **wrong**; §0.29(iii)
("the Claim really is Poitou–Tate; there is no cheaper reformulation hiding in it") was right.
The refutation is worth recording, because the tempting argument looks correct from a distance.

SW's step 2 needs to kill an obstruction class living in `Ш²(k, E(n,τ))`.  Their Claim produces a
commutative square with **surjective** horizontals

```
Ĥ^{-2}(G, E(m,τ)(-1))  ↠  Ш²(k, E(m,τ))
        ↓                        ↓
Ĥ^{-2}(G, E(n,τ)(-1))  ↠  Ш²(k, E(n,τ))
```

so that Prop 6 (applied to the *left* column, a Tate cohomology group of the **finite** group `G`)
can be used to shrink.  Getting the horizontals costs Tate–Poitou duality
`Ш²(k,E) ≅ Ш¹(k,E′)^∨`, the Hasse principle, and "the dual of cohomology is homology".

The tempting shortcut: `Ш²(k, −)` is an `𝔽_p`-linear subfunctor of `H²(G_k, −)` and
`θ_a : E(m,τ) → E(n,τ)` is homogeneous of degree `j` in `a`, so why not apply the count with
`Ш²(k, E(n,τ))` itself as the target?

**Why it fails.**  The homogeneity of `θ_a` in `a` is *not* a statement about the map `θ_a`; it is
a statement about its pullback along the fixed surjection `θ_τ(m) : (P_m/P_m²)^{⊗j} ↠ E(m,τ)` of
Prop 5:

```
φ_a^{⊗j} = Σ_{i₁…i_j} a_{i₁}···a_{i_j} · (proj_{i₁} ⊗ ⋯ ⊗ proj_{i_j}),
θ_a ∘ θ_τ(m) = θ_τ(n) ∘ φ_a^{⊗j}.
```

The individual monomial maps `proj_{i₁} ⊗ ⋯ ⊗ proj_{i_j}` do **not** descend to `E(m,τ)` — only
their `a`-weighted sum does — so there is no decomposition `θ_a = Σ_μ a^μ c_μ` with `c_μ` maps of
`G`-modules, and hence no way to make `Ш²(k, θ_a)` polynomial in `a` at the level of `Ш²`.
Polynomiality is only visible on *elements* of `E(m,τ)` lying in the image of pure tensors.  Every
correct application of the count therefore has the shape

> represent the class to be killed by **boundedly many elements of `E(m,τ)`**, kill those, conclude

— and "boundedly" means *independently of `m`*, since `m = r·n` is chosen only after the count
demands `r > d · t · dim W`.  This is exactly what the repo's counting core
`Shafarevich.exists_ne_zero_forall_apply_eq_zero` (`Shafarevich/LayerTensor.lean`) already
formalizes: it takes a spanning family `u` of the **source** with `Φ a (u ω) = (monomial) • u' ω`.

For `Ĥ^k(G, −)` with `G = Gal(K|k)` finite and fixed, a class is represented by a cochain with
`|G|^k` values: bounded, so the count applies (that is Prop 6, and it is how step 1 works).  For
`Ш²(k, −) ⊆ H²(G_k, −)`, a class is represented by a cocycle on `Gal(M|k)` for some finite `M`
containing the field cut out by the extension in question — and that field grows with `m`.  The
requirement is circular, and the shortcut collapses.

One might hope to escape by *inflating*: is `Ш²(k, E) ⊆ inf H²(Gal(K|k), E)`?  Local triviality
does restrict to `K`, and `Ш²(K, E) = 0` for a `G_K`-trivial `E` (see (d)), so
`Ш²(k,E) ⊆ ker(res : H²(G_k,E) → H²(G_K,E)) = F¹H²`.  But Hochschild–Serre only gives
`F¹/F² ↪ H¹(G, H¹(G_K, E))` with `F² = inf H²(G, E)`, and `H¹(G_K, E) = Hom(G_K, E)` is enormous.
Cutting `F¹` down to `F²` is precisely the content of the duality theorem; there is no free lunch.

### (d) What of (c) survives, and where the duality actually enters

Three of the four ingredients of the Claim are duality-free and (almost) already in the repo:

* **Hasse principle ⇒ `Ш¹(k, E′) ↪ H¹(Gal(K|k), E′)`.**  A class of `Ш¹(k, E′)` restricts into
  `Ш¹(K, E′)`, which is `0` because a solvable extension in which every place splits completely is
  trivial — `CFT/Units/SplitNorm.lean`, `subsingleton_gal_of_isSolvable_of_free`.  In degree one
  inflation–restriction is exact on the left, so `Ш¹(k, E′) ⊆ inf H¹(G, E′)`.  (Note the contrast
  with degree two above: this is *why* SW dualize into degree one.)
* **Dualizing.**  `H¹(G, E′)^∨ ↠ Ш¹(k, E′)^∨`, and `H¹(G, E′)^∨ ≅ Ĥ^{-2}(G, E′^∨)` — the repo has
  `h1DualEquiv` (`CFT/GroupCohomology/Duality.lean`) and `h1TwistEquiv`,
  `exists_h1Twist_surjective` (`CFT/GroupCohomology/TateTwist.lean`).
* **Prop 6 / Prop 7** on the resulting finite-group Tate cohomology: done
  (`Shafarevich/GenericCohomology.lean`, `Shafarevich/GenericHomology.lean`).

The **single** genuinely missing input is the global duality isomorphism

```
Ш²(k, A) ≅ Ш¹(k, A′)^∨,   A′ = Hom(A, μ_∞)
```

i.e. Poitou–Tate.  That, not a generalized Chevalley–Warning, is the wall in step 2.

The finiteness observation from the discarded argument is still true and still useful in its own
right: for a `G_K`-trivial `E ≅ (ℤ/p)^d` with `μ_p ⊆ K`, `Ш²(K, ℤ/p) ≅ Ш²(K, μ_p) ≅ Ш(Br K)[p] = 0`
by Albert–Brauer–Hasse–Noether (needs `μ_p ⊆ K`, Hilbert 90, `H¹(G, C_K) = 0` — all present in the
repo).  This is what makes `Ш²(k, E)` finite, and it will be needed anyway.

And the two caveats established by re-reading the paper line by line remain:

* **Step 4 needs duality too.**  SW Theorem 13 (the existence of algebraic numbers with
  prescribed local behaviour) uses Chebotarev's density theorem, local Tate duality
  (Serre, *Galois Cohomology* II §5.2, §5.5), the exactness of the lower line of the long
  Tate–Poitou sequence, a pigeonhole argument, and the Hilbert-symbol product formula
  `∏_{P ∈ S(K)} (a, b)_P = 1`.  The `p = 2` case additionally runs the combinatorial three-element
  construction of Serre's *Topics* ch. 5 §3.
* **Lemma 10** (`0 → Ш¹(k_S, A′) → Ш¹(k_S, S∖T, A′) → coker(k_S, T, A)^∨ → 0`) also quotes the
  local and global duality theorems.

### (e) Chebotarev is the gateway, and Mathlib's analytic floor is further along than expected

Every route to Shafarevich in the literature (Shafarevich 1954; NSW ch. IX §6 = Schmidt–Wingberg;
Ishkhanov–Lur'e–Faddeev) passes through Chebotarev's density theorem over a general number field —
it is not an artefact of one write-up.  The two uses in SW Theorem 13 are, precisely:

* odd `p`: "choose a prime `P_{n+1} ∈ S ∖ T_n(K)` such that the image of `ξ` in
  `H¹(k_{T_n}|K, ℤ/p)^∨` equals `Frob_{P_n}`" — ray-class Chebotarev for the maximal abelian
  exponent-`p` extension of `K` unramified outside `T_n`;
* `p = 2`: "there is a prime `Q ∉ T(K)` of `O_{K,S_∞}` with `Q^σ ≠ Q` and `Q = A·(x)`" — every
  `S`-ideal class of `K` contains infinitely many primes.

Both are *abelian* Chebotarev, i.e. **Dirichlet's theorem for ray classes of a number field**.
Over `ℚ` this is Dirichlet + Kronecker–Weber, which the repo already has; over `K` it is not.

Mathlib v4.28 turns out to supply a surprising amount of the analytic floor:

* `Mathlib/NumberTheory/NumberField/DedekindZeta.lean` — `NumberField.dedekindZeta`,
  `dedekindZeta_residue`, and `tendsto_sub_one_mul_dedekindZeta_nhdsGT`, i.e. **Dirichlet's
  analytic class number formula**;
* `Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean` —
  `NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop`: **the count of ideals of bounded norm in
  a fixed class of the class group**;
* `Mathlib/NumberTheory/LSeries/` — `Dirichlet.lean`, `Nonvanishing.lean`, `PrimesInAP.lean`,
  `SumCoeff.lean`, `Positivity.lean`, `Convergence.lean`.

What is missing: ray-class groups with their `L`-functions, an *error term* in the ideal count
(`tendsto_norm_le_and_mk_eq_div_atTop` is a bare limit, and analytic continuation of `L(s,χ)` past
`Re s = 1` needs `A(x) = O(x^{1-1/d})`), Landau's theorem for Dirichlet series with non-negative
coefficients, non-vanishing at `s = 1`, and a density notion.  Also absent: any Chebotarev
statement, `groupCohomology` inflation as a named map, and an `H²`-classification of group
extensions (`Mathlib/GroupTheory/GroupExtension/` has only a docstring TODO).

### The remaining arithmetic, with costs

| # | Missing piece | Notes |
| --- | --- | --- |
| 1 | ~~`H^i(G_k, A)` for finite discrete `A`, as a filtered colimit `colim_M H^i(Gal(M/k), A)` over finite Galois `M ⊇ K`, with localization maps and `Ш^i`~~ | **DONE** — `InverseGalois/CFT/Profinite/`: `SmoothH1`/`SmoothH2` with `galInflH1`/`galInflH2`, `resH1`/`resH2`, and `sha1`/`sha2` (see §0.37) |
| 2 | ~~`Ш¹(k, A) ↪ H¹(Gal(K\|k), A)` from the Hasse principle, and its dual~~ | **DONE** — `CFT/Units/HasseInflation.lean`: `exists_galInflH1_eq_of_forall_level` and `exists_galInflH1_eq_of_forall_level_outside`, and — with the glue of §0.40 — `CFT/Units/HasseDecomposition.lean`: `exists_galInflH1_eq_of_finiteDecomposition(Outside)`, stated at the genuine decomposition subgroups of `G_k` |
| 3 | ~~Finiteness of `Ш²(k, E)` via ABHN + Hochschild–Serre~~ | **DONE** — `CFT/Units/HasseTwo.lean`: `eq_one_of_forall_isLocallySplitLevel`, the vanishing of the everywhere locally trivial classes of `H²` with `μ_n` coefficients, valid at `p = 2` (see §0.38).  The degree-one glue is §0.40; the degree-two glue is §0.42 — `CFT/Units/HasseTwoDecomposition.lean`: `eq_one_of_mem_sha2`, stated at `sha2 M (decompositionSubgroups k Ω)`, the genuine decomposition subgroups of `G_k` |
| 4 | ~~Local Tate duality for finite modules over a local field~~ | **DONE** — `CFT/Local/CyclicNormIndex.lean` (the norm index of *any* cyclic extension of a local field is its degree), `CFT/Local/KummerNonNorm.lean` (nondegeneracy of the `q`-th power norm residue symbol), see §0.39; `inv_M ∘ res = [M:K] · inv_K` is `localInvariantHom_baseChange` (`CFT/Brauer/InvariantBaseChange.lean`); and `CFT/Brauer/CyclicNormResidue.lean` assembles the norm residue symbol of a cyclic extension of a local field, see §0.56 |
| 5 | **Global duality `Ш²(k, A) ≅ Ш¹(k, A′)^∨`** | wall #1: the sole missing input of SW's Claim, hence of step 2 |
| 6 | The `p`-th power Hilbert symbol over a number field and its product formula | the repo has the *quadratic* symbol over `ℚ` (`CFT/Global/Hilbert*.lean`); the *local* nondegeneracy of the `p`-th power symbol is §0.39(b) |
| 7 | ~~**Chebotarev density over a number field**, in the abelian/ray-class form of (e)~~ | **DONE for odd `p`** — `NumberTheory/RelativeSplitDensity.lean` + `CFT/RelativeFrobenius.lean`: Theorem 13 only needs the Frobenius *up to a scalar*, which is `exists_relStabilizer_eq_zpowers` (see §0.41).  What remains is "every ideal class contains a prime", used only in the `p = 2` Claim |
| 8 | Poitou–Tate, at least the eight-term sequence for `μ_p` over `k_S` | needed by Lemma 10 and Theorem 13 |
| 9 | SW Theorem 13, then Theorems 14 and 15 | assembly |

Already-existing bricks that will be consumed and should not be rebuilt:

* `CFT/GroupCohomology/Duality.lean` — `h1DualEquiv` (`H₁` of the contragredient `≅` dual of `H¹`);
* `CFT/GroupCohomology/TateTwist.lean` — `h1TwistEquiv`, `exists_h1Twist_surjective` (the finite-
  group half of SW's Claim, already formalized);
* `CFT/Units/ABHN.lean` — `exists_sub_add_eq_globalUnits`;
* `CFT/Units/SplitNorm.lean` — `subsingleton_gal_of_isSolvable_of_free`, the Hasse-principle brick;
* `CFT/GrunwaldWang.lean` — Grunwald–Wang in power-class form (SW Prop 11 wants the character
  form).

---

## 0.37 Status (2026-08-30) — rows 1 and 2 were already built; `Br(K) ≅ ℚ/ℤ` is now a theorem

### (a) Two rows of the §0.36 table were stale

A survey of the tree found that the "next brick" named in §0.36 had in fact already been laid,
twice over.

**Row 1** is `InverseGalois/CFT/Profinite/`.  It carries the smooth (= continuous, finite-level)
cohomology of the absolute Galois group in degrees one and two — `SmoothH1`, `SmoothH2`,
`smoothH1Mk`, `smoothH2Mk` — with the inflation maps `galInflH1`, `galInflH2` from a finite level,
the localization maps `resH1`, `resH2` to a subgroup, and the Tate–Shafarevich subgroups
`sha1 (S : Set (Subgroup G))`, `sha2` cut out by them (`Profinite/Res.lean`), plus the trivial-
action dictionary in `Profinite/Trivial.lean` (`cocycleHom`, `smoothH1Mk_eq_one_iff_of_trivial`,
`resH1_eq_one_iff_of_trivial`, `smoothH1Mk_mem_sha1_iff_le_ker`).

**Row 2** is `InverseGalois/CFT/Units/HasseInflation.lean`.  It proves exactly the required
statement — a smooth one-cocycle that dies on every decomposition subgroup at every finite level is
inflated from that level:

```lean
theorem exists_galInflH1_eq_of_forall_level (hs : IsSmooth₁ u) (hloc : …) :
    ∃ z : SmoothH1 (↥F ≃ₐ[k] ↥F) M, galInflH1 F hπ z = smoothH1Mk u hu hs
```

together with the variant `exists_galInflH1_eq_of_forall_level_outside` that ignores a finite set of
places.

**What is genuinely still open in row 2** is only the glue: `sha1` is stated for an abstract family
`S : Set (Subgroup G_k)`, while `HasseInflation` quantifies over `levelDecompositionSet L`.  Making
the two match needs *genuine* decomposition subgroups of `G_k` — i.e. a place of `k̄` over a place
of `k` and its stabilizer — which is a design task in its own right and has been deferred.

### (b) The Brauer group of a local field is `ℚ/ℤ`

`InverseGalois/CFT/Brauer/InvariantSurjective.lean` closes the other half of the local invariant
map.  Injectivity was already in `InvariantInjective.lean`; surjectivity needs unramified
extensions of arbitrary degree, which the file builds by hand:

* `dvd_of_pow_sub_one_dvd_pow_sub_one : 2 ≤ q → q ^ a - 1 ∣ q ^ b - 1 → a ∣ b`.  Elementary, but not
  in Mathlib — only the converse `Nat.pow_sub_one_dvd_pow_sub_one` is.  The proof writes
  `b = a·(b/a) + b%a`, moves to `ℤ` (where `x^b - 1 = x^{b%a}(x^{a(b/a)} - 1) + (x^{b%a} - 1)` is a
  ring identity), and squeezes the remainder term between `0` and `q^a - 1`.
* `dvd_card_divisionResidue_sub_one_of_isPrimitiveRoot` — a root of unity whose order is invertible
  in `K` keeps that order in the residue field.  Its residue is a nonzero element of a finite field,
  so `ζ^{N-1}` is congruent to `1`; and a root of unity of invertible order congruent to `1` **is**
  `1` (`eq_one_of_pow_eq_one_of_divisionNorm_sub_lt_one`, from `DivisionCyclic.lean`).  Hence
  `M ∣ N - 1`.
* `exists_unramified_dvd_finrank` — given `n`, put `Q = #(residue field)` and `M = Q^n - 1`.  Then
  `‖M‖ = 1` (`norm_natCast_pow_card_divisionResidue_sub_one`), so `L = CyclotomicField M K` is
  unramified (`unramified_of_isCyclotomicExtension`) and its residue field has `Q^{[L:K]}` elements
  (`card_divisionResidue_of_unramified`).  The primitive `M`-th root forces `M ∣ Q^{[L:K]} - 1`,
  i.e. `Q^n - 1 ∣ Q^{[L:K]} - 1`, i.e. `n ∣ [L:K]`.
* `localInvariantHom_surjective` — for a target `r + ℤ`, take `n = r.den`, get `L` with
  `[L:K] = r.den · t`, take the class `w` with invariant `1/[L:K]` (`exists_localInvariant_eq`) and
  raise it to the power `r.num · t`.
* `localInvariantEquiv : BrauerGroup K ≃* Multiplicative (ℚ/ℤ)` — the two halves combined.

This is the group-theoretic cornerstone of local class field theory and the prerequisite for row 4
(local Tate duality) and row 6 (the `p`-th power Hilbert symbol).

---

## 0.38 Status (2026-08-30, later) — row 3 is laid: `Ш²(k, μ_n) = 0`, and the prime `2` is covered

### (a) The relative Brauer group of a local field is bounded by the degree

`InverseGalois/CFT/Brauer/RelativeTorsion.lean` isolates the `n`-torsion of `ℚ/ℤ` as a subgroup,
transports it through `localInvariantEquiv`, and reads off the consequences for the relative Brauer
group of a finite extension `L/K` of local fields:

* `nsmulTorsionQModZ`, `zmodEquivNsmulTorsionQModZ`, `natCard_nsmulTorsionQModZ` — the `n`-torsion of
  `ℚ/ℤ` is cyclic of order `n`;
* `brauerTorsion`, `brauerTorsionEquiv`, `natCard_brauerTorsion` — hence the `n`-torsion of `Br K`
  is cyclic of order `n`;
* `relative_le_brauerTorsion`, `finite_relative_local`,
  `card_relative_le_finrank_local : Nat.card ↥(relativeBrauerGroup K L) ≤ finrank K L` — a class
  split by `L` is killed by `[L:K]`;
* `relative_eq_brauerTorsion_of_unramified` — for unramified `L/K` the bound is an equality.

The reverse bound `#Br(L/K) ≥ [L:K]` for an arbitrary `L` still wants the base-change formula
`inv_L ∘ res = [L:K] · inv_K`, which is what would turn this into the local reciprocity isomorphism.

### (b) The local-global principle for central embedding problems, now at `p = 2` as well

The multiplicative wrappers of Albert–Brauer–Hasse–Noether that were in the tree all bought their
silence at the archimedean places by restricting the integer killing the cocycle — odd order, or
order coprime to the local degrees at infinity.  Two new files remove the restriction and pay for
the infinite places instead:

* `InverseGalois/CFT/Units/ABHNPlaces.lean` — `smulUnitsAut_infiniteUnitHom_algebraMap` (the
  decomposition group at an archimedean place fixes the local units coming from the base field) and
  `exists_isMulCoboundary_of_forall_place`: **a two-cocycle with values in `kˣ` which splits at
  every place of `K`, archimedean places included, is the coboundary of a one-cochain with values
  in `Kˣ`** — no hypothesis whatever on the cocycle.
* `InverseGalois/CFT/Kummer/CentralEmbeddingPlaces.lean` —
  `exists_surjective_hom_of_forall_place`, the archimedean twin
  `exists_local_coboundary_of_exists_lift_infinitePlace` of
  `exists_local_coboundary_of_exists_lift`, and
  `exists_surjective_hom_of_forall_place_lift`: **a central Frattini embedding problem that is
  solvable over the decomposition group at every place is solvable over a larger extension**, with
  no restriction on the order of the kernel.

This is the form of the criterion that survives at `p = 2`, where the real places genuinely
obstruct.

### (c) Row 3: the everywhere locally trivial classes of `H²` with `μ_n` coefficients vanish

`InverseGalois/CFT/Units/HasseTwo.lean` is the degree-two analogue of `Units/HasseLevel.lean` and
`Units/HasseInflation.lean`, and it is what §0.36(d) asked for:

* `exists_level_cochain₂` — a two-cochain constant on the cosets of the kernel is a two-cochain of
  the quotient (the curried companion of `exists_comap₂_eq`, with no action on the quotient
  required);
* `restrictNormalHom_eq_of_res` — restriction to a level factors through restriction to a larger
  level, which is what transfers a cochain produced at the radical level back down;
* `IsLocallySplitLevel ι L a` — the local hypothesis: the `kˣ`-transported level cocycle is a
  coboundary in the completion at every place of `L`, archimedean places included;
* `exists_isSmooth₁_coboundary₂_eq_of_isLocallySplitLevel` — the inflation of a locally split level
  cocycle to `G_k` is the coboundary of a **smooth** one-cochain;
* `smoothH2Mk_eq_one_of_isLocallySplitLevel`, and
* `eq_one_of_forall_isLocallySplitLevel` — **a class of `SmoothH2 G_k M` every level representative
  of which splits at every place of its level is trivial**, for coefficients `M` acted on trivially
  and embedded in `kˣ` as the `n`-th roots of unity.

The chain is: `exists_isGalois_smooth₂` (every class lives at a finite Galois level) →
`exists_level_cochain₂` (descend the representative to that level) →
`exists_isMulCoboundary_of_forall_place` (ABHN, §0.38(b), so `p = 2` is fine) →
`exists_intermediateField_cochain_of_isMulCoboundary` (Kummer, `Kummer/CocycleDescent.lean`:
rescale over a radical extension so the trivialising cochain is `μ_n`-valued) →
`restrictNormalHom_eq_of_res` + `isSmoothHom_restrictNormalHom` (read it as a smooth cochain on
`G_k`).  Notably the profinite Kummer sequence is **not** needed: the finite-level Hilbert 90
argument already in `Kummer/InflationRootsOfUnity.lean` does the whole job.

**What was still open in row 3** (closed in §0.42) is the same glue as in row 2:
`IsLocallySplitLevel` quantifies over the places of a *level*, while genuine membership in `sha2`
is a statement about the decomposition subgroups of `G_k` itself.  Matching the two needs a place of `k̄` over a place of `k` and its
stabilizer — the design task deferred in §0.37(a).  With that glue, the finiteness of `Ш²(k, E)`
for a `G_K`-trivial `E ≅ (ℤ/p)^d` is `Ш²(K, μ_p)^d = 0` plus Hochschild–Serre.

### (d) The table, updated

Rows 1, 2 and 3 are laid (each modulo the one shared glue lemma, itself closed in §0.40 for
degree one and in §0.42 for degree two).  The next brick is **row 4**,
local Tate duality with `μ_p` coefficients, for which `localInvariantEquiv` (§0.37(b)) and the
torsion computation of §0.38(a) are the inputs.  Rows 5 and 7 — Poitou–Tate and Chebotarev over a
number field — remain the two walls.  (Row 4 was laid the same day; see §0.39.)

---

## 0.39 Status (2026-08-30, later still) — the local norm index for **every** cyclic extension, and the nondegeneracy of the norm residue symbol

### (a) The unramifiedness hypothesis was never needed

`InverseGalois/CFT/Local/CompleteNormIndex.lean` has carried, for some time, the sharp local first
inequality

```
(normSubgroup K L).index = finrank K L
```

for an arbitrary cyclic `L/K` — ramified or not — *provided* the larger field `L` is itself
presented as complete and discretely valued with the automorphisms acting by isometries.  What was
missing was the package supplying that presentation.  The only one in the tree,
`exists_valued_of_spectralNorm` (`CFT/Local/NormValued.lean`), carries a hypothesis

```
hval : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖
```

which says `L/K` is unramified.  Reading its proof line by line shows that `hval` is used for
**one** conclusion only, `IsUnramifiedValued K L`; every other component — the valuation
`normValued K L`, completeness, rank one, proper-ness, the residue characteristic, finiteness of
the graded pieces, invariance under `Gal(L/K)`, a unit of nontrivial value, a generator of the
value group — is proved from the field norm alone and does not care about ramification.

`InverseGalois/CFT/Local/CyclicNormIndex.lean` therefore just drops it:

* `exists_valued_of_finite` — **a finite extension of a complete, discretely valued, locally
  compact field carries all the structure of a local field**, with no hypothesis on the extension;
* `index_normSubgroup_eq_finrank_local` — **the norm index of any cyclic extension of a local field
  is its degree**;
* `exists_notMem_normSubgroup` — hence a cyclic extension of degree bigger than one always has a
  unit of the base field which is not a norm.

This is the first inequality of local class field theory in full.  It is one of the two halves of
the local reciprocity isomorphism `Kˣ / N Lˣ ≅ Gal(L/K)^{ab}`; what the second half still wants is
the base-change formula `inv_L ∘ res = [L:K] · inv_K` of §0.38(a).

### (b) The norm residue symbol is nondegenerate

`InverseGalois/CFT/Local/KummerNonNorm.lean` is the immediate arithmetic consequence, and it is the
shape in which the theory of embedding problems actually consumes local duality.  Let `K` be a
local field containing a primitive `q`-th root of unity, `q` prime, and let `a ∈ K` not be a `q`-th
power.  Then `X^q - a` is irreducible (`X_pow_sub_C_irreducible_of_prime`, valid at `q = 2` too),
its splitting field is cyclic of degree `q` over `K` (Mathlib's Kummer API), and (a) gives a unit of
`K` which is not a norm from it:

* `exists_notMem_normSubgroup_of_isSplittingField` — for any field presented as a splitting field of
  `X^q - a`;
* `exists_cyclic_notMem_normSubgroup` — packaged with the construction of the extension by
  `AdjoinRoot`, together with the root itself and the degree.

Written with the norm residue symbol `(a, c)` — the class of the cyclic algebra of `K(q√a)` with
coefficient `c`, equivalently the amount by which the Artin symbol of `c` moves `q√a` — this says
that the symbol is nondegenerate in its second argument: for every `a` which is not a `q`-th power
there is a `c` with `(a, c) ≠ 1`.  That is the duality between `H¹(K, μ_q)` and `H¹(K, ℤ/q)` in the
only shape rows 6 and 9 use it.

### (c) What row 4 still owes

The full statement of local Tate duality — a perfect pairing
`H^i(K, A) × H^{2-i}(K, A′) → H²(K, 𝔾_m) = ℚ/ℤ` for every finite module `A` — is not what SW
Theorem 13 consumes; it consumes the `i = 1`, `A = ℤ/p` case, which is (b), plus the *global*
product formula for the same symbol (row 6).  So the honest reading of the table is that row 4 is
laid in its usable form, and the remaining work has moved into rows 6 and 5.

The one piece of row 4 which is genuinely still missing and genuinely still wanted elsewhere is the
invariant-map functoriality `inv_M ∘ res = [M:K] · inv_K` for an arbitrary finite `M/K`.  The tree
has `localInvariant_baseChange` (`Brauer/LocalInvariantRestrict.lean`) only for `K ⊆ M ⊆ L` with
`L/K` unramified, and `brauerInvariant_baseChange_compositum`
(`Brauer/InvariantCompositum.lean`) only when `Gal(N/M) ≅ Gal(E/K)`, which fails as soon as
`E ∩ M ≠ K`.  The classical repair is to factor `M/K` through its maximal unramified subextension
`M₀` (degree `f`) and the totally ramified `M/M₀` (degree `e`), using
`exists_unramified_le_finrank_eq`, `eq_of_finrank_eq_of_unramified` and
`ramification_mul_finrank_divisionResidue`, all of which are already in the tree.  That is a
self-contained chunk and it is what would upgrade `card_relative_le_finrank_local` of §0.38(a) to
an equality, i.e. to local reciprocity.

---

## 0.40 Status (2026-08-30, later still) — the glue is closed: genuine decomposition subgroups of `G_k`

The "one shared glue lemma" that §0.36 rows 2 and 3 and §0.37(a) both deferred is now a theorem.

### (a) The obstruction, restated

`sha1`/`sha2` (`CFT/Profinite/Res.lean`) are stated for an abstract family `S : Set (Subgroup G)`,
while `HasseLevel`/`HasseInflation` quantify over `levelDecompositionSet L` — the automorphisms
whose *restriction to a finite level* fixes a place *of that level*.  A local-global principle
produces the first shape, not the second.  Matching them needs genuine decomposition subgroups of
`G_k` itself, i.e. primes of the ring of integers of the (infinite) top field and transitivity of
the Galois action on them.

### (b) `CFT/Units/InfiniteDecomposition.lean`

`NumberField.RingOfIntegers K = integralClosure ℤ K` is defined for *any* field, with no
`NumberField` hypothesis, and Mathlib already supplies the whole `𝓞`-functoriality package for
infinite extensions (`inst_ringOfIntegersAlgebra`, `inst_isScalarTower`,
`extension_algebra_isIntegral`, `ker_algebraMap_eq_bot`, and the `MulSemiringAction G (𝓞 K)`
instance).  So the primes are there; what has to be proven is transitivity.

* `under_smul_ringOfIntegers` — the prime of a subfield below a moved prime is the moved prime
  below, for raw ideals and with no finiteness anywhere (the `HeightOneSpectrum` version in
  `Units/PlaceRestrict.lean` needs `NumberField K`).
* `isInvariant_ringOfIntegers_of_isGalois` — `Algebra.IsInvariant (𝓞 F) (𝓞 K) Gal(K/F)` for an
  *arbitrary* Galois `K/F`, via `InfiniteGalois.mem_range_algebraMap_iff_fixed` (Mathlib's
  `Algebra.isInvariant_of_isGalois` wants `FiniteDimensional`).
* `smulCommClass_ringOfIntegers`, `continuousSMul_ringOfIntegers` — the two side conditions; the
  second is `continuousSMul_iff_stabilizer_isOpen` plus `stabilizer_isOpen_of_isIntegral`, i.e. the
  Krull topology.
* `exists_smul_eq_of_under_eq_ringOfIntegers` — **the Galois group of an arbitrary Galois extension
  acts transitively on the primes of its integers above a prime of the base.**  This is Mathlib's
  `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` (`RingTheory/Invariant/Profinite.lean`),
  which does the whole compactness / inverse-limit argument; the work here was assembling its five
  hypotheses for `𝓞 K` with the discrete topology.
* `exists_stabilizer_prime_restrictNormalHom_eq` — **an automorphism of a level fixing a place
  there is the restriction of an automorphism fixing a prime above**: lift by
  `restrictNormalHom_surjective_level`, then correct by an element of `Gal(K/L)` using
  transitivity.  This is the actual glue.
* `finiteDecompositionSubgroups k K` and `finiteDecompositionSubgroupsOutside k K S` — the
  stabilisers of the nonzero primes of `𝓞 K` (with the place below avoiding `S`).  `P ≠ ⊥` is part
  of the definition on purpose: `stabilizer ⊥ = ⊤`, so admitting `⊥` would wrongly strengthen the
  `sha1` hypothesis.
* `eq_one_of_finiteDecomposition`, `eq_one_of_finiteDecompositionOutside` — **a homomorphism into a
  commutative group killing a level and every decomposition subgroup is trivial.**
* `eq_one_of_mem_sha1`, `eq_one_of_mem_sha1_outside` — **`Ш¹(G_k, M) = 0` for trivial coefficients,
  with `Ш¹` taken over the genuine decomposition subgroups**, the class being reduced to a level by
  `exists_isGalois_smooth₁` and the cocycle to a homomorphism by `Profinite/Trivial.lean`.

### (c) `CFT/Units/HasseDecomposition.lean`

The bridge to the consumer.  `HasseInflation`'s `exists_galInflH1_eq_of_forall_level_outside` works
relative to the base `↥F` (the finite Galois level trivialising the coefficients), with
`L : IntermediateField ↥F K`; and `ρ • P = P` for `ρ : K ≃ₐ[↥F] K` says exactly that
`ρ ∈ stabilizer Gal(K/↥F) P`.  So the decomposition-subgroup hypothesis is fed straight in:

* `eq_one_of_finiteDecompositionOutside_over`, and
* `exists_galInflH1_eq_of_finiteDecomposition` /
  `exists_galInflH1_eq_of_finiteDecompositionOutside` — **a class dying on the stabiliser of every
  nonzero prime of `𝓞 K` is inflated from the field trivialising its coefficients**, with no level
  left in the hypothesis.

### (d) The table, updated again

Rows 1, 2, 3 are now laid **without** the glue caveat, and row 4 is laid in the shape consumed.
The remaining bricks are unchanged: row 4's leftover `inv_M ∘ res = [M:K]·inv_K`, row 6 (the `p`-th
power Hilbert symbol over a number field and its product formula), row 8, row 9 — and the two
walls, row 5 (**Poitou–Tate global duality**, `Ш²(k,A) ≅ Ш¹(k,A′)^∨`) and row 7 (**Chebotarev
density over a number field**).

Phase 1 is the finite places only; `levelDecompositionSetOutside` never mentions the archimedean
ones, so nothing was lost *in degree one*.

> **Correction (see §0.42).**  The last sentence of this subsection originally read that
> archimedean decomposition subgroups of `G_k` "are not needed by anything downstream".  That is
> false in degree two: `IsLocallySplitLevel` is a *conjunction* of an archimedean clause and a
> finite clause, so the degree-two glue needs the archimedean half as well.  It is built in §0.42.

---

## 0.41 Status (2026-08-30, night) — **wall #2 falls for odd `p`**: Theorem 13 only needs Frobenius *up to a scalar*

### (a) The analytic floor over a general base

Two modules carry the density argument of `NumberTheory/SplitDensity.lean` from the base `ℚ` to an
arbitrary number field `k`.

* `InverseGalois/NumberTheory/RelativeSplitDensity.lean` — `idealSum`, `HasIdealDensity`, the
  fibre decomposition of `log ζ_L(s)` over the primes of the base, and the three headline
  statements `hasIdealDensity_relSplitSet` (the primes of `k` splitting completely in a Galois
  `L|k` of degree `n` have Dirichlet density `1/n`), `infinite_relSplitSet`, and
  `infinite_setOf_splitsCompletelyIn_not_splitsCompletelyIn`.
* `InverseGalois/CFT/RelativeFrobenius.lean` — the decomposition dictionary at the base `k`:
  `card_relStabilizer`, `relInertia_eq_bot_iff_isUnramifiedAt`, `relStabilizer_eq_bot_iff`,
  `relStabilizer_eq_zpowers_arithFrobAt`, the restriction lemmas
  `relAlgebraMap_smul_restrictNormal` / `relRestrictNormal_mem_stabilizer`, and
  `relStabilizer_le_of_splitsCompletelyIn`.

Their combination is

```
exists_relStabilizer_eq_zpowers :
  (Subgroup.zpowers σ).Normal → (orderOf σ).Prime → ∀ T : Finset (HeightOneSpectrum (𝓞 k)),
    ∃ v ∉ T, v ∉ relRamifiedSet k L, ∃ P over v,
      MulAction.stabilizer Gal(L/k) P = Subgroup.zpowers σ ∧
      Subgroup.zpowers (arithFrobAt (𝓞 k) Gal(L/k) P) = Subgroup.zpowers σ
```

— for `σ` of prime order generating a normal subgroup, the decomposition group at infinitely many
primes of the base is exactly `⟨σ⟩`, and the Frobenius there generates `⟨σ⟩`.  It is **not** the
statement `Frob_P = σ`: what is produced is `Frob_P = σ^j` for an uncontrolled `j ≢ 0 mod p`.

### (b) The ambiguity is not removable by splitting conditions

"Splits completely in `F`" is the condition `Frob ∈ Gal(M|F)`, i.e. membership in a *subgroup*.
Every subgroup of an abelian `A` containing `σ` contains every `jσ`, so no boolean combination of
complete-splitting conditions — in `M` or in any larger field, since the constraint sets pull back
to subgroups — separates `σ` from `jσ`.  Nor does a nonabelian crossing help: for
`G = A ⋊ ⟨c⟩` with `c` acting on `A ≅ 𝔽_p^d` by a generator of `𝔽_p^×`, the conjugacy class of `σ`
is exactly `{jσ : j ≠ 0}`.  Pinning a single `Frob` is therefore equivalent to genuine Chebotarev,
which needs `L(1, χ) ≠ 0` for `χ` of order `p`; for `p = 2` the ratio `ζ_M/ζ_k` gives it, for
`p = 3, 4, 6` the pair `|L(s,χ)|²` does, and for `p ≥ 5` there is no escape from analytic
continuation of Hecke `L`-series (which needs the ideal count with error term `O(x^{1-1/d})`, not
in Mathlib).

### (c) But Schmidt–Wingberg's Theorem 13 does not need it

Reading the proof (arXiv `math/9809211`, pp. 14–16) line by line: the odd-`p` half constructs a
sequence `z_1, z_2, … ∈ H¹(k_S|K, μ_p)` with

```
(1)  ∃ 𝔓_i ∈ S ∖ T(K) with (z_i)_{𝔓_i} ≡ Frob_{𝔓_i} mod H¹_nr(K_{𝔓_i}, μ_p),
                       and (z_i)_𝔓 ∈ H¹_nr(K_𝔓, μ_p) for all 𝔓 ≠ 𝔓_i,
(2)  (z_i)_𝔓 = ½ y_𝔓 for 𝔓 ∈ T(K),
(3)  (z_{n+1})_{σ𝔓_i} = −(z_i)_{σ𝔓_i} for i ≤ n and all σ ∈ G(K|k) ∖ {1},
```

the prime `𝔓_{n+1}` being produced by "using Čebotarev's density theorem, we can choose a prime
`𝔓_{n+1} ∈ S ∖ T_n(K)` such that the image of `−ξ` in `H¹(k_{T_n}|K, ℤ/pℤ)^∨` is equal to
`Frob_{𝔓_{n+1}}`".

`H¹(K_𝔓, μ_p)/H¹_nr` is **cyclic of order `p`** (local duality: it is dual to
`H¹_nr(K_𝔓, ℤ/p) = ℤ/p`), and the map to `H¹(k_{T_n}|K, ℤ/pℤ)^∨ ≅ Gal(k_{T_n}|K)` sends its
canonical generator to `Frob_𝔓`.  So a prime with `Frob_𝔓 = λ·(image of −ξ)`, `λ ≠ 0`, is just as
good: put `λ^{-1}` times the generator in the `𝔓`-slot, and the exactness of the upper line still
produces `z_{n+1}`.  Condition (1) weakens to

```
(1')  (z_i)_{𝔓_i} ≡ λ_i · Frob_{𝔓_i} mod H¹_nr,   λ_i ∈ 𝔽_p^×.
```

Propagate `λ` through the closing computation.  With `u = z_i(Frob_{σ𝔓_i})` and
`w = z_i(Frob_{σ𝔓_N})`, and using that the Hilbert symbol is bilinear:

| step | SW | with scalars |
| --- | --- | --- |
| `ψ` | `z_N(Frob_{σ𝔓_N}) = u` | unchanged |
| (1) for `z_i` | `(z_i, σz_i)_{σ𝔓_i} = u` | `= u^{λ_i}` |
| product formula | `(z_i, σz_i)_{𝔓_i} = u^{-1}` | `= u^{-λ_i}` |
| (3) | `(z_i, σz_N)_{𝔓_i} = u` | `= u^{λ_i}` |
| product formula | `(z_i, σz_N)_{σ𝔓_N} = u^{-1}` | `= u^{-λ_i}` |
| (1) for `z_N` | `= w` | `= w^{λ_N}` |

so `w^{λ_N} = u^{-λ_i}`, and what the proof needs is `w·u = 1`, i.e. `λ_i = λ_N`.  Nothing else in
the argument touches the normalization: the two product-formula steps use only the *support* of
`z_i` (the second bullet of (1)), and conditions (2), (3), (a), (b) are `λ`-free.

The scalars are then absorbed by the pigeonhole.  SW apply the shoe-box principle to
`ψ : {z_1, z_2, …} → μ_p^r` to get `i < N` with `ψ(z_i) = ψ(z_N)`; apply it instead to

```
z_i ↦ (ψ(z_i), λ_i) ∈ μ_p^r × 𝔽_p^×
```

— still a finite set, of size `p^r (p-1)` instead of `p^r` — and the pair `i < N` produced
satisfies `ψ(z_i) = ψ(z_N)` **and** `λ_i = λ_N`.  The proof goes through verbatim.

**Conclusion.**  For odd `p`, `exists_relStabilizer_eq_zpowers` is exactly the Chebotarev input
that Theorem 13 consumes.  Row 7 of the §0.36 table is closed on the odd side, with no `L`-series,
no ray-class groups and no analytic continuation.  (`Gal(k_{T_n}|K)` is a finite elementary abelian
`p`-group, so every nonzero element has order `p` and generates a normal subgroup — the two
hypotheses of the theorem.  The side condition `𝔓_{n+1} ∈ S = cs(Ω|k) ∪ T` is free: take
`L = k_{T_n}·Ω` and `σ` the element that is `ξ` on `k_{T_n}` and `1` on `Ω`, whereupon
`Frob ∈ ⟨σ⟩ ⊆ Gal(L|Ω)` forces complete splitting in `Ω` automatically.)

### (d) What is left of row 7

The `p = 2` half of Theorem 13 uses Chebotarev twice, and only one of the two is covered.

* Condition (1) at `p = 2` reads `(z_i)_{𝔓_i} ≡ Frob_{𝔓_i} mod H¹_nr(K_{𝔓_i}, μ_2)`, and
  `𝔽_2^× = {1}`: there is no scalar to absorb, and none is created, because
  `exists_relStabilizer_eq_zpowers` at `orderOf σ = 2` gives `Frob_P = σ` on the nose.  **Covered.**
* The Claim's proof needs: *"there exists a prime ideal `𝔔 ∉ T(K)` of `𝒪_{K,S_∞}` with
  `𝔔 ≠ σ𝔔` such that `𝔔 = 𝔄·(x)` with `x ∈ K^×`"* — i.e. **every ideal class of `Cl_{S_∞}(K)`
  contains a prime**, used to replace the fractional ideal `𝔄` in `(z̃_i) = 𝔓_i 𝔄²` by a prime, so
  that `z̃_i` and `σz̃_i` are coprime.  Here `[𝔔] = [𝔄]` is needed exactly: `𝔔² = 𝔄²(x²)` in the
  free abelian group of ideals forces `𝔔 = 𝔄(x)`.  `Cl_{S_∞}(K)` is an arbitrary finite abelian
  group, so this is *not* a prime-order statement and the scalar trick does not apply.  **Open.**
  Mathlib's `NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop` is the count of ideals of
  bounded norm in a fixed class — the *ideal* count, not the *prime* count; upgrading it is the
  non-vanishing `L(1, χ) ≠ 0` for an unramified class character.

So row 7 reduces to a single classical statement: **every ideal class of a number field contains
infinitely many prime ideals**.

---

## 0.42 Status (2026-08-31) — the degree-two glue is closed: `Ш²(k, μ_n) = 0` for the genuine decomposition subgroups of `G_k`

§0.38(c) named the one thing still open in row 3: `IsLocallySplitLevel` quantifies over the places
of a finite *level*, while membership in `sha2` is a statement about the decomposition subgroups of
`G_k` itself.  That glue is now a theorem, in both halves.

`IsLocallySplitLevel` (`Units/HasseTwo.lean`) is a **conjunction** — an archimedean clause over
`InfinitePlace ↥L` and a finite clause over `HeightOneSpectrum (𝓞 ↥L)` — so closing it required
building the archimedean mirror of the whole finite tower, not just the finite half.  This is where
the last sentence of §0.40 was wrong.

### (a) The finite half — `Units/TowerDescent.lean`, `Units/HasseTwoDecomposition.lean`

For a tower `k ⊆ F ⊆ K` of number fields and a prime `v` of `K`, a local coboundary of the
decomposition group at `v` with values in `(v.adicCompletion K)ˣ` descends to one of the
decomposition group at the prime below with values in the completion of `F`
(`exists_sub_add_eq_adicUnits_descent`).  The three inputs are: the decomposition group at `v` maps
*onto* the one below (`stabilizerRestrictPlaceFinite_surjective`), the kernel is the automorphisms
fixing `F`, and Hilbert 90 for that kernel (`Units/CompletionHilbert90.lean`) together with the
abstract descent of a 2-coboundary along a surjection (`GroupCohomology/CoboundaryDescent.lean`).

`exists_sub_add_eq_adicUnits_of_resH2` then goes from `sha2` to the local condition at a finite
place of a level: pick a prime `P` of `𝓞 Ω` above the place, take the trivialising cochain of
`stabilizer Gal(Ω/k) P`, use its *smoothness* to make it constant on the automorphisms fixing some
finite Galois `E₀`, enlarge the level to `E ⊔ E₀`, descend the cochain along the surjection onto
the decomposition group of that level, and finally descend the tower `k ⊆ E ⊆ E''`.

### (b) The archimedean half — `Units/InfiniteHilbert90.lean`, `Units/InfiniteTowerDescent.lean`

The same four steps, with `HeightOneSpectrum` replaced by `InfinitePlace` and `adicCompletion` by
`InfinitePlace.Completion`:

* `stabilizerAlgEquivInfinite` — **the decomposition group at an infinite place *is* the
  automorphism group of the completion there**, `↥(stabilizer Gal(K/k) w) ≃* (w.Completion ≃ₐ[…] …)`.
  This is what makes Hilbert 90 available: a subgroup `S` of it is the Galois group of `w.Completion`
  over the fixed field of the image, a *finite* extension, so
  `isMulCoboundary₁_of_isMulCocycle₁_stabilizerInfinite` is Mathlib's Hilbert 90 read through that
  isomorphism.
* `stabilizerRestrictPlaceInfinite_surjective` — surjectivity onto the decomposition group at the
  place below, from `NumberField.InfinitePlace.exists_smul_eq_of_comap_eq` (which needs no
  `NumberField` instance, so it also applies over an infinite `Ω`).
* `exists_infiniteUnitsComapHom_eq_of_ker` — the units of `w.Completion` fixed by the whole
  decomposition group over `F` are the units of the completion of `F`.
* `exists_sub_add_eq_infiniteUnits_descent` — the descent, assembled from the same abstract lemma.

`Units/InfiniteDecomposition.lean` gains `infiniteDecompositionSubgroups k Ω`, the archimedean
counterpart of `finiteDecompositionSubgroups`, and `Units/HasseTwoDecomposition.lean` gains the
`RestrictInfinitePlace` section and `exists_sub_add_eq_infiniteUnits_of_resH2`.

### (c) The assembly

```lean
theorem eq_one_of_mem_sha2 {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m)
    {ι : M →* kˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (z : SmoothH2 Gal(Ω/k) M)
    (hz : z ∈ sha2 M (finiteDecompositionSubgroups k Ω ∪ infiniteDecompositionSubgroups k Ω)) :
    z = 1
```

for `Ω` an algebraic closure of the number field `k` and `M` a `G_k`-trivial group of `n`-th roots
of unity.  A class of `sha2` is represented by a cocycle inflated from a finite Galois level; the
two bridge theorems turn the vanishing on the two families of decomposition subgroups into the two
clauses of `IsLocallySplitLevel` for that representative; and
`eq_one_of_forall_isLocallySplitLevel` (Albert–Brauer–Hasse–Noether plus Kummer theory) finishes.

So **row 3 is done**: `Ш²(k, μ_n) = 0` in the form the downstream Hochschild–Serre argument needs,
stated for the genuine decomposition subgroups of `G_k` and with no hypothesis left.

**Cost.** `Units/InfiniteTowerDescent.lean` needs `maxHeartbeats 4000000` on its headline theorem
and takes ~11 min to compile on its own; the pathology is instance search on `(w.Completion)ˣ`
(failing `Ring`/`AddCommGroup`/`LieRing` searches), the same one the three shortcut instances in
`Units/InfiniteHilbert90.lean` were introduced to cure.

Build: 9444 jobs green, zero warnings, zero sorries outside the comparator.

**What is left** is unchanged from §0.41: rows 5 and 8 (Poitou–Tate global duality), row 6 (the
`p`-th power Hilbert symbol and the product formula), row 7 (Chebotarev / "every ideal class
contains infinitely many primes", needed for `p = 2` only), and row 9 (the Schmidt–Wingberg
Theorem 13/14/15 assembly).

---

## 0.43 Status (2026-08-31) — cup products in low degrees

Two corrections to the §0.36 table first.

* **Row 4 is finished, not partial.**  The cell says "what is left of the row is
  `inv_M ∘ res = [M:K] · inv_K`".  That is exactly `localInvariant_baseChange` in
  `CFT/Brauer/LocalInvariantRestrict.lean`, together with `restrictScalars_divisionFrobenius`.
  Nothing is left of row 4.
* **The general-base class formation of §0.36(a) is not "bounded, mechanical".**
  `CFT/Units/IdeleQuotCyclic.lean` carries `[IsPrincipalIdealRing (𝓞 k)]` on
  `forall_mem_multiples_ideleQuot`, `addOrderOf_ideleQuot_eq`,
  `exists_addOrderOf_H2_ideleClassRep_eq` and
  `exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep`, and the class group is a genuine obstruction, not
  a convenience.  What *is* unconditional in `k` is the **order**: `first_inequality_index`
  (`Units/IdeleClassIndex.lean`), `card_tateModule_resObj_ideleClassRep_two_le`
  (`Units/IdeleClassTate.lean`) and the periodicity `tateH0AddEquivH2` give
  `#Ĥ⁰(Gal(F|k), C_F) = n` with no hypothesis; only the *cyclicity* of that group uses the
  principal-ideal hypothesis.  The repair is to work with `S`-ideles for a finite set `T` of primes
  generating `Cl(k)` and to choose the auxiliary prime `q` so that every `v ∈ T` splits completely
  in `F`, i.e. `q` split completely in `K · ℚ(ζ_{2n}) · ∏_{v ∈ T} ℚ(ζ_n, (Nv)^{1/n})`.

### The brick

Rows 5, 6 and 8 all consume cup products, and **neither Mathlib v4.28 nor this repository had
any** (`grep -ri cup Mathlib/RepresentationTheory/` is empty).
`CFT/GroupCohomology/Cup.lean` supplies them in the two degrees that matter, without the monoidal
structure on `Rep k G`: instead of a tensor product of representations the input is an equivariant
bilinear pairing of the coefficients,

```lean
(Φ : A →ₗ[k] B →ₗ[k] C) (hΦ : ∀ g a b, Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b))
```

and the product of two `1`-cochains is

```lean
cup₁₁ Φ f₁ f₂ = fun p => Φ (f₁ p.1) (B.ρ p.1 (f₂ p.2))
```

matching Mathlib's sign conventions for `d₀₁`, `d₁₂`, `d₂₃`.  The three computations are
`cup₁₁_mem_cocycles₂` (a product of cocycles is a cocycle), and
`cup₁₁_mem_coboundaries₂_left` / `_right` (a product with a coboundary is a coboundary), the latter
two with explicit primitives `y ↦ Φ a (f₂ y)` and `x ↦ -Φ (f₁ x) (B.ρ x b)`.  Descending through
`Submodule.liftQ` twice gives

```lean
cupH1 Φ hΦ : H1 A →ₗ[k] H1 B →ₗ[k] H2 C
cupH1_apply : cupH1 Φ hΦ (H1π A f₁) (H1π B f₂) = H2π C (cupCocycles₁₁ A B Φ hΦ f₁ f₂)
```

Note for the consumer: this is the **`Rep k G` / finite-level** flavour.  The profinite layer
(`CFT/Profinite/Cochain.lean`) is multiplicative — `IsMulCocycle₁`/`IsMulCocycle₂` and
`SmoothH1`/`SmoothH2` — so a multiplicative, smoothness-preserving mirror will be needed before the
Hilbert symbol can be written as `H¹(G_K, μ_p) × H¹(G_K, μ_p) → H²(G_K, μ_p)`.  Smoothness is the
easy half: the product of two cochains constant on the cosets of `N` and `N'` is constant on the
cosets of `N ⊓ N'`, which is `IsOpenNormal.inf`.

Build: 9445 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.44 Status (2026-08-31, later) — the profinite cup product, and `H¹(G_k, μ_n) = kˣ/(kˣ)ⁿ`

The mirror that §0.43 asked for is built, and with it the first cohomology of an *infinite* Galois
group is now computed, not merely defined.  Five modules, all sorry- and axiom-free.

### (a) `CFT/Profinite/Cup.lean` — the multiplicative cup product

The input is a pairing `Φ : M → M' → M''` of the coefficients of three smooth modules,
multiplicative in each variable and compatible with the three actions, and the product of two
`1`-cochains is

```lean
mulCup₁₁ Φ u v = fun p => Φ (u p.1) (p.1 • v p.2)
```

with `isMulCocycle₂_mulCup₁₁`, `isSmooth₂_mulCup₁₁` (the subgroup at which the product is constant
is the intersection of the three subgroups for the two factors and the action — `IsOpenNormal.inf`,
exactly as predicted), and `mulCup₁₁_mem_smoothCoboundary₂_left`/`_right` with explicit primitives.
Descending gives

```lean
cupSmoothH1 Φ hΦ : SmoothH1 G M → SmoothH1 G M' →* SmoothH2 G M''
```

`comapH2_cupSmoothH1` makes it commute with pullback along any smooth homomorphism, hence
`resH2_cupSmoothH1` with restriction to a subgroup, hence `cupSmoothH1_mem_sha2_left`/`_right`:
**a cup product one of whose factors is everywhere locally trivial is everywhere locally trivial.**
That is the shape in which the Hilbert symbol will be consumed.

### (b) `CFT/Profinite/Hilbert90.lean` — Hilbert 90 for an infinite Galois group

`isMulCoboundary₁_of_isMulCocycle₁_smooth`: a *smooth* `1`-cocycle of `Gal(Ω|k)` with values in
`Ωˣ` is the coboundary of a single unit; hence `subsingleton_smoothH1_units`.  The reduction to the
finite case is the only interesting step and it is short: a smooth cochain is constant on the
cosets of an open normal subgroup, the fixing subgroups of the finite Galois levels are cofinal
among those (`exists_fixingSubgroup_le`, §0.40), and the values of a cocycle constant on the cosets
of `E.fixingSubgroup` are *fixed* by that subgroup, so by `InfiniteGalois.fixedField_fixingSubgroup`
they lie in `E` itself.  Choosing a preimage of each automorphism of `E` turns the cocycle into a
cocycle of the finite level, Noether's form supplies a primitive there, and the primitive works
upstairs unchanged because every automorphism of `Ω` acts on `E` through its restriction.

### (c) `CFT/Profinite/Kummer.lean` — the two directions

With a primitive `n`-th root of unity in the base, the coefficients are an abstract `M` mapping
into `kˣ` by `ι` with image the `n`-th roots of unity — deliberately the *same* convention as
`eq_one_of_mem_sha2` (row 3), so the two layers compose.

* `exists_isMulCocycle₁_kummer`: if `β ^ n = a` with `a ∈ kˣ` then `σ ↦ σ • β / β` has values in
  the `n`-th roots of unity of the base, and the resulting `M`-valued cochain is a *smooth*
  cocycle.  Smoothness is where the infinite case differs from the finite one, and it comes from
  `exists_isOpenNormal_forall_apply_eq`: a single element of `Ω` is fixed by the subgroup fixing
  the normal closure of the field it generates, which is open because that closure is finite.
* `exists_pow_eq_of_isMulCocycle₁`: conversely, Hilbert 90 turns a smooth cocycle into a radical
  `β`, and `β ^ n` is fixed by everything, hence lies in the base.
* `smoothH1Mk_eq_one_iff_exists_pow`: the class is trivial exactly when the radicand is already an
  `n`-th power in the base.

### (d) `CFT/Profinite/KummerHom.lean` — the isomorphism

`IsKummerData k Ω M ι n` bundles the five hypotheses (a primitive root in `k`, the trivial action
on `M`, `ι` injective with image the `n`-th roots of unity, and an `n`-th root in `Ω` of every unit
of `k`).  Two roots of the same unit differ by a root of unity of the base, which every
automorphism fixes, so `smul_div_eq_of_pow_eq` says the coboundary does not depend on the root; and
a cocycle is determined by its coboundary because `ι` is injective.  So `cochain` is well defined,
`cochain_mul` is multiplicative, and

```lean
kummerHom      : kˣ →* SmoothH1 Gal(Ω/k) M
ker_kummerHom  : kummerHom.ker = (powMonoidHom n).range
kummerHom_surjective
kummerEquiv    : kˣ ⧸ (powMonoidHom n : kˣ →* kˣ).range ≃* SmoothH1 Gal(Ω/k) M
```

**Non-vacuity was a genuine risk** and is now closed.  A grep showed that the abstract-`M`-with-`ι`
convention introduced by row 3 had never once been instantiated, so the entire layer could have
been about an empty class of data.  `isKummerData_rootsOfUnity` supplies the witness — `M` is
`rootsOfUnity n k` with the trivial action (`rootsOfUnityTrivialAction`, kept a `def` rather than a
global instance to avoid an instance diamond on `Gal(Ω/k)`-actions), and `exists_units_pow_eq`
supplies the roots whenever `Ω` is algebraically closed.

### (e) `CFT/Profinite/KummerRes.lean` — restriction, and Ш¹ in Kummer terms

The point of the whole layer.  The cochain of `a` measures how far a chosen root is from being
fixed, and because the action on the coefficients is trivial a cocycle is a coboundary on a
subgroup exactly when it *vanishes* there.  So

```lean
resH1_kummerClass_eq_one_iff_smul_root : resH1 D (h.kummerClass a) = 1 ↔ ∀ d ∈ D, d • h.root a = h.root a
resH1_kummerClass_eq_one_iff_mem_fixedField :
  resH1 D (h.kummerClass a) = 1 ↔ ∃ b ∈ IntermediateField.fixedField D, b ^ n = algebraMap k Ω a
resH1_fixingSubgroup_kummerClass_eq_one_iff :
  resH1 E.fixingSubgroup (h.kummerClass a) = 1 ↔ ∃ b : ↥E, (b : Ω) ^ n = algebraMap k Ω a
```

No closedness hypothesis on `D` is needed: the fixed field is taken as it stands, and the
intermediate-field form follows from `InfiniteGalois.fixedField_fixingSubgroup`.  Over a family `S`
of subgroups this reads off the everywhere locally trivial classes: `localPowers S` is the subgroup
of `kˣ` of units that are `n`-th powers in the field fixed by every `D ∈ S`, and

```lean
map_localPowers : (h.localPowers S).map h.kummerHom = sha1 M S
```

For `S` the genuine decomposition subgroups of `G_k` (`decompositionSubgroups`, §0.40) this is
exactly **`Ш¹(k, μ_n) = {a ∈ kˣ : a is locally an n-th power} / (kˣ)ⁿ`**, which is the object the
dual of row 5 has to be paired with, and the object Theorem 13 of Schmidt–Wingberg computes.

### What this does and does not unlock

It does *not* touch rows 5 and 8: Poitou–Tate is still wall #1.  What it does is make rows 6 and 9
writable in the same language as row 3.  The remaining piece for the Hilbert symbol itself is the
**invariant map on `SmoothH2`** — the repository has `localInvariant` only at the finite level
(`CFT/Brauer/LocalInvariant.lean`), and the bridge `SmoothH2 G_K Ωˣ ≅ Br(K)` does not exist.
Building it needs one compatibility that a search of the 81 modules of `CFT/Brauer/` did not turn
up: that the crossed product of an *inflated* cocycle (same base, larger splitting field) has the
same Brauer class, i.e. `(Ω_E/K, inf f) ≅ M_{[E:L]}((L/K, f))`.  That is the next brick on this
line.

Build: 9450 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.45 Status (2026-08-31, night) — Ш² restricts to a larger base, and inflation preserves the Brauer class

Two bricks, and one correction to the §0.26 table.

### (a) `CFT/Units/DecompositionRestrict.lean` — step 1 of the narrowed route of §0.26

§0.26 narrowed the remaining route to: *first* show that an everywhere locally trivial class over
`k` dies after passing to a base that contains the roots of unity, *then* feed that into
Hochschild–Serre.  Step 1 is now a theorem.  Three pieces:

* `continuous_galRestrictScalarsHom` — an automorphism of `Ω` over an intermediate field `k ⊆ K` is
  in particular one over `k`, and that inclusion `Gal(Ω/K) → Gal(Ω/k)` is *continuous* for the
  Krull topologies.  The proof is the only one with content: a finite subextension `E/k` is
  finitely generated (`IntermediateField.essFiniteType_iff` is the practical route to `E.FG`),
  adjoining generators to `K` gives a finite subextension of `Ω/K`, and an automorphism fixing the
  latter fixes `E` pointwise because `E` lands in the fixed field of the group it generates.
* `decompositionSubgroups_le_galRestrictScalarsHom` — a prime of `𝓞 Ω` and an archimedean place of
  `Ω` are *the same objects* whichever base one works over, and the two stabilizer conditions are
  literally the same proposition, so each decomposition subgroup over `K` sits inside the
  corresponding one over `k`.  Both cases are `rw [mem_stabilizer_iff] at hx ⊢; exact hx`.
* `comapH2_mem_sha2_decompositionSubgroups` (and its degree-one twin) — feeding those two into
  `comapH2_mem_sha2` (§0.40): **Ш²(k, ·) restricts into Ш²(K, ·)**.

Composing with row 3 gives the statement the route asked for:

```lean
theorem eq_one_of_mem_sha2_of_isPrimitiveRoot_intermediate … :
    comapH2 (galRestrictScalarsHom k K Ω) hπ (isSmoothHom_galRestrictScalarsHom k K Ω) z = 1
```

so `Ш²(k, M) ⊆ ker(H²(k, M) → H²(K, M))` whenever `K` contains the `n`-th roots of unity.

**Correction to the §0.26 table.**  Four of its rows are stale.  "the fundamental class of a class
formation", "Tate's cohomological triviality theorem", "Tate–Nakayama" and "cup products" were all
listed as *absent*; `baseFundamentalClass`, `baseTateEquiv`, `baseTateNakayamaEquiv` and
`baseArtinEquiv` landed in `74e3a6d` (§0.35–§0.36) and `CFT/Profinite/Cup.lean` in §0.44.  The
residual obstacle in that direction is narrower than the table suggests: the `Module.Flat ℤ`
hypothesis on the coefficients, which `p`-torsion modules do not satisfy (§0.28).

### (b) `CFT/Brauer/CrossedProductInflate.lean` — the brick §0.44 named

§0.44 ended by naming the missing compatibility for the bridge `SmoothH2 G_K Ωˣ ≅ Br(K)`: that
inflating a cocycle to a larger splitting field does not change the Brauer class.  That is now a
theorem.

For a tower `K ⊆ L ⊆ L'` of finite Galois extensions, the inflation of `f : Gal(L/K)² → Lˣ` is

```lean
inflateCocycle L' f = fun p => Units.map (algebraMap L L')
  (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2))
```

and it is a cocycle by a transport lemma stated for an arbitrary pair of a group homomorphism and
an equivariant coefficient homomorphism (`isMulCocycle₂_comp`), instantiated at
`AlgEquiv.restrictNormalHom L` and `Units.map (algebraMap L L')`; the equivariance
`smul_units_map_algebraMap` is `AlgEquiv.restrictNormal_commutes` wrapped in `Units.ext`.

The recognition theorem is the `CyclicTower.lean` pattern run for an arbitrary Galois group instead
of a cyclic one, and it reuses that file's `coordMatrix` toolkit verbatim.  Given a simple algebra
`A` of dimension `[L : K]²` containing `L` via `emb` together with units `u σ` conjugating it by
`Gal(L/K)` and multiplying by `f`, and a basis `b : Basis ι L L'`, put

```lean
W σ = emb.mapMatrix (coordMatrix b fun j => σ (b j)) * diagonal (fun _ => u (σ.restrictNormal L))
```

inside `Matrix ι ι A`.  Two facts make these the symbols of the inflated cocycle:
`coordMatrix_map`, which says `S (σ * τ) = S σ * (S τ).map (σ|_L)` — that is exactly the semilinear
cocycle identity the change-of-basis matrices satisfy — and `hDcomm`, which says the diagonal of a
symbol conjugates matrix entries by the restriction.  A dimension count
`finrank K (Matrix ι ι A) = [L:K]² · |ι|² = [L':K]²` then lets
`crossedProductAlgHom_bijective` (§0.36's recognition API) conclude:

```lean
nonempty_algEquiv_matrix_inflateCocycle :
  Nonempty (CrossedProduct (isMulCocycle₂_inflateCocycle (L' := L') hf) ≃ₐ[K]
    Matrix (Fin (finrank L L')) (Fin (finrank L L')) A)
```

Applying it to `A = CrossedProduct hf` itself, with `emb = inclAlgHom hf` and the symbols
`unitSymbol hf g = (isUnit_single_one hf g).unit`, gives the headline

```lean
mk_csa_inflateCocycle (hf : IsMulCocycle₂ f) :
  (⟦csa (isMulCocycle₂_inflateCocycle (L' := L') hf)⟧ : BrauerGroup K) = ⟦csa hf⟧
```

i.e. `(L'/K, inf f) ≅ M_{[L':L]}((L/K, f))` in the Brauer group.  This is the cyclic
`cyclicBrauerHom_restrictNormal` of `CyclicTower.lean` with the cyclicity dropped.

**Lean note.**  `crossedProductAlgHom` and `crossedProductAlgHom_bijective` live in a
`variable {K L A : Type u}` block, so the target algebra must be in the *same* universe as `K`.
Declaring the index type `{ι : Type*}` makes `Matrix ι ι A : Type (max u u_1)` and the application
fails on universes; `{ι : Type}` (so `max 0 0 u = u`) is the fix, and it costs nothing because the
only instantiation is `Fin (finrank L L')`.

### What is left

Unchanged: rows 5 and 8 (Poitou–Tate global duality, wall #1), row 6 (the `p`-th power Hilbert
symbol and the product formula), row 7 (Chebotarev, `p = 2` only), row 9 (the Schmidt–Wingberg
Theorem 13/14/15 assembly).  On the row-6 line the next step is now the colimit itself:
`colim_L H²(Gal(L/K), Lˣ) ≅ colim_L Br(L/K) = Br(K)`, for which (b) supplies the compatibility that
makes the maps of the colimit system well defined, and then the composite with `localInvariantHom`
is the invariant map on `SmoothH2`.

Build: 9454 jobs green, zero warnings, zero sorries outside the comparator; the new headline has
axioms `[propext, Classical.choice, Quot.sound]`.

---

## 0.46 Status (2026-08-31, late night) — the colimit: `SmoothH2(G_k, Ωˣ) ↪ Br(k)`

§0.45(b) supplied the compatibility; this section builds the map it makes well defined.  The
statement is the one the row-6 line asked for:

```lean
smoothBrauerHom : SmoothH2 Gal(Ω/k) Ωˣ →* BrauerGroup k
smoothBrauerHom_injective : Function.Injective (smoothBrauerHom (k := k) (K := Ω))
```

for an arbitrary Galois extension `Ω/k` (no finiteness anywhere).  Three files moved.

### (a) `CFT/Profinite/Cochain.lean` — three quotient lemmas

`smoothH2Mk` is a `QuotientGroup.mk` of a subtype, so the three obvious facts about it were
missing and every one of them is needed below:

* `smoothH2Mk_congr` — equal cocycles have equal classes (a `subst` + `rfl`; it exists only to
  avoid dependent rewriting, since the proof arguments change type when the cocycle does);
* `smoothH2Mk_eq_iff` — **two classes agree exactly when the quotient of the cocycles is the
  coboundary of a *smooth* cochain**, via `QuotientGroup.eq` and `Subgroup.mem_subgroupOf`
  followed by a `show` that turns the subgroup membership `b⁻¹ * a ∈ smoothCoboundary₂` into the
  pointwise `fun p => a p / b p`;
* `smoothH2Mk_eq_mul` — the same dodge for `smoothH2Mk_mul`.

### (b) `CFT/Brauer/InflateTower.lean` — transitivity of inflation, and the compositum trick

**Transitivity.**  For a tower `k ⊆ L ⊆ L' ⊆ K` of normal subfields,

```lean
inflateCocycle_trans (w : Gal(L/k)² → Lˣ) :
  inflateCocycle K (inflateCocycle L' w) = inflateCocycle K w
```

This is short because Mathlib already has the restriction half:
`IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply` (`FieldTheory/Normal/Defs.lean:245`) says
`σ|_L = (σ|_{L'})|_L`, so the proof is `Units.ext` plus a three-step `rw` ending in
`← IsScalarTower.algebraMap_apply`.

**Raising a level.**  The awkwardness in stating "compare two levels in their compositum" is that
`Algebra ↥E ↥F` for `E ≤ F` is *not* an instance — the two are intermediate fields of the same
`K`, not a tower.  Rather than introduce a global instance (which would clash with the ambient
`Algebra ↥E K`), the level-raising is packaged as an existential whose *statement* never mentions
the extra algebra, and the instances live inside the proof:

```lean
exists_cocycle_of_le (hEF : E ≤ F) (hw : IsMulCocycle₂ w) :
  ∃ v (hv : IsMulCocycle₂ v), inflateCocycle K v = inflateCocycle K w ∧
    (⟦CrossedProduct.csa hv⟧ : BrauerGroup k) = ⟦CrossedProduct.csa hw⟧
```

with `letI : Algebra ↥E ↥F := ((IntermediateField.inclusion hEF).toRingHom).toAlgebra` and both
scalar towers by `IsScalarTower.of_algebraMap_eq fun _ => rfl` — all three `rfl`s hold on the nose.
The witness is `inflateCocycle ↥F w`; the first conjunct is `inflateCocycle_trans` and the second
is §0.45(b)'s `mk_csa_inflateCocycle`.

**Well-definedness.**  With those two, the key comparison is a five-line proof: given cocycles at
levels `E₁, E₂` whose inflations to `K` have the same smooth class, raise both to `E₁ ⊔ E₂` (which
is finite and Galois over `k` by `IntermediateField.finiteDimensional_sup` and the repo's
`isGalois_sup`), read the hypothesis through `smoothH2Mk_eq_iff` to get a smooth cochain
trivialising the quotient, and feed it to `SmoothLevel.lean`'s
`isMulCoboundary₂_of_coboundary₂_inflateCocycle` — the descent of a smooth trivialisation to the
level — to conclude via `mk_csa_eq_mk_csa_iff`:

```lean
mk_csa_eq_mk_csa_of_smoothH2Mk_eq :
  … → (⟦CrossedProduct.csa hw₁⟧ : BrauerGroup k) = ⟦CrossedProduct.csa hw₂⟧
```

`existsUnique_mk_csa` then packages "every smooth class comes from some level"
(`exists_isGalois_levelCocycle₂`) with that uniqueness into an `∃!`, `smoothBrauer` is its
`choose`, and `mk_csa_eq_smoothBrauer` is the defining property.  Multiplicativity
(`smoothBrauer_mul`) is the same compositum argument once more: raise the two levels to
`E₁ ⊔ E₂`, note that inflation is multiplicative (`map_mul` of `Units.map`), and use
`CrossedProduct.mk_csa_mul`.  `MonoidHom.mk'` then avoids proving `map_one` separately.

**Injectivity.**  A cocycle at a finite level whose crossed product splits is a coboundary there
(`mk_csa_eq_one_iff`), and the inflation of that trivialising cochain — pull back along
`AlgEquiv.restrictNormalHom E` and push forward along `Units.map (algebraMap ↥E K)` — is smooth
(it is constant on the cosets of `E.fixingSubgroup`, which is open normal) with differential the
inflated coboundary.  So the class dies in `SmoothH2`:

```lean
smoothH2Mk_eq_one_of_mk_csa_eq_one (hw : IsMulCocycle₂ w)
    (h : (⟦CrossedProduct.csa hw⟧ : BrauerGroup k) = 1) :
  smoothH2Mk (inflateCocycle K w) … = 1
```

and `injective_iff_map_eq_one` plus `exists_isGalois_levelCocycle₂` finishes.

**Lean note.**  `isGalois_sup` already existed in `CFT/Compositum.lean` (proved by `inferInstance`);
declaring it again is a hard error, not a shadow.  The `omit`s the `unusedSectionVars` linter asked
for are all of `[IsGalois k K]`, plus `[FiniteDimensional k ↥E]` on the coboundary computation —
the `IsGalois k K` hypothesis is only needed for the *surjectivity* half (`exists_levelCocycle₂`),
never for inflation itself.

### What is left

Unchanged: rows 5 and 8 (Poitou–Tate, wall #1), row 7 (Chebotarev, `p = 2` only), row 9 (the
Schmidt–Wingberg 13/14/15 assembly).  On row 6 the remaining step is *surjectivity* of
`smoothBrauerHom` — every class of `Br(k)` is split by some finite Galois extension, which is
`H2Surjective.lean`'s `exists_brauerHom_eq` at each level, modulo its universe-0 restriction — and
then the composite with `localInvariantHom` is the invariant map on `SmoothH2`.

---

## 0.47 Status (2026-08-31, late night) — `H²(G_k, k̄ˣ) = Br(k)`, and `= ℚ/ℤ` for a local field

§0.46 built `smoothBrauerHom` and proved it injective.  It is also surjective, as soon as the top
field is an algebraic closure of a **perfect** field, and then the local invariant turns it into an
isomorphism with `ℚ/ℤ`.

### (a) `CFT/Brauer/SmoothBrauer.lean`

Two steps, both short because the pieces were already there.

* `exists_mk_csa_eq_of_mem_relative` — a `Type u` restatement of `H2Surjective.lean`'s
  `exists_brauerHom_eq`, avoiding that file's universe-0 restriction.  The restriction came from
  `brauerHom`, which the statement need not mention: `exists_csa_finrank_sq_of_mem_relative`
  (`SplittingSubfield.lean`) and `exists_algEquiv_crossedProduct_of_finrank_sq`
  (`CrossedProductRecognition.lean`) are both stated in `Type u`, and chaining them directly gives
  `∃ c (hc : IsMulCocycle₂ c), ⟦CrossedProduct.csa hc⟧ = x`.
* `smoothBrauerHom_surjective` — `GaloisSplitting.lean`'s `exists_isGalois_mem_relative` produces a
  finite Galois level `E ⊆ k̄` splitting the class, the previous bullet produces a cocycle there,
  and `mk_csa_eq_smoothBrauer E hc rfl` identifies its inflation's smooth class as a preimage.

Hence

```lean
smoothBrauerEquiv (k) [PerfectField k] :
  SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ ≃* BrauerGroup k
```

**The Brauer group of a perfect field is the smooth second cohomology of its absolute Galois
group.**  Note `smoothBrauerHom` elaborates at `BrauerGroup.{u, u}`, which is what
`localInvariantEquiv` (stated at `BrauerGroup.{0, 0}`) needs when `k : Type`.

### (b) `CFT/Brauer/SmoothInvariant.lean`

Composing with §'s `localInvariantEquiv`:

```lean
smoothLocalInvariantEquiv (K) [PerfectField K] (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) :
  SmoothH2 Gal(AlgebraicClosure K/K) (AlgebraicClosure K)ˣ ≃* Multiplicative QModZ
```

This is the invariant map of local class field theory in cohomological form — the half of the norm
residue symbol that turns a cup product into a number.

### Why this is on the critical path

Re-reading §0.41(c): SW's Theorem 13 consumes the `p`-th power Hilbert symbol only through
(i) bilinearity, (ii) the product formula `∏_v (a, b)_v = 1`, and (iii) the local computation
`(z, σz)_𝔓 = z(Frob_𝔓)` at a prime where one argument is unramified.  All three are statements
about `inv_v(χ_a ∪ χ_b)`, so the invariant map on `SmoothH2` is the first of the two halves.  The
second is the cup product `H¹(G, μ_p) × H¹(G, μ_p) → H²(G, k̄ˣ)`, which `CFT/Profinite/Cup.lean`
already supports *provided* the base contains `μ_p`: for a trivial action on `μ_p` the pairing
`Φ(ζ^a)(η) = η^a` is genuinely `G`-equivariant (for a non-trivial action it is not — that is the
`μ_p ⊗ μ_p` twist), and SW work over a base containing `μ_p` throughout.

Build: 9458 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.48 Status (2026-08-31, late night) — coefficient functoriality, and `H²(G, μ_n) = Br(k)[n]`

Two bricks, both prerequisites for the Hilbert symbol named at the end of §0.47.

### (a) `CFT/Profinite/Coeff.lean` — functoriality in the coefficients

The repo had `Comap.lean` (functoriality in the *group*) but nothing in the *coefficients*.  For a
homomorphism `φ : M →* N` commuting with the two actions:

```lean
coeffMap₁ φ u := fun g => φ (u g)          coeffMap₂ φ a := fun p => φ (a p)
coeffH1 φ hφ : SmoothH1 G M →* SmoothH1 G N
coeffH2 φ hφ : SmoothH2 G M →* SmoothH2 G N
```

All the content is that the cocycle relations are equations built from the group law and the
action, that a cochain constant on the cosets of an open normal subgroup stays constant there, and
that `coboundary₂ (coeffMap₁ φ u) = coeffMap₂ φ (coboundary₂ u)`.  Both maps are computed on
cocycles by `rfl`.

⚠ One asymmetry to remember: `coeffH1`'s descent needs `(coeffMap₁_smul_div φ hφ t).symm` while
`coeffH2`'s needs the *unsymmetrised* equation, because `smoothCoboundary₁`'s carrier is
`{u | ∃ t, (fun g => g • t / t) = u}` and `smoothCoboundary₂`'s is
`{a | ∃ u, IsSmooth₁ u ∧ coboundary₂ u = a}` — the two equations point in opposite directions.

### (b) `CFT/Profinite/KummerTwo.lean` — the Kummer sequence one degree up

Let `Ω/k` be Galois with every unit of `Ω` having an `n`-th root (e.g. `Ω = k̄`), and let
`ι : M →* Ωˣ` be an injective equivariant map onto the `n`-th roots of unity of `Ω`.  Then

* `pow_coeffH2_eq_one` — every class in the image is killed by `n`;
* `coeffH2_injective` — **`coeffH2 ι : H²(G, M) → H²(G, Ωˣ)` is injective**;
* `exists_coeffH2_eq_of_pow_eq_one` — **every class killed by `n` is in the image**;
* `range_coeffH2`, `kummerH2Equiv` — so `H²(G, μ_n) ≅ H²(G, Ωˣ)[n]`, which by §0.47 is `Br(k)[n]`
  when `k` is perfect and `Ω = k̄`.

Injectivity is Hilbert 90.  If `ι ∘ b = coboundary₂ w`, then `coboundary₂ (wⁿ) = 1`, so `wⁿ` is a
smooth *one* cocycle, so `wⁿ = g ↦ g•β/β`; an `n`-th root `γ` of `β` corrects `w` into
`t g := w g · γ / (g•γ)`, whose `n`-th power is `(g•β/β)·(β/g•β) = 1` and whose coboundary is still
`coboundary₂ w` (because `g ↦ γ/(g•γ)` is the inverse of a one cocycle).  Surjectivity onto the
`n`-torsion is the same computation backwards: choose an `n`-th root `ρ(y)` of every unit, put
`v := ρ ∘ u` where `coboundary₂ u = aⁿ`, and `a / coboundary₂ v` takes values in `μ_n`.

**The one real obstacle** was smoothness of `coboundary₂ v`.  `Cochain.lean`'s
`IsSmooth₁.coboundary₂` needs `IsSmoothAction G M` — *one* open normal subgroup acting trivially on
*all* of `M` — and `Ωˣ` does not satisfy that.  The fix is that it does not have to: a smooth
cochain `u : Gal(Ω/k) → Ωˣ` is constant on the cosets of `E.fixingSubgroup` for a *finite* Galois
level `E` (`exists_fixingSubgroup_le`), and `restrictNormalHom_surjective_level` gives a section, so
`u` has only `|Gal(E/k)|` values; the normal closure of the field they generate is a finite level
whose fixing subgroup fixes them all.  That is

```lean
exists_isOpenNormal_forall_smul_eq_of_isSmooth₁ :
  IsSmooth₁ u → ∃ P, IsOpenNormal P ∧ ∀ g m, m ∈ P → m • u g = u g
isSmooth₂_coboundary₂_of_isSmooth₁ : IsSmooth₁ u → IsSmooth₂ (coboundary₂ u)
```

and the second is `Cochain.lean`'s proof verbatim with `hact n hn.2` replaced by `hfix y n hn.2`.

### Why this is on the critical path

The Hilbert symbol wants `H¹(G, μ_p) × H¹(G, μ_p) → H²(G, μ_p) → H²(G, k̄ˣ) —inv→ ℚ/ℤ`.
`Cup.lean` gives the first arrow (for `μ_p` in the base, the pairing `Φ(ζᵃ)(η) = η^a` is
`G`-equivariant), `coeffH2 ι` is the second, and §0.47's `smoothLocalInvariantEquiv` is the third.
Injectivity of `coeffH2 ι` is what makes the symbol *faithful*: a cup product is trivial in
`Br(K)` exactly when it is trivial in `H²(G, μ_p)`.

Build: 9460 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.49 Status (2026-08-31, late night) — the `n`-th power symbol

Row 6 of the §0.36 table asks for the `p`-th power Hilbert symbol.  Its *definition* and its
formal properties are now in the repository; only the product formula (global reciprocity) is
still missing.

### `CFT/Profinite/Symbol.lean`

Given Kummer data `h : IsKummerData k Ω M ι n` (see `KummerHom.lean`: `M` is an abstract copy of
the `n`-th roots of unity with its trivial `Gal(Ω/k)`-action, `ι : M →* kˣ` the inclusion) and a
pairing `Φ : M →* M →* M`, the symbol is the cup product of the two Kummer classes:

```lean
noncomputable def kummerSymbol : kˣ →* kˣ →* SmoothH2 Gal(Ω/k) M where
  toFun a := (cupSmoothH1 Φ (h.equivariant Φ) (h.kummerHom a)).comp h.kummerHom
```

Bimultiplicativity is free — it is exactly the statement that `kummerHom` and `cupSmoothH1` are
homomorphisms, so `map_one'`/`map_mul'` are one `rw` each.  Because the action on `M` is trivial,
*every* pairing is equivariant (`IsKummerData.equivariant`, proved by three rewrites with
`h.smul_eq`), which is what keeps `kummerSymbol h Φ` a two-argument gadget instead of a
three-argument one carrying an equivariance proof around.

The four properties that make it usable:

* `kummerSymbol_eq_one_of_isPow_left` / `_right`: the symbol is trivial as soon as one argument is
  an `n`-th power in `k`.  This is `kummerClass_eq_one_iff` plus `map_one`, so the symbol descends
  to `kˣ/(kˣ)ⁿ × kˣ/(kˣ)ⁿ`.
* `resH2_kummerSymbol`: restriction to a subgroup `H ≤ Gal(Ω/k)` turns the symbol into the symbol
  of the restricted classes — that is, the symbol localizes.  This is `resH2_cupSmoothH1` from
  `Cup.lean`.
* `kummerSymbol_mem_sha2_left` / `_right`: combining the previous two with `KummerRes.lean`'s
  `resH1_kummerClass_eq_one_iff`, a symbol one of whose arguments lies in `h.localPowers S` is in
  `sha2 M S`.  Over a number field, with `S` the decomposition subgroups, this says: *a symbol one
  of whose arguments is locally a power everywhere is everywhere locally trivial.*
* `pow_kummerSymbol_eq_one`: the symbol is killed by `n`.  The general fact behind it,
  `smoothH2_pow_eq_one`, is that `H²(G, M)` is killed by `n` when `M` is — one line, because
  `coboundary₂ 1 = 1`.

### Avoiding a discrete logarithm

A pairing `μ_n × μ_n → μ_n` is *not* canonical: it is a choice of a primitive root, i.e. a
discrete logarithm.  Rather than manufacture one on an abstract cyclic group, the file supplies
the model where the pairing is free:

```lean
def mulZMod : Multiplicative (ZMod n) →* Multiplicative (ZMod n) →* Multiplicative (ZMod n)
noncomputable def zmodRootHom (hζ : IsPrimitiveRoot ζ n) : Multiplicative (ZMod n) →* kˣ
theorem isKummerData_zmod (hζ) (hroot) : IsKummerData k Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n
```

`mulZMod` is multiplication in `ZMod n` read multiplicatively, and `zmodRootHom hζ` sends a
residue `a` to `ζ^a.val`.  That this is a homomorphism is `ZMod.val_add` together with
`pow_mod_of_pow_eq_one`; injectivity is `IsPrimitiveRoot.pow_inj` on representatives below `n`,
and surjectivity onto the `n`-th roots of unity is `IsPrimitiveRoot.eq_pow_of_pow_eq_one` with
`ZMod.val_cast_of_lt`.  The trivial action `zmodTrivialAction` is a `def` used through `letI`,
deliberately not a global instance — the same pattern as `rootsOfUnityTrivialAction`.

⚠ In this Mathlib pin `Multiplicative` is a plain `def`, `ofAdd`/`toAdd` are `Equiv`s, and the
simp lemmas `ofAdd_toAdd`, `toAdd_mul`, … live in the **root** namespace, *not* under
`Multiplicative.`; `Multiplicative.ofAdd_toAdd` is an unknown constant.  All of them are `rfl`, so
the file uses `show`/`rfl` throughout and closes injectivity with `Multiplicative.ext` (which
*does* exist) applied to `ZMod.val_injective`.

### Landing the symbol in the Brauer group

`IsKummerData.unitsHom = Units.map (algebraMap k Ω) ∘ ι : M →* Ωˣ` is the coefficient
homomorphism into the units of the extension; it is equivariant because the base units are fixed
(`smul_units_algebraMap`), injective, and its image consists of `n`-th roots of unity.  Pushing
the symbol along it:

```lean
noncomputable def kummerSymbolUnits : kˣ →* kˣ →* SmoothH2 Gal(Ω/k) Ωˣ :=
  ...(coeffH2 h.unitsHom h.unitsHom_equivariant).comp (kummerSymbol h Φ a)
theorem kummerSymbolUnits_eq_one_iff (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ n = y) (a b : kˣ) :
    kummerSymbolUnits h Φ a b = 1 ↔ kummerSymbol h Φ a b = 1
```

The `iff` is §0.48's `coeffH2_injective`: over an extension closed under `n`-th roots, nothing is
lost by reading the symbol in `H²(Gal(Ω/k), Ωˣ)`.  Composed with §0.46's `smoothBrauerEquiv` this
is a symbol with values in `Br(k)[n]`, and over a local field §0.47's
`smoothLocalInvariantEquiv` turns it into a number in `(1/n)ℤ/ℤ ⊆ ℚ/ℤ`.

### What is still missing for row 6

The *product formula* `∏_v (a,b)_v = 0`.  That is global reciprocity — the statement that the sum
of the local invariants of a global Brauer class vanishes — and it needs the exact sequence
`0 → Br(k) → ⊕_v Br(k_v) → ℚ/ℤ → 0`, of which only the injectivity on the left (row 3's
`eq_one_of_mem_sha2`, in the roots-of-unity form) is currently available.  The symbol as built is
already enough for the *local* Scholz–Reichardt bookkeeping, which is where it is wanted.

Build: 9461 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.50 Status (2026-08-31, late night) — the norm residue symbol of a local field

`CFT/Brauer/LocalSymbol.lean` closes the local half of row 6.  Over a local field `K` (perfect,
complete, discretely valued, locally compact) containing a primitive `n`-th root of unity `ζ`, the
composite

```
Kˣ × Kˣ  —kummerSymbol→  H²(G_K, μ_n)  —coeffH2→  H²(G_K, K̄ˣ)  —smoothBrauer→  Br(K)  —inv→  ℚ/ℤ
```

is packaged as

```lean
noncomputable def localSymbol (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) : Kˣ →* Kˣ →* Multiplicative QModZ
```

together with `pow_localSymbol_eq_one` (values in the `n`-torsion), and
`localSymbol_eq_one_of_isPow_left` / `_right`.  The general form `localKummerSymbol` takes arbitrary
Kummer data and an arbitrary pairing; `localSymbol` instantiates it at `Multiplicative (ZMod n)`
with `mulZMod n`, which is where §0.49 put the choice of primitive root.

Two small things make the assembly clean:

* `MonoidHom.compHom` post-composes a *bilinear* gadget in one step — `localKummerSymbol` is just
  `(MonoidHom.compHom inv).comp (kummerSymbolUnits h Φ)`, so bimultiplicativity is inherited rather
  than re-proved.
* `exists_units_pow_eq_self`: over an algebraically closed field every unit is an `n`-th power.
  This discharges the hypothesis of §0.49's `kummerSymbolUnits_eq_one_iff` outright, so

  ```lean
  theorem localKummerSymbol_eq_one_iff … :
      localKummerSymbol hres hm h Φ a b = 1 ↔ kummerSymbol h Φ a b = 1
  ```

  holds with no side condition: **the invariant sees the whole symbol.**

### What row 6 still lacks, and why it is not a local question

The product formula `∑_v inv_v (a,b)_v = 0` is *not* a statement about the symbol; it is the
statement that the sum of the local invariants of a global Brauer class vanishes.  Formally that is
the middle of

```
0 → Br(k) → ⊕_v Br(k_v) → ℚ/ℤ → 0,
```

whose left exactness is row 3 (`eq_one_of_mem_sha2`).  The repo's global class formation
(`Units/GlobalTate.lean`) produces `globalFundamentalClass` by a *choice* — the existence of a
class annihilated by exactly the multiples of the degree — which is enough for Tate's theorem but
does **not** pin the invariant map down as the sum of local invariants.  Getting the product
formula therefore means building the invariant map of the global class formation from the local
ones, which needs:

* the decomposition subgroup `D_v ≤ G_k` identified with `G_{k_v}` as a topological group, with
  `Ω` becoming `k̄_v` as a `D_v`-module (the repo has `decompositionSubgroups`
  (`Units/InfiniteDecomposition.lean`) and the completions, but not yet the identification at the
  level of absolute Galois groups);
* the localization `H²(G_k, Ωˣ) → H²(D_v, Ωˣ) ≅ Br(k_v)` for each `v`, and the fact that all but
  finitely many components vanish;
* exactness of `H²(G, K̄ˣ) → H²(G, I) → H²(G, C)` from `Units/IdeleClassSES.lean`, plus Shapiro to
  read `H²(G, I)` as `⊕_v Br(k_v)`.

That is the next large project on the critical path, and it is shared with row 8: Poitou–Tate needs
the same localization maps.

Build: 9462 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.51 Status (2026-08-31, late night) — the localization of the Brauer group at a finite place

`CFT/Brauer/PlaceInvariant.lean` lays the first brick of the project named at the end of §0.50 —
and it turns out that the hardest-looking prerequisite listed there is **not needed at all**.

### (a) The localization map does not need the decomposition group

§0.50 planned the localization `H²(G_k, Ωˣ) → H²(D_v, Ωˣ) ≅ Br(k_v)` and observed that it requires
identifying the decomposition subgroup `D_v ≤ G_k` with `G_{k_v}` as a topological group, with `Ω`
becoming `k̄_v` as a `D_v`-module.  That is a genuine piece of work (a normal-closure/compositum
argument plus continuity of the comparison map) and it has *not* been done.

It does not have to be.  The same map is available purely algebraically:

```
Br(k)  —baseChangeHom k_v→  Br(k_v)  —localInvariantHom→  ℚ/ℤ
```

`BrauerGroup.baseChangeHom` (`Brauer/BaseChange.lean`) sends `⟦A⟧` to `⟦k_v ⊗_k A⟧` with no Galois
theory whatsoever, and `localInvariantHom` (`Brauer/InvariantMap.lean`) is the invariant map of
local class field theory.  Composing them is

```lean
noncomputable def placeInvariant (v : HeightOneSpectrum (𝓞 k)) :
    BrauerGroup.{0, 0} k →* Multiplicative QModZ
```

and, because `smoothBrauerEquiv` identifies `Br` of a perfect field with `SmoothH2` of its absolute
Galois group, the cohomological form `smoothPlaceInvariant` is a one-line transport.  The
comparison of Galois groups is thereby *replaced* by the comparison of Brauer groups, which is a
tensor product.

### (b) The completion is a local field in the sense the repo already uses

Every hypothesis of the local invariant map is discharged for `v.adicCompletion k`:

| hypothesis | source |
| --- | --- |
| `Valued _ ℤᵐ⁰`, `CompleteSpace` | Mathlib |
| `Valuation.RankOne` | `NumberField.instRankOneValuedAdicCompletion` — but only with `synthInstance.maxHeartbeats 1000000`; at the default it times out |
| `ProperSpace` | `Local.properSpace_adicCompletion` (`Local/AdicLocalField.lean`) |
| `PerfectField` | new instance `charZero_adicCompletion` + `PerfectField.ofCharZero` |
| `IsUnitValGen _ 1` | `isUnitValGen_one (valued_adicCompletion_surjective v)` — the canonical normalization, so `placeInvariant` carries no `hm` argument |
| `HasResidueChar _ p e` | `exists_hasResidueChar_adicCompletion` (`Local/AdicHerbrand.lean`) — available for *every* place, so it can be produced inside a proof rather than carried as a hypothesis |

The last row is what makes the main result unconditional:

```lean
theorem placeInvariant_eq_one_iff (v) (x) :
    placeInvariant k v x = 1 ↔ x ∈ BrauerGroup.relative k (v.adicCompletion k)
```

**a Brauer class of a number field has trivial invariant at a place exactly when the completion
there splits it.**  Injectivity of the local invariant map (`localInvariantHom_injective`) is the
whole content of the forward direction.

### (c) Base change of the smooth second cohomology, functorially

The same transport gives, for perfect fields,

```lean
noncomputable def smoothBaseChange (k K : Type u) … :
    SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ →*
      SmoothH2 Gal(AlgebraicClosure K/K) (AlgebraicClosure K)ˣ
```

with `smoothBaseChange_self` and `smoothBaseChange_comp` inherited from `baseChangeHom_self` and
`baseChangeHom_comp`.  This is the coefficient-and-group change that a direct construction would
have had to build by hand out of `comapH2` and `coeffH2`, complete with an `IsSmoothHom` proof.

### (d) What the product formula still needs

With the localizations in place, the sequence

```
0 → Br(k) → ⊕_v Br(k_v) → ℚ/ℤ → 0
```

decomposes into three independent statements, all now expressible without any profinite plumbing:

1. **Injectivity** (Albert–Brauer–Hasse–Noether): `(∀ v, placeInvariant k v x = 1) → x = 1`.  The
   repo has the finite-level cocycle form, `exists_sub_add_eq_globalUnits` (`Units/ABHN.lean`), and
   `H2Surjective.lean` identifies `Br(K/k)` with `H²(Gal(K/k), Kˣ)`.  The bridge that is missing is
   the compatibility of *algebraic* base change `k_v ⊗_k −` with *cohomological* restriction to the
   decomposition subgroup: `k_v ⊗_k (K/k, a)` is the crossed product `(K_w/k_v, res a)`.
2. **Almost-all vanishing**: for a fixed `x`, `placeInvariant k v x = 1` for all but finitely many
   `v`.  Classically, a splitting field `K/k` is unramified outside a finite set and the values of
   a cocycle are units outside a finite set, and `H²` of the units of an unramified local extension
   vanishes — the last of which the repo has (`Local/UnramifiedCoboundary.lean`,
   `subsingleton_tate_adicUnits`).
3. **The sum vanishes**.  This is the deep one and is the reciprocity law.

Items 1 and 2 need the same bridge, and it is a bounded, purely algebraic project; item 3 is not.

The archimedean places are not yet covered: `Brauer/RealInvariant.lean` has
`realBrauerInvariant : Br(ℝ) →* ℚ/ℤ`, so the missing step is only to turn a real embedding of `k`
into an `Algebra k ℝ` and base change along it.

Build: 9463 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.52 Status (2026-08-31, late night) — the bridge of §0.51(d)1 is built: base change of a crossed product to a completion

The missing compatibility named at the end of §0.51(d)1 — *"`k_v ⊗_k (K/k, a)` is the crossed
product `(K_w/k_v, res a)`"* — is now a theorem, in `CFT/Brauer/PlaceCrossedProduct.lean`, resting
on a new brick `CFT/Units/DecompositionField.lean`.

### (a) The decomposition field, and the tower that was *not* needed

The plan of record was to go through the completion `F_u` of the decomposition field
`F = K^{D_w}` and to compare degrees along `k_v → F_u → K_w`.  That is painful in Lean, because
`primeUnder (𝓞 k) (primeUnder (𝓞 F) w) = primeUnder (𝓞 k) w` holds only propositionally and the
repo has to transport along it with the `ringCast` machinery of `Units/PlaceTower.lean`.

None of it is necessary.  `Units/CompletionGalois.lean` already proves

```lean
mem_range_algebraMap_iff_forall_stabilizer_smul_eq :
    z ∈ Set.range (algebraMap (primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K))
      ↔ ∀ σ : ↥(stabilizer Gal(K/k) w), σ • z = z
```

so an element of `F` — fixed by the decomposition group by definition — lands in the image of
`k_v` the moment it is pushed into `K_w`.  That gives a ring homomorphism directly,

```lean
noncomputable def decompositionFieldHom : ↥(decompositionField k w) →+* (primeUnder (𝓞 k) w).adicCompletion k
```

built as `(rangeEquivBaseCompletion k w).symm ∘ codRestrict (toAdicCompletion w ∘ algebraMap …)`,
together with `algebraMap_decompositionFieldHom` saying the triangle into `K_w` commutes.  From it
come the `Algebra ↥F k_v` instance and both scalar towers (`k → F → k_v` and `F → k_v → K_w`).
`F_u`, `ringCast` and the degree count are all off the critical path.

### (b) The Galois groups

`Units/DecompositionGalois.lean` has `decompositionEquiv k w : ↥(stabilizer Gal(K/k) w) ≃* Gal(K_w/k_v)`,
and `IntermediateField.subgroupEquivAlgEquiv` has `↥(stabilizer Gal(K/k) w) ≃* Gal(K/F)`.  Composing,

```lean
noncomputable def localDecompositionEquiv : Gal(K_w/k_v) ≃* Gal(K/↥(decompositionField k w))
```

with the compatibility `algebraMap_localDecompositionEquiv` — `τ` and `localDecompositionEquiv k w τ`
agree on the image of `K` — which is exactly the hypothesis shape `he` of
`CrossedProduct.baseChangeHom_mk_csa_compositum`.

### (c) The bridge, in two steps

`Brauer/CrossedProductRestrict.lean` computes base change from `k` to an intermediate field, and
`Brauer/CrossedProductCompositum.lean` computes base change along a field over which the Galois
group is unchanged.  `F` is precisely the field where the second applies, so the composite

```
Br(k) —base change→ Br(F) —base change→ Br(k_v)
```

evaluated on `⟦(K/k, f)⟧` is the class of the crossed product of

```lean
noncomputable def localCocycle (f : Gal(K/k) × Gal(K/k) → Kˣ) :
    Gal(K_w/k_v) × Gal(K_w/k_v) → (w.adicCompletion K)ˣ :=
  CrossedProduct.compositumCocycle (localDecompositionEquiv k w)
    (CrossedProduct.restrictCocycle ↥(decompositionField k w) f)
```

(`baseChangeHom_mk_csa_adicCompletion`, via `BrauerGroup.baseChangeHom_comp`), and with
`Brauer/Kernel.lean`'s `mk_csa_eq_one_iff` this gives the payoff

```lean
theorem placeInvariant_mk_csa_eq_one_iff (hf : IsMulCocycle₂ f) :
    placeInvariant k (primeUnder (𝓞 k) w) (⟦CrossedProduct.csa hf⟧ : BrauerGroup k) = 1
      ↔ IsMulCoboundary₂ (localCocycle k w f)
```

**the invariant at a finite place of a crossed-product class vanishes exactly when the local
cocycle is a coboundary.**  That is the hypothesis `hfin` of `exists_sub_add_eq_globalUnits`
(`Units/ABHN.lean`) up to the notational dictionary between `IsMulCoboundary₂` and the
`Additive`/`smulUnitsAut`/`adicUnitHom` spelling, which is the next brick.

### (d) What §0.51(d)1 still needs after this

1. the notational dictionary just named (mechanical);
2. the archimedean analogue: `w.Completion` in place of `w.adicCompletion K`, an infinite-place
   decomposition field, and `Br(ℝ)` in place of `Br(k_v)` — `Brauer/RealInvariant.lean` supplies
   the invariant, the decomposition-field construction transcribes;
3. surjectivity of `H²(Gal(K/k), Kˣ) → Br(K/k)` for a *variable* splitting field, so that an
   arbitrary class of `Br(k)` is a crossed product — `H2Surjective.lean` has the finite-level
   statement.

Lean notes: two instance traps.  A module-level `set_option synthInstance.maxHeartbeats 1000000`
is mandatory once `Algebra ↥(IntermediateField …) (… adicCompletion …)` is in scope — the default
20000 cannot even find `SMul ↥F k_v`, and the failure surfaces as a bogus goal rather than an
error.  And `IsGalois k_v K_w` is needed to *state* `localCocycle`, so the in-proof
`haveI := isGalois_adicCompletion k w` is too late; it must be
`attribute [local instance] isGalois_adicCompletion` before the `variable` block.

Build: 9466 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.53 Status (2026-08-31, late night) — the Albert–Brauer–Hasse–Noether theorem, on the Brauer group

Item 1 of §0.51(d) is **done**.

```lean
theorem eq_one_of_forall_mem_relative (x : BrauerGroup k)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 k), x ∈ BrauerGroup.relative k (v.adicCompletion k))
    (hinf : ∀ u : InfinitePlace k, x ∈ BrauerGroup.relative k u.Completion) :
    x = 1
```

**a Brauer class over a number field which is split by every completion is trivial**
(`Brauer/HasseNoether.lean`), together with the invariant-map phrasing
`eq_one_of_forall_placeInvariant_eq_one` and the packaged

```lean
theorem brauerToCompletions_injective : Function.Injective (brauerToCompletions k)
```

into `(∏_v Br(k_v)) × (∏_u Br(k_u))`.  Unconditional, sorry-free, axiom-free.

### (a) The three §0.52(d) items, and where each landed

1. **The notational dictionary** — `Brauer/PlaceCoboundary.lean`.  The two identifications of the
   decomposition group agree (`localDecompositionEquiv_decompositionEquiv`), so transporting
   `IsMulCoboundary₂ (localCocycle k w f)` along `decompositionEquiv` and unwinding
   `Additive`/`smulUnitsAut`/`adicUnitHom` gives
   `placeInvariant_mk_csa_eq_one_iff_exists` and its `relative`-phrased twin
   `mem_relative_mk_csa_adicCompletion_iff_exists`, which are *literally* the `hfin` clause of
   `exists_sub_add_eq_globalUnits`.
2. **The archimedean analogue** — `Units/InfiniteDecompositionField.lean` +
   `Brauer/InfinitePlaceCrossedProduct.lean`.  This turned out to be a transcription rather than a
   new construction: the whole infinite-place infrastructure already existed in parallel
   (`mem_range_algebraMap_iff_forall_stabilizer_smul_eq_infinite`, `isGalois_infiniteCompletion`,
   `finiteDimensional_infiniteCompletion`, and crucially `stabilizerAlgEquivInfinite`, the infinite
   analogue of `decompositionEquiv`), so only the decomposition-field embedding and the two-step
   base change had to be written.  `Br(ℝ)` is *not* used: the statement is
   `x ∈ BrauerGroup.relative k u.Completion`, which needs no invariant map at all.
3. **Surjectivity for a variable splitting field** — already in the repo.
   `exists_mk_csa_eq_of_mem_relative` (`Brauer/SmoothBrauer.lean`) plus
   `exists_isGalois_mem_relative` (`Brauer/GaloisSplitting.lean`, applicable because a number field
   is perfect) writes an arbitrary class of `Br(k)` as `⟦CrossedProduct.csa hf⟧` for a cocycle of
   some finite Galois extension of number fields.

### (b) The assembly

Given `x : Br(k)`, pick the Galois splitting field `L` (a number field by
`NumberField.of_module_finite`) and write `x = ⟦csa hf⟧`.  Then:

* `hfin` at a prime `v` of `𝓞 L` is the hypothesis at `primeUnder (𝓞 k) v`;
* `hinf` at an infinite place `w` of `L` is the hypothesis at `w.comap (algebraMap k ↥L)`;
* the cocycle identity `IsMulCocycle₂ f` *is* the additive cocycle identity `ha`, via the one-line
  dictionary `Additive.toMul (globalUnitsAut σ u) = σ • Additive.toMul u`, proved by `Units.ext rfl`;
* `exists_sub_add_eq_globalUnits` then returns a cochain, which is exactly a witness of
  `IsMulCoboundary₂ f`, and `CrossedProduct.mk_csa_eq_one_iff` concludes.

So the global input is *only* `Units/ABHN.lean`; everything else is the crossed-product dictionary.

### (c) What is left of the product formula

Of the three items of §0.51(d), **item 1 is closed**.  Remaining:

2. **almost-all vanishing** of `placeInvariant k v x` — a splitting field is unramified outside a
   finite set and `H²` of the units of an unramified local extension vanishes
   (`Local/UnramifiedCoboundary.lean`, `subsingleton_tate_adicUnits`);
3. **the sum vanishes** — the reciprocity law, still the deep one.

Lean notes.  `MonoidHom.pi` does not exist in Mathlib; the product of monoid homomorphisms into a
dependent product is `Pi.monoidHom`.  `placeInvariant` takes `k` explicitly but
`placeInvariant_eq_one_iff` takes it implicitly.  And an `@[simp]` lemma whose right-hand side is a
pair of lambdas needs the binder types written out, or the field projections inside them cannot be
elaborated.

Build: 9470 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.54 Status (2026-08-31, late night) — almost all local invariants vanish

Item 2 of §0.51(d) is **done**.

```lean
theorem finite_setOf_not_mem_relative_adicCompletion (x : BrauerGroup k) :
    {v : HeightOneSpectrum (𝓞 k) | x ∉ BrauerGroup.relative k (v.adicCompletion k)}.Finite

theorem finite_setOf_placeInvariant_ne_one (x : BrauerGroup k) :
    {v : HeightOneSpectrum (𝓞 k) | placeInvariant k v x ≠ 1}.Finite
```

(`Brauer/PlaceInvariantFinite.lean`), with the base-change phrasing
`finite_setOf_baseChangeHom_adicCompletion_ne_one` in between.  Unconditional, sorry-free,
axiom-free.  Together with §0.53 this says that `brauerToCompletions` is injective *and* lands in
the restricted product: a Brauer class over a number field is determined by its local invariants,
and only finitely many of them are nontrivial.

### (a) `CFT/Units/ABHNUnitValues.lean` — dropping the torsion hypothesis of `ABHNTorsion`

`Units/ABHNTorsion.lean` proved that at an unramified finite place the local component of a
two-cocycle of the units is a coboundary **provided the cocycle is killed by a nonzero integer**.
Reading that proof, the torsion hypothesis is used for exactly one thing: to know that the values
land in `(unitVal).ker`, the units of the valuation ring, where the second cohomology of the cyclic
decomposition group vanishes (`Local/UnramifiedCoboundary.lean`, `exists_sub_add_eq_adicUnits`).
So the hypothesis can simply be replaced by that conclusion:

```lean
theorem exists_sub_add_eq_adicUnits_of_unitVal (v : HeightOneSpectrum (𝓞 K))
    (hunr : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal)
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (hu : ∀ x y : Gal(K/k), unitVal (Additive.ofMul (adicUnitHom v (a x y).toMul)) = 0)
    (ha : ∀ x y z : Gal(K/k),
      globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y) :
    ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ, …
```

and the hypothesis `hu` is then available for free at almost every place, because it is literally
the statement that the diagonal image of a unit is an idele:

```lean
theorem finite_setOf_unitVal_adicUnitHom_ne_zero (u : Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | unitVal (Additive.ofMul (adicUnitHom v u)) ≠ 0}.Finite
```

which is `fullDiag_mem_idele` (`Units/Idele.lean`) read through `mem_idele` and
`Filter.eventually_cofinite`.  A number field element has nonzero order at only finitely many
primes; nothing further is needed.

### (b) `CFT/Brauer/PlaceInvariantFinite.lean` — the bad set, and pushing it down

Take a class `x` of `Br(k)`.  By `exists_isGalois_mem_relative` and
`exists_mk_csa_eq_of_mem_relative` it is `⟦CrossedProduct.csa hf⟧` for a two-cocycle
`f : Gal(L|k) × Gal(L|k) → Lˣ` of a finite Galois extension of number fields.  Upstairs, put

```
Bad = {w : ramified over k} ∪ ⋃_{(σ,τ)} {w : unitVal (adicUnitHom w (f (σ,τ))) ≠ 0}.
```

The first piece is finite by `finite_setOf_not_isUnramifiedAt` (a ramified place divides the
different ideal, and a nonzero ideal has finitely many prime divisors); the union is over the
**finite** set `Gal(L|k) × Gal(L|k)`, so `Set.finite_iUnion` applies to the finiteness of (a).
Downstairs, every place of `k` has a place of `L` above it (`exists_primeUnder_eq`), so the set of
bad places of `k` is contained in `primeUnder (𝓞 k) '' Bad`, which is finite.  And a place of `k`
under a `w ∉ Bad` is good: `exists_sub_add_eq_adicUnits_of_unitVal` produces the local coboundary
and `mem_relative_mk_csa_adicCompletion_iff_exists` (§0.53) turns it into splitting.

The additive form of the cocycle identity for `f` is re-derived inline, as in `HasseNoether.lean`;
the dictionary lemma `toMul_globalUnitsAut` (`Units/ABHNCoboundary.lean`) is what makes it one
`simp only`.

### (c) What is left of the product formula

Of the three items of §0.51(d), **items 1 and 2 are closed**.  What remains is

3. **the sum vanishes**, `∑_v inv_v(x) = 0` — the reciprocity law.

This is not a bookkeeping item: it is the fundamental class of global class field theory, and it is
what upgrades §0.53 + §0.54 to the exact sequence `0 → Br(k) → ⊕_v Br(k_v) → ℚ/ℤ → 0`.  It is also
the input that rows 5 and 8 of the §0.36 table (Poitou–Tate, wall #1) are waiting on: the pairing
`Ш¹(k, A′) × Ш²(k, A) → ℚ/ℤ` is *defined* by a sum of local invariants, and its well-definedness is
exactly the product formula.

Build: 9472 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.55 Status (2026-08-31, late night) — the archimedean invariant, and the full family

Two new modules, `CFT/Brauer/InfiniteInvariant.lean` and `CFT/Brauer/TotalInvariant.lean`.  Together
they close the archimedean gap flagged at the end of §0.51(d) and give the family of local
invariants a single name.

### (a) `CFT/Brauer/InfiniteInvariant.lean` — the invariant at an infinite place

Up to now the archimedean side of the theory was phrased through *real embeddings*:
`realEmbeddingInvariant k` needs an `[Algebra k ℝ]` instance supplied by the caller, and
`realPlaceInvariant k hw` supplies it from a proof that a place is real.  The completions
`u.Completion` never appeared on the invariant side, so `eq_one_of_forall_placeInvariant_eq_one`
still had to take its archimedean hypothesis in the raw form `x ∈ BrauerGroup.relative k u.Completion`.

The two facts that fix this are entirely about the shape of the completion.

```lean
theorem relative_completion_eq_top_of_isComplex {u : InfinitePlace k} (hu : u.IsComplex) :
    BrauerGroup.relative k u.Completion = ⊤

theorem relative_completion_eq_relative_real {u : InfinitePlace k} (hu : u.IsReal) [Algebra k ℝ]
    (halg : (algebraMap k ℝ) = (InfinitePlace.embedding_of_isReal hu : k →+* ℝ)) :
    BrauerGroup.relative k u.Completion = BrauerGroup.relative k ℝ
```

Mathlib already has the two ring isomorphisms `ringEquivComplexOfIsComplex` and
`ringEquivRealOfIsReal`, and the compatibility with the base is `extensionEmbedding_coe` /
`extensionEmbeddingOfIsReal_coe`.  What is worth recording is the mechanical part: **turn the ring
isomorphism into an `AlgEquiv` with `AlgEquiv.ofRingEquiv`, not with a structure-update `{ e.symm
with commutes' := … }`**.  The structure-update route builds an `AlgHom` whose application unfolds
to `(↑↑e.symm.toRingHom).toFun x`, and `rw [RingEquiv.apply_symm_apply]` then fails to match; with
`AlgEquiv.ofRingEquiv hmap` the same proof is two `relative_le_relative_of_algHom` calls on
`e.toAlgHom` and `e.symm.toAlgHom`, and the compatibility hypothesis `hmap` is exactly what
`ofRingEquiv` asks for.  A pleasant surprise: `algebraMap k u.Completion r` is *definitionally* the
coercion `↑r`, so `hmap` is `extensionEmbedding_coe` applied verbatim, with no glue.

For the complex case, `relative k ℂ = ⊤` is `BrauerGroup.relative_eq_top_of_isAlgClosed`, and the
`Algebra k ℂ` instance needed to state it is a `letI` from `u.embedding`; the conclusion is about
`u.Completion` only, so the instance never escapes.

The invariant itself is then a `dite` on `u.IsReal`:

```lean
noncomputable def infinitePlaceInvariant (u : InfinitePlace k) :
    BrauerGroup.{0, 0} k →* Multiplicative QModZ :=
  if hu : u.IsReal then realPlaceInvariant k hu else 1

theorem infinitePlaceInvariant_eq_one_iff (u : InfinitePlace k) (x : BrauerGroup.{0, 0} k) :
    infinitePlaceInvariant k u x = 1 ↔ x ∈ BrauerGroup.relative k u.Completion
```

Note that none of these need `[NumberField k]`: `InfinitePlace`, its completion and
`realPlaceInvariant` are all defined for a bare field, so the linter's `omit [NumberField k] in` is
correct and not a warning to be silenced.

### (b) `CFT/Brauer/TotalInvariant.lean` — the family, and its sum

```lean
noncomputable def localInvariants :
    BrauerGroup.{0, 0} k →*
      ((HeightOneSpectrum (𝓞 k) → Multiplicative QModZ) ×
        (InfinitePlace k → Multiplicative QModZ))

theorem localInvariants_injective : Function.Injective (localInvariants k)
```

which is the Albert–Brauer–Hasse–Noether theorem in its final form: **a Brauer class over a number
field is determined by its family of local invariants.**  The archimedean hypothesis of
`eq_one_of_forall_placeInvariant_eq_one` is now discharged by (a), so the intermediate statement

```lean
theorem eq_one_of_forall_invariant_eq_one (x : BrauerGroup.{0, 0} k)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x = 1)
    (hinf : ∀ u : InfinitePlace k, infinitePlaceInvariant k u x = 1) :
    x = 1
```

mentions no relative Brauer groups at all.

The sum over all places is a `MonoidHom` because of §0.54:

```lean
noncomputable def totalInvariant : BrauerGroup.{0, 0} k →* Multiplicative QModZ where
  toFun x := (∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x) *
    ∏ u : InfinitePlace k, infinitePlaceInvariant k u x
```

`map_mul'` is `finprod_mul_distrib` fed with `finite_setOf_placeInvariant_ne_one` twice — the
`Function.mulSupport` of `fun v => placeInvariant k v x` *is* the set of §0.54 on the nose, so no
conversion lemma is needed — followed by `Finset.prod_mul_distrib` (the infinite places are a
`Fintype`) and `mul_mul_mul_comm`.

### (c) What is left

Reciprocity is now a one-line statement in the repository's own vocabulary:

```
totalInvariant k = 1.
```

That is item 3 of §0.51(d), unchanged, and still the input rows 5, 6 and 8 of the §0.36 table are
waiting on.  What §0.55 adds is that everything *around* it is now phrased in invariants: the exact
sequence to aim for is

```
0 → Br(k) --localInvariants--> ⊕_v ℚ/ℤ --sum--> ℚ/ℤ → 0,
```

whose left exactness is `localInvariants_injective` (done), whose "almost all vanish" is §0.54
(done), and whose middle exactness is reciprocity plus a surjectivity statement.

Also worth recording, from the survey done while choosing this brick: **row 4 of the §0.36 table is
stale.**  Its stated remainder, `inv_M ∘ res = [M : K] · inv_K`, is already a theorem —
`localInvariantHom_baseChange` in `CFT/Brauer/InvariantBaseChange.lean`.  Local class field theory
in this repository is complete (`localInvariantEquiv`, `localInvariantHom_injective`,
`localInvariantHom_baseChange`), and so is the idele class formation on the global side
(`first_inequality`, `globalFundamentalClass`, `globalTateEquiv`, `globalReciprocityEquiv`,
`H¹(G, C_K) = 0`, `H²(G, K*) ↪ H²(G, I_K)`).  The reciprocity law is genuinely the one missing
global input, not a bookkeeping gap.

One shortcut was considered and **refuted**: one cannot get reciprocity by comparing indices, on the
grounds that the image of `H²(G, I_K)` in `H²(G, C_K)` and the kernel of the sum have the same
index.  The image is generated by `1 / lcm_v(n_v)`, not by `1 / n`, and these differ already for a
biquadratic extension.

Build: 9474 jobs green, zero warnings, zero sorries outside the comparator; axioms of
`localInvariants_injective` and `totalInvariant` are `[propext, Classical.choice, Quot.sound]`.

---

## 0.56 Status (2026-08-31) — the norm residue symbol of a cyclic local extension, and the shape of reciprocity

### (a) `CFT/Brauer/CyclicNormResidue.lean`

Two bricks that were already in the tree turn out to fit together with nothing in between:

* `cyclicBrauerEquiv` (`CFT/Brauer/CyclicNorm.lean`) — for *any* finite cyclic Galois `L/K` of
  *any* fields, `Kˣ / N(Lˣ) ≃* Br(L/K)`, together with `exists_cyclicBrauerHom_eq` (surjectivity)
  and `ker_cyclicBrauerHom`.  No local hypotheses at all.
* `index_normSubgroup_eq_finrank_local` (`CFT/Local/CyclicNormIndex.lean`) — the norm index of a
  cyclic extension of a local field is the degree, **ramified or not**.

Transporting the second along the first is immediate and gives the two structural facts:

```lean
theorem natCard_relative_eq_finrank_of_cyclic … :
    Nat.card ↥(BrauerGroup.relative K L) = finrank K L
theorem relative_eq_brauerTorsion_of_cyclic … :
    BrauerGroup.relative K L = brauerTorsion K (finrank K L)
```

The second is `Subgroup.eq_of_le_of_card_ge` fed with `relative_le_brauerTorsion` and
`natCard_brauerTorsion`.  It is the *general* form of `relative_eq_brauerTorsion_of_unramified`
(`CFT/Brauer/RelativeTorsion.lean`): **a cyclic extension of a local field splits exactly the
classes killed by its degree**, with no unramifiedness hypothesis and no Frobenius.

The symbol itself is the composite of the two maps that are now available:

```lean
noncomputable def cyclicNormResidue (hm : IsUnitValGen K m) : Kˣ →* Multiplicative QModZ :=
  (localInvariantHom K hm).comp (cyclicBrauerHom hsigma)
```

with `ker_cyclicNormResidue = normSubgroup K L` (injectivity of `localInvariantHom` turns the
kernel of the cyclic algebra map into the kernel of the symbol), the user-facing
`cyclicNormResidue_eq_one_iff` (*a unit has trivial symbol exactly when it is a norm*),
`pow_cyclicNormResidue_eq_one`, and

```lean
theorem exists_cyclicNormResidue_eq … :
    ∃ a : Kˣ, cyclicNormResidue hsigma hm a
      = Multiplicative.ofAdd (QuotientAddGroup.mk (1 / (finrank K L : ℚ)) : QModZ)
```

so the symbol is onto `(1/n)ℤ/ℤ`.  Together: `Kˣ / N(Lˣ) ≅ (1/n)ℤ/ℤ ≅ ℤ/n ≅ Gal(L/K)`, which is
local class field theory for cyclic extensions in the concrete form the global argument consumes.
`a ↦ σ₀ ^ (n · inv(L/K, σ₀, a))` is the local Artin map, and it is now one definition away.

Build: 9475 jobs green, zero warnings, zero sorries outside the comparator; all seven new
declarations have axioms `[propext, Classical.choice, Quot.sound]`.

### (b) The obstruction named in §0.55 was the wrong one

§0.55 left reciprocity as `totalInvariant k = 1` and the next brick as the *global splitting
criterion*

> `x ∈ Br(L/k)` ⟺ for every place `v`, `placeInvariant k v x ^ n_v = 1`, `n_v` the local degree.

The apparent obstruction was `localInvariantHom_baseChange`, whose hypothesis
`hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖` genuinely fails for a tower of adic completions:
`valued_adicCompletionComap` gives `v(comap z) = v(z) ^ e` and `normValued K L` restricts to
`v_K ^ n`, so neither normalization is an isometry.

That lemma is **not needed**.  `relative_eq_brauerTorsion_of_cyclic` is *intrinsic* — it is a
statement about the subgroup `Br(L_w / k_v) ≤ Br(k_v)`, not about comparing two invariant maps —
so the criterion factors as

```
x_v ∈ Br(L_w / k_v)  ⟺  x_v ∈ brauerTorsion k_v n_v  ⟺  inv_v(x) ^ n_v = 1,
```

the middle step being (a) and the right step `localInvariantHom_injective`.  The reverse direction
of the criterion is then ABHN over `L` (`eq_one_of_forall_invariant_eq_one`) plus
`BrauerGroup.baseChangeHom_comp`, since `(x_L)_w` and `(x_v)_{L_w}` are the same base change of `x`
read two ways.

### (c) The completion tower `k_v ⊆ L_w` is already built

The plumbing that (b) consumes turned out to be in the tree already, from the ABHN work:

| ingredient | source |
| --- | --- |
| `Algebra (v.adicCompletion k) (w.adicCompletion L)` | `instAlgebraAdicCompletion` (`CFT/Units/CompletionFinite.lean`), from the ring map `adicCompletionComap` |
| `IsScalarTower k (v.adicCompletion k) (w.adicCompletion L)` | `instIsScalarTowerBaseAdicCompletion` (`CFT/Units/CompletionGalois.lean`) |
| `FiniteDimensional (v.adicCompletion k) (w.adicCompletion L)` | `finiteDimensional_adicCompletion` — an **instance** |
| `IsGalois (v.adicCompletion k) (w.adicCompletion L)` | `isGalois_adicCompletion` — a theorem, so `attribute [local instance]` |
| the Galois group is the decomposition group | `restrictToBase`, `adicCompletionAut_restrictToBase`, `mem_range_algebraMap_iff_forall_stabilizer_smul_eq` |

So the only genuinely new step is `IsCyclic (L_w ≃ₐ[k_v] L_w)` for cyclic `L/k`, which is
`restrictToBase` packaged as an injective group homomorphism into `Gal(L/k)`.

That makes the splitting criterion a three-step chain, each step short:

1. **Hasse principle for relative Brauer groups.**  `x ∈ Br(L/k)` iff every completion of `L`,
   finite or infinite, splits `x`.  Forwards is monotonicity of `relative`; backwards is ABHN over
   `L` (`eq_one_of_forall_invariant_eq_one`) together with `BrauerGroup.baseChangeHom_comp`, since
   `(x_L)_w` and `x_{L_w}` are the same base change read two ways.
2. **Descend the local condition to `k_v`.**  `x ∈ Br(L_w / k)` iff `x_{k_v} ∈ Br(L_w / k_v)`, again
   just `baseChangeHom_comp` along `k → k_v → L_w`.
3. **Read it off as an invariant**, by (a): `Br(L_w / k_v) = brauerTorsion k_v [L_w : k_v]`, and
   membership in the latter is `placeInvariant k v x ^ [L_w : k_v] = 1` by injectivity of
   `localInvariantHom`.

### (d) Reciprocity itself, costed

With (c) in hand the two remaining routes are both explicit computations, not soft arguments:

* **Cyclotomic.** Every class of `Br(ℚ)` is split by a cyclic subfield of some `ℚ(ζ_m)`; the sum
  formula becomes the product formula for the local Artin symbols of `ℚ(ζ_m)/ℚ`.  At `p ∤ m` the
  extension is unramified and `localInvariant_apply_cyclicBrauerHom` already gives `v(a)/n`; at
  `p ∣ m` it is wildly ramified and needs the explicit local Artin map of `ℚ_p(ζ_{p^k})/ℚ_p`, i.e.
  Lubin–Tate.  That last piece is the expensive one.
* **One auxiliary tame prime.**  Split off a single auxiliary prime `q` and a cyclic
  `L ⊆ ℚ(ζ_q)` of degree `N ∣ q − 1`, so that the only ramified place is *tame*.  The tame symbol
  reduces to the unramified formula by bilinearity together with `⟨−a, a⟩ = 1` (which holds because
  `N_{K(a^{1/N})/K}(a^{1/N}) = (−1)^{N−1} a`) and the fact that the Kummer extension of a unit is
  unramified.  The local tame norm groups are then computable from
  `index_normSubgroup_eq_finrank_local`, `Φ_q(1) = q = N(1 − ζ_q)`, "a subgroup of index prime to
  `q` contains `1 + qℤ_q`", and uniqueness of the index-`N` subgroup of a cyclic group.
  **Caveat, established while costing this:** knowing the *kernels* of the local symbols does not
  pin the symbols themselves, so one genuine ramified (tame) computation survives, and routing it
  through the bilinear `kummerSymbol` of `CFT/Profinite/Symbol.lean` needs the **cup product ↔
  cyclic algebra bridge**, which is still on the deferred list.

The second route avoids Lubin–Tate entirely and is the one to take; its enabling lemma is that
bridge, and its prerequisite is the chain of (c).

---

## 0.57 Status (2026-08-31) — the chain of §0.56(c) is built: when a cyclic extension of number fields splits a Brauer class

The three-step chain named in §0.56(c) is now three files, all sorry- and axiom-free.

### (a) `CFT/Units/CompletionCyclic.lean` — the decomposition group is a subgroup

The local input of §0.56(a) is a statement about a *cyclic* extension of a local field, so applying
it at a place of a global cyclic extension needs the completion `L_w / k_v` to be cyclic.  It is,
for the cheapest possible reason: restriction

```
Gal(L_w | k_v) → Gal(L | k)
```

is **injective** (`restrictToBase_injective`), because an automorphism of `L_w` over `k_v` is
continuous (`continuous_algEquiv`, already in `Units/CompletionGalois.lean`) and `L` is dense in
`L_w`, so its values on `L` determine it.  Packaged as a group homomorphism `restrictToBaseHom`
(the `map_one'`/`map_mul'` proofs are `FaithfulSMul.algebraMap_injective` plus
`toAdicCompletion_restrictToBase`), Mathlib's `isCyclic_of_injective` then gives

```
isCyclic_algEquiv_adicCompletion : IsCyclic Gal(L | k) → IsCyclic Gal(L_w | k_v).
```

No decomposition-group theory, no `e·f·g`, no surjectivity: only injectivity is needed, and only
subgroup-heredity of cyclicity is used.

### (b) `CFT/Brauer/RelativeHasse.lean` — the Hasse principle for a fixed extension

`Brauer/HasseNoether.lean` and `Brauer/TotalInvariant.lean` state Albert–Brauer–Hasse–Noether for a
fixed *class*: a class of `Br(L)` which is locally trivial everywhere is trivial.  What the
splitting criterion needs is the same theorem read for a fixed *extension*:

```
mem_relative_iff_forall_completion :
  x ∈ Br(L | k) ↔ (∀ w finite, x ∈ Br(L_w | k)) ∧ (∀ U real, x ∈ Br(L_U | k)).
```

The forward direction is `BrauerGroup.relative_le_relative` twice.  The reverse direction applies
ABHN over `L` to `base_L(x)` and, at each place, rewrites
`base_{L_w}(base_L(x)) = base_{L_w}(x)` with `BrauerGroup.baseChangeHom_comp` — the *only* content
is that functoriality of base change lets the same class be read either way.

The complex places drop out: `relative_completion_eq_top_of_isComplex_extension` transports
`BrauerGroup.relative_eq_top_of_isAlgClosed ℂ` along `AlgEquiv.ofRingEquiv` applied to
`InfinitePlace.Completion.ringEquivComplexOfIsComplex`, whose compatibility with the base is
`extensionEmbedding_coe` after `IsScalarTower.algebraMap_apply k L U.Completion`.  Finally

```
mem_relative_adicCompletion_iff_baseChange :
  x ∈ Br(L_w | k) ↔ base_{k_v}(x) ∈ Br(L_w | k_v),   v = w ∩ k
```

is again `baseChangeHom_comp`, and it is what turns a global condition into a local-field one.

### (c) `CFT/Brauer/RelativeCyclic.lean` — the criterion

Putting (a), (b) and §0.56(a) together:

```
mem_relative_adicCompletion_iff_pow_placeInvariant :
  x ∈ Br(L_w | k)  ↔  inv_v(x) ^ [L_w : k_v] = 0

mem_relative_iff_forall_pow_placeInvariant :
  x ∈ Br(L | k)  ↔  (∀ w, [L_w : k_v] · inv_v(x) = 0) ∧ (∀ U real, x ∈ Br(L_U | k)).
```

Note which hypotheses are *absent*.  There is no unramifiedness assumption; there is no isometry
hypothesis `‖·‖_{k_v} = ‖·‖_{L_w}`, which genuinely fails for an adic tower and is why
`Brauer/LocalReciprocity.lean`'s `relative_eq_brauerTorsion` — the same statement for an arbitrary
finite Galois extension of local fields — cannot be used here; and there is no restriction on the
residue characteristic, since `exists_hasResidueChar_adicCompletion` supplies one for every place.
The cyclic hypothesis is the price paid for dropping the isometry, and it is free for us: the
extensions reciprocity is proven against are cyclic anyway.

### (d) What is left, unchanged

Reciprocity, `totalInvariant k = 1`.  The route is §0.56(d)'s second one, and its remaining
prerequisite is the single deferred item

> **the cup product ↔ cyclic algebra bridge**: for `K ∋ ζ_n`, `b ∈ K^×` and `L = K(b^{1/n})`
> cyclic of degree `n` with `σβ = ζβ`, the class `kummerSymbolUnits a b` of
> `Profinite/Symbol.lean` is the class `cyclicBrauerHom hσ a` of `Brauer/CyclicNorm.lean`.

That bridge is what makes `localSymbol` (`Brauer/LocalSymbol.lean`: already bimultiplicative,
`n`-torsion, trivial on `n`-th powers) *computable*: it identifies its kernel with a norm group, and
from `N_{K(x^{1/n})|K}(x^{1/n}) = (−1)^{n−1} x` one gets `⟨x, −x⟩ = 1`, hence skew-symmetry by the
usual expansion of `⟨ab, −ab⟩ = 1`, hence the tame value at the auxiliary prime from the *unramified*
formula `localInvariant_apply_cyclicBrauerHom` on the other argument.  Without it the symbol is a
pairing whose values are never computed, and reciprocity is a statement about values.

Build: 9478 jobs green, zero warnings, zero sorries outside the comparator; all ten new
declarations have axioms `[propext, Classical.choice, Quot.sound]`.

---

## 3. What is reachable *without* class field theory

This is the section that matters for this repository.

### 3.1 Ikeda's theorem: split embedding problems with abelian kernel over Hilbertian fields

> **Theorem (Ikeda).** *Let k be a Hilbertian field, L/k a finite Galois extension with group G,
> and A a finite abelian group with a G-action. Then the split embedding problem*
> ```
> G_k ↠ G,      1 → A → A ⋊ G → G → 1
> ```
> *has a proper solution: there is a Galois extension F/k containing L with
> Gal(F/k) ≅ A ⋊ G compatibly.*

References:
* M. D. Fried, M. Jarden, *Field Arithmetic*, 3rd ed., Springer 2008, **§16.4 "Split Embedding
  Problems with Abelian Kernels"** (p. 301), Proposition **16.4.5** (numbered 16.4.4 in some
  printings; §16.3, p. 297, is "Regular Realization of Finite Abelian Groups", and §16.4 is built
  directly on it).
* B. H. Matzat, *Einbettungsprobleme über Hilbertkörpern*, in *Konstruktive Galoistheorie*,
  LNM 1284 (1987), 215–268 (Folg. 1, p. 231).
* Malle–Matzat, *Inverse Galois Theory*, Chapter IV.
* Original: M. Ikeda, *Zur Existenz eigentlicher galoisscher Körper beim Einbettungsproblem für
  galoissche Algebren*, Abh. Math. Sem. Univ. Hamburg **24** (1960), 126–131.
* A modern refinement with local conditions: F. Legrand, *On finite embedding problems with
  abelian kernels*, J. Algebra **595** (2022), 633–659, <https://hal.science/hal-03517543>.

**Exactly what the proof needs.** The whole content is the wreath-product reduction:

1. *Group theory.* Let A₀ be A with its group structure but the G-action forgotten, and let
   Ind_1^G(A₀) = A₀^G be the induced module, so that A₀^G ⋊ G = A ≀ G is the **regular wreath
   product**. The augmentation-type map A₀^G → A, (a_g) ↦ ∏_g g·a_g, is G-equivariant and
   surjective, hence **A ⋊ G is a quotient of A ≀ G**, compatibly over G. So it suffices to solve
   the embedding problem for the wreath product; realizability is closed under quotients, which
   this repository has (`IsInverseGalois.quotient`).
2. *A regular abelian realization over the base.* One needs: for a field k (char 0 suffices) and
   a finite abelian A, **a regular Galois extension of k(t) with group A** — Fried–Jarden §16.3.
   This is where "does it need a regular abelian extension of N(T) for a number field N?" is
   answered: **yes, over the base field k, not merely over ℚ**. For the Ikeda step over ℚ with
   L/ℚ of group G, the construction is carried out over ℚ (or over L) and then descended.
3. *Independent variables + linear disjointness.* Take |G| independent variables (t_g)_{g∈G} with
   G permuting them, and in each variable an A-extension; the compositum has group A^G ⋊ G over
   k(t_g : g). Linear disjointness of the |G| conjugate A-extensions is what makes the group come
   out as the full wreath product; it is arranged by the independence of the variables (or,
   equivalently, by specializing to |G| "independent" values).
4. *Hilbert irreducibility over k.* Specialize the (t_g) to elements of k preserving the Galois
   group. **Hilbertianity of k is needed, not merely Hilbertianity of ℚ** — but for the concrete
   application to ℚ, ℚ is the base and ℚ's Hilbertianity is enough. A multivariable Hilbert
   irreducibility statement is required, though it reduces to the one-variable case by the
   standard reduction (Fried–Jarden §12.1 "Hilbert Sets and Reduction Lemmas").

**No class field theory, no Chebotarev, no Dirichlet, no Brauer groups, no Galois cohomology.**

**Sharpness.** "Split" cannot be dropped: over a field of characteristic ≠ 2, k(√a)/k embeds in a
cyclic degree-4 extension iff a is a sum of two squares in k (Serre, *Topics*, Thm 1.2.4 — cited
in this form by Schmidt–Wingberg §1). In particular ℚ(√−1) does not embed in a ℤ/4-extension of ℚ,
so the non-split embedding problem with kernel ℤ/2 over a Hilbertian field is not always solvable.

### 3.2 The wreath-product route and the class it reaches: semiabelian groups

> **Question.** If H is a Galois group over ℚ and A is finite abelian, is A ≀ H a Galois group
> over ℚ? **Yes** — it is the special case of Ikeda's theorem with the induced module as kernel,
> and it needs exactly items 2–4 above.

Iterating Ikeda and closing under quotients gives a precisely-defined class:

> **Definition (Matzat 1987; Dentzer 1995, Def. 2.1).** The class of **semiabelian** finite groups
> is the smallest non-empty class of finite groups that is closed under quotients and under
> semidirect products with finite abelian kernel (i.e. A ⋊ H is semiabelian whenever H is
> semiabelian and A is finite abelian with an H-action).

Equivalent forms and basic facts (see the Wikipedia entry *Semiabelian group* and the references
there; Dentzer, *On geometric embedding problems and semiabelian groups*, manuscripta math. **86**
(1995) 199–216; M. Stoll, *Construction of semiabelian Galois extensions*, Glasgow Math. J. **37**
(1995) 99–104; D. Neftin, *On semiabelian p-groups*, J. Algebra **344** (2011) 60–69):

* **Dentzer's criterion.** A non-trivial finite G is semiabelian iff there are an abelian normal
  subgroup A and a *proper* semiabelian subgroup H with G = A·H.
* Every semiabelian group is solvable; every abelian group is semiabelian.
* Closed under quotients; **not** closed under subgroups.
* Nilpotent groups of class 2 are semiabelian. A solvable group all of whose Sylow subgroups are
  abelian is semiabelian. An abelian extension of a cyclic group is semiabelian.
* Not every solvable group is semiabelian (Dentzer computes a table of small non-semiabelian
  groups). So this route does **not** give Shafarevich's theorem — it gives a large,
  cleanly-axiomatized proper subclass.

> **Theorem (Ikeda + induction).** *Every finite semiabelian group is a Galois group over every
> Hilbertian field of characteristic 0, in particular over ℚ.*

Moreover Dentzer's paper studies which semiabelian groups have **geometric** (= regular over
ℚ(t)) realizations, via *geometric* embedding problems — directly relevant to this repository's
`IsRegularInverseGalois`.

### 3.3 Noether's problem ⇒ regular realization

Wittenberg, *Park City lecture notes: around the inverse Galois problem*, arXiv:2302.13719,
§1.4–§1.6 (<https://arxiv.org/abs/2302.13719>):

* **Problem 1.9 (Noether).** For G ↪ S_n acting on 𝔸_k^n by permuting coordinates, is 𝔸_k^n/G
  rational over k?
* **Remark 2.2.** If k is infinite and perfect, a positive answer to Noether's problem for (k,G)
  implies a positive answer to the *regular* inverse Galois problem for (k,G) (Jouanolou,
  *Théorèmes de Bertini et applications*, Thm 6.3).

What is known for solvable G:
* **Fischer 1915** (Wittenberg Example 1.11): positive for all abelian G of exponent n over any
  field of characteristic ∤ n containing μ_n. Over ℚ this is useless for us, and in any case this
  repository already realizes every finite abelian group regularly over ℚ(T) by other means.
* **Swan 1969 / Voskresenskiĭ**: negative for ℤ/47ℤ over ℚ.
* **Lenstra 1974** (*Rational functions invariant under a finite abelian group*, Invent. Math.
  **25** (1974), 299–325, <https://eudml.org/doc/142292>): a complete criterion for all finite
  abelian G over all fields. Over ℚ, for cyclic groups (Wittenberg Thm 1.21, citing Lenstra
  [Len80, §3]): for G = ℤ/nℤ acting regularly on 𝔸_ℚ^n, TFAE:
  1. 𝔸_ℚ^n/G is rational;
  2. 𝔸_ℚ^n/G is stably rational;
  3. **8 ∤ n**, and for every prime p | n with s = v_p(n), the ring ℤ[ζ_{(p−1)p^{s−1}}] contains
     an element of norm p or −p.
  The smallest abelian counterexample is **ℤ/8ℤ** — the same 2-adic obstruction as the
  Grunwald–Wang special case (Wittenberg Prop. 1.20).
* **Plans 2017** (Wittenberg Thm 1.22): condition (3) is equivalent to
  n | 2²·3^m·5²·7²·11·13·17·19·23·29·31·37·41·43·61·67·71 for some m ≥ 0. In particular
  Noether's problem is **negative over ℚ for ℤ/pℤ for all but finitely many primes p** (the only
  known affirmative primes are p ≤ 43 together with 61, 67, 71).
* **Non-abelian, over ℂ**: Saltman 1984 and Bogomolov 1988 give counterexamples already over ℂ,
  by the unramified Brauer group ("Bogomolov's formula", Wittenberg Thm 1.23). These are
  p-groups. So Noether's problem is *hopeless* as a general route to solvable groups.

**Verdict: Noether's problem is a dead end for this project.** It fails for ℤ/8, fails for almost
all ℤ/p, and fails for non-abelian p-groups even over ℂ. It is worth knowing only to avoid
spending effort on it.

### 3.4 Other CFT-free theorems of the shape "normal series with factors of type X"

* **Semiabelian groups** (§3.2) — the main one, and the *only* clean "normal-series" class known
  to be realizable by purely Hilbertian methods.
* **Groups with a normal series whose factors are Sₙ / Aₙ / abelian split off**: nothing extra;
  closure of realizability under quotients and the Ikeda step already covers what is available.
* **GAR-realizations** (Malle–Matzat Ch. IV §3.1; Fried–Jarden §16.8): if every finite simple
  group had a GAR-realization over ℚ^ab, the Shafarevich Conjecture (that Gal(ℚ̄/ℚ^ab) is free
  profinite) would follow. This is a *different, much harder* programme; Harbater's survey
  (<https://www2.math.upenn.edu/~harbater/sc1.pdf>) is the reference. Not a route to solvable
  groups over ℚ.
* **Iwasawa's theorem** (NSW Ch. IX): Gal(k_solv/k^ab...) freeness statements — these are CFT-heavy.
* **Neukirch 1979** (*On solvable number fields*, Invent. Math. **53**): pro-solvable groups of
  finite exponent **prime to #μ(k)** with prescribed local behaviour. Scholz–Reichardt-flavoured,
  so still CFT.

---

## 4. Mathlib gap analysis

Roots: Mathlib at `/home/alex_harmonic_fun/InverseGaloisProblem/.lake/packages/mathlib/Mathlib`
(abbreviated `$M`); local project at `/home/alex_harmonic_fun/InverseGaloisProblem/InverseGalois`
(abbreviated `$L`).

### 4.1 Absent, and hard

| Ingredient | Status | Notes |
|---|---|---|
| **Chebotarev density theorem** | **ABSENT** | Zero occurrences of "chebotarev" anywhere in Mathlib. |
| **Dirichlet / natural density of sets of primes** | **ABSENT** | No `dirichletDensity`, `natDensity`, `upperDensity`. `$M/Combinatorics/Schnirelmann.lean` has `schnirelmannDensity`, the wrong notion. `$M/NumberTheory/PrimeCounting.lean` has `Nat.primeCounting` but no asymptotics; no PNT. |
| **Class field theory**: Artin reciprocity, Artin map, ray class groups/fields, Hilbert class field, idele class group | **ABSENT** | Only a comment at `$M/RingTheory/Valuation/Discrete/Basic.lean:61` pointing at the external `mariainesdff/LocalClassFieldTheory` repo. |
| **Kronecker–Weber** | **ABSENT** | Zero hits. |
| **Grunwald–Wang** | **ABSENT in Mathlib / EXISTS locally** | Zero hits upstream, nothing adjacent (no Ш, no local–global for cyclic extensions). `$L/CFT/GrunwaldWang.lean` proves the power-class form for a squarefree exponent — see §0.24. |
| **Poitou–Tate duality / local duality** | **ABSENT** | No profinite group cohomology at all. |
| **Hilbert symbols, power residue symbols, higher reciprocity** | **ABSENT** | Quadratic case is complete (§4.2), everything above degree 2 is missing. |
| **Brauer group** | **PARTIAL — a stub** | `$M/Algebra/BrauerGroup/Defs.lean` is 98 lines: `CSA`, `IsBrauerEquivalent`, `BrauerGroup K := Quotient …`. **There is no group structure on it.** No `Br(K) ≅ H²(Gal, K̄ˣ)`, no local invariants, no Albert–Brauer–Hasse–Noether. |
| **H² ↔ (central) group extensions** | **ABSENT, an explicit TODO** | `$M/GroupTheory/GroupExtension/Defs.lean:51` lists the bijection as future work; `$M/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean:50` lists it too. No `IsCentralExtension` anywhere. |
| **Chief series / elementary abelian factors / composition series of groups** | **ABSENT** | `$M/Order/JordanHolder.lean` has `CompositionSeries` but the only `JordanHolderLattice` instance is `Submodule R M` (`$M/RingTheory/SimpleModule/Basic.lean:544`); **there is no instance for `Subgroup G`**. No `chiefSeries`, no "elementary abelian". |
| **Embedding problems (any formalized notion), free profinite groups** | **ABSENT** | Local substitute: the whole `$L/Rigidity/RET/Pi1/` étale-π₁ development. |
| **Hilbert irreducibility** | **ABSENT in Mathlib** | See §4.3 — the local project has it. |
| **Noether's problem / rationality of fields / Lüroth** | **ABSENT in Mathlib** | No rationality predicate, no Lüroth. Raw material: `$M/FieldTheory/Fixed.lean` (Artin's theorem `finrank (FixedPoints.subfield G F) F = card G`). Local: `$L/Hilbert/Analytic/Luroth.lean`. |
| **Artin–Schreier** | **ABSENT in Mathlib / EXISTS locally** | `$L/Experimental/ArtinSchreier.lean` (`artinSchreier_irreducible`). |

### 4.2 Present and usable

| Ingredient | Status | Where |
|---|---|---|
| **Dirichlet's theorem on primes in AP** | **EXISTS, complete** | `$M/NumberTheory/LSeries/PrimesInAP.lean`: `Nat.infinite_setOf_prime_and_eq_mod` (:475), `Nat.forall_exists_prime_gt_and_eq_mod` (:487), `Nat.forall_exists_prime_gt_and_zmodEq` (:495), `Nat.frequently_atTop_prime_and_modEq` (:512). Supporting: `$M/NumberTheory/DirichletCharacter/*`, `$M/NumberTheory/LSeries/{Dirichlet,Nonvanishing}.lean`. |
| **Dedekind zeta + analytic class number formula** | **EXISTS** | `$M/NumberTheory/NumberField/DedekindZeta.lean`: `NumberField.dedekindZeta` (:47), `dedekindZeta_residue` (:54), `dedekindZeta_residue_pos` (:63), **`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` (:75)** — the simple pole at s = 1. *No Euler product yet.* |
| **Euler product machinery** | **EXISTS (ℕ-indexed)** | `$M/NumberTheory/EulerProduct/Basic.lean`: `eulerProduct` (:209), `ArithmeticFunction.IsMultiplicative.eulerProduct` (:252), `eulerProduct_completely_multiplicative` (:366). |
| **Legendre / Jacobi symbols, quadratic reciprocity** | **EXISTS, complete** | `$M/NumberTheory/LegendreSymbol/Basic.lean:108` `legendreSym` (root namespace, *not* `ZMod.legendreSym`); `.../QuadraticReciprocity.lean:107` `legendreSym.quadratic_reciprocity`; `.../JacobiSymbol.lean:86` `jacobiSym` with full reciprocity. |
| **Dedekind–Kummer factorization** | **EXISTS, two layers** | `$M/NumberTheory/KummerDedekind.lean:103` `KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`; `$M/NumberTheory/NumberField/Ideal/KummerDedekind.lean:168` `primesOverSpanEquivMonicFactorsMod` with the ramification/inertia dictionary at :210–:252. Local: `$L/Polynomial/DedekindFacts.lean`, `DedekindProof.lean`. |
| **Frobenius element** | **EXISTS** | `$M/RingTheory/Frobenius.lean`: `AlgHom.IsArithFrobAt` (:54), `IsArithFrobAt` (:182), `arithFrobAt R G Q : G` (:253), `isConj_arithFrobAt` (:261) — *the Frobenius conjugacy class map Chebotarev would need*, `IsArithFrobAt.eq_of_isUnramifiedAt` (:163). |
| **Decomposition / inertia** | **PARTIAL, unnamed** | No `Ideal.decompositionGroup` — it is spelled `MulAction.stabilizer G Q`. `Ideal.inertia` at `$M/RingTheory/Ideal/Defs.lean:152` (very general abbrev); `ValuationSubring.{decomposition,inertia}Subgroup` at `$M/RingTheory/Valuation/RamificationGroup.lean:30,50`. Structure theory: `$M/RingTheory/Invariant/Basic.lean` `Ideal.Quotient.stabilizerQuotientInertiaEquiv` (:399) = D/I ≅ Gal(residue). Counting: `$M/NumberTheory/RamificationInertia/Galois.lean` (`ramificationIdxIn`, `inertiaDegIn`, `card_stabilizer_eq` = e·f at :337, fundamental identity at :237). `galRestrict` at `$M/RingTheory/IntegralClosure/IntegralRestrict.lean:178`. |
| **"Splits completely" / unramified** | **PARTIAL** | No named `totallySplit`/`splitsCompletely` predicate anywhere; must be spelled `(primesOver p B).ncard = finrank K L` or e = f = 1. `Algebra.IsUnramifiedAt` at `$M/RingTheory/Unramified/Locus.lean:45`; the bridge `Algebra.isUnramifiedAt_iff_of_isDedekindDomain` at `$M/NumberTheory/RamificationInertia/Unramified.lean:90`. |
| **Group cohomology H¹, H²** | **EXISTS, rich** | `$M/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`: `H1` (:927), `H2` (:1003), `cocycles₁/₂` (:266/:271), `IsMulCocycle₁/₂` (:611/:615). Also `Hilbert90.lean`, `LongExactSequence.lean`, `Shapiro.lean`, `FiniteCyclic.lean`. *Note the path is `RepresentationTheory/Homological/GroupCohomology/`, not `RepresentationTheory/GroupCohomology/`.* |
| **Hilbert 90** | **EXISTS** | `$M/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`: `isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units` (:84), `exists_div_of_norm_eq_one` (:132). |
| **Kummer theory** | **EXISTS, complete** | `$M/FieldTheory/KummerExtension.lean`: irreducibility of Xⁿ − C a (:130–:143), `autEquivZmod` (:411), `isCyclic_of_isSplittingField_X_pow_sub_C` (:431), converse `exists_root_adjoin_eq_top_of_isCyclic` (:464), `isCyclic_tfae` (:542). |
| **`RegularWreathProduct`** | **EXISTS** | `$M/GroupTheory/RegularWreathProduct.lean:45` `structure RegularWreathProduct D Q`, notation `D ≀ᵣ Q` (:51), `Group` instance (:84), `IteratedWreathProduct`, `Sylow.mulEquivIteratedWreathProduct`. **Only the regular wreath product** — no `G ≀_X H` for a general action, and no twisted wreath product. |
| **`SemidirectProduct`** | **EXISTS, full API** | `$M/GroupTheory/SemidirectProduct.lean`, `N ⋊[φ] G`. |
| **Group extensions** | **EXISTS (defs only)** | `$M/GroupTheory/GroupExtension/Defs.lean:74` `structure GroupExtension N E G`, `.Splitting` (:271); `$M/GroupTheory/GroupExtension/Basic.lean:152,178` `semidirectProductToGroupExtensionEquiv`, `semidirectProductMulEquiv` (split ⟹ semidirect). No H² classification, no obstruction theory. |
| **Solvable / nilpotent** | **PARTIAL** | `$M/GroupTheory/Solvable.lean:104` `class IsSolvable` (= derived series terminates) with sub/quotient/product closure (:138–:152); `$M/GroupTheory/Nilpotent.lean:184` `Group.IsNilpotent`. Adjacent: `$M/GroupTheory/{Frattini,SchurZassenhaus,Sylow,PGroup,Transfer,Goursat}.lean`, `$M/GroupTheory/IsSubnormal.lean` (`exists_normal_and_le_and_lt_top_of_ne` :145). **Fitting subgroup: check — not found under that name.** |
| **Chevalley–Warning** | **EXISTS** | `$M/FieldTheory/ChevalleyWarning.lean`. |
| **Class group, adeles** | **EXISTS (thin)** | `$M/RingTheory/ClassGroup.lean:86` `ClassGroup`, finiteness in `$M/NumberTheory/ClassNumber/*`; `$M/NumberTheory/NumberField/AdeleRing.lean:47` `AdeleRing`. **No idele group, no idele class group, no norm/Artin map.** |

### 4.3 The local project's own assets

* **Hilbert irreducibility.** `$L/Hilbert/HilbertIrreducibility.lean` (592 lines):
  `hilbert_irreducibility_monic` (:255), `hilbert_irreducibility_theorem` (:423) — for
  `f : Polynomial (Polynomial ℚ)`, infinitely many **integer** specializations preserving
  irreducibility; `reducibleLocus` (:471), `reducibleLocus_not_univ` (:477). Support:
  `$L/NumberTheory/IntegerPointsSublinear.lean`, `$L/NumberTheory/PrimeLowerBound.lean`
  (elementary π(n) lower bounds — the same technique Serre's Lemma 2.1.4 needs).
  Downstream seam: `$L/Hilbert/RegularExtension.lean:136` `IsInverseGalois.of_regular_family`.
* **Realizability predicates.**
  `$L/Core/Basic.lean:29` `IsInverseGalois G`, with `of_mulEquiv`, `of_surjective`, `quotient`.
  `$L/Rigidity/RET/Statement.lean:66,81,91` `IsRegularGaloisGroupOverBase k F G`,
  `IsRegularGaloisGroupOver K G`, `IsRegularInverseGalois G`.
* **The bridge.** `$L/Rigidity/RET/Specialization.lean:1107`
  `IsRegularInverseGalois.isInverseGalois : IsRegularInverseGalois G → IsInverseGalois G`.
* **Abelian.** `$L/Rigidity/RET/AbelFinale.lean:73`
  `Rigidity.RET.IsRegularInverseGalois.of_commGroup (A) [CommGroup A] [Finite A] :
  IsRegularInverseGalois A`. **Currently hard-wired to base field ℚ** — the multi-radical tower
  in `$L/Rigidity/RET/AbelRegular.lean` is built over `FF = ℚ(T)`. The *geometric* layer below it
  is already parameterized by an arbitrary base field k
  (`$L/Rigidity/RET/ExistenceAbelian.lean:88 exists_cover_of_commGroup`,
  `$L/Rigidity/RET/DeckGroups.lean:93 isDeckGroupOver_of_commGroup`).
* **Rigidity + descent.** `$L/Rigidity/Rigidity.lean:49 rigidity_realizable`;
  `$L/Rigidity/RigidData.lean` (`RigidData`, `StableRigidData`, `RigidityCertificateH`);
  `$L/Rigidity/RET/Descent/` (`exists_regular_numberField_of_orbitRigid`, `Index2`).
* **Catalogue.** `$L/Catalogue.lean` is the index of everything realized.

---

## 5. Recommended roadmap

### 5.0 The strategic conclusion first

*(Read §0 first: the group-theoretic scaffolding this section prices as expensive turned out to be
cheap and is now formalized. The verdicts below concern the arithmetic, and they stand.)*

There are two candidate routes and they are **not** equally good.

**Route A (classical / arithmetic): Scholz–Reichardt, then Shafarevich.** Requires
Brauer–Hasse–Noether, Kronecker–Weber (or full CFT), Grunwald–Wang, Poitou–Tate. Every one of
these is absent from Mathlib and each is, by itself, a multi-year formalization. Mathlib does not
even have a *density* of a set of primes. **Do not start here.**

**Route B (Hilbertian / geometric): Ikeda ⇒ semiabelian groups.** Requires exactly two things,
both of which this repository already has in usable form: (i) regular realizations of finite
abelian groups over a base field, and (ii) Hilbert irreducibility over ℚ. It reaches a large,
crisply-defined subclass of the solvable groups (all nilpotent of class 2, all solvable with
abelian Sylows, all abelian-by-cyclic, all iterated wreath products, closed under quotients).
**Start here.** It is also the route that composes with everything already in the Catalogue: for
any H already realized (Sₙ, Aₙ, dihedral, PGL₂(𝔽_p), Mathieu…), Ikeda immediately yields A ⋊ H
and A ≀ H for every finite abelian A with an H-action.

The honest headline: **Shafarevich's theorem itself is a multi-year, probably multi-person
project that is gated on class field theory in Mathlib, and should not be attempted directly.
Semiabelian groups are a genuine, publishable, achievable target that captures a large slice of
the solvable world.**

Effort units below: **S** ≈ days, **M** ≈ 1–3 weeks, **L** ≈ 1–3 months, **XL** ≈ 6–18 months,
**XXL** ≈ multi-year.

### Milestone 1 — Regular abelian realization over an arbitrary number field. **[M–L]**

Generalize `Rigidity.RET.IsRegularInverseGalois.of_commGroup` from ℚ to an arbitrary base field
k of characteristic 0 (at minimum, an arbitrary number field N):

```
IsRegularGaloisGroupOver N A     for every number field N and finite abelian A
```

The geometric layer (`ExistenceAbelian`, `DeckGroups`, `KummerAbelian`) is already
base-parameterized; the work is in the arithmetic layer `AbelRegular.lean`, where `FF = ℚ(T)`,
`EE n`, `GG n`, `KK n` are all built over ℚ. The obstacle is the μ_n-descent bookkeeping
(the `Φ`-exponent twisted-Kummer recipe) over a base that may already contain roots of unity.

*Value:* prerequisite for everything downstream, and independently strengthens the Catalogue.
*Risk:* low. This is engineering, not mathematics.

### Milestone 2 — The regular wreath-product construction. **[L]**

Given a finite group H with `IsRegularGaloisGroupOver k H` (or just a Galois L/k with group H)
and a finite abelian A, build a regular Galois extension of k(t_h : h ∈ H) with group A ≀ᵣ H,
using `RegularWreathProduct` (`$M/GroupTheory/RegularWreathProduct.lean`).

Sub-tasks:
* (2a) **[S]** The group-theoretic surjection `A ≀ᵣ H ↠ A ⋊[φ] H` for any H-action φ on A, over H.
  Pure Mathlib group theory; combines `RegularWreathProduct` and `SemidirectProduct`.
* (2b) **[M]** Linear disjointness of the |H| conjugate A-extensions in independent variables;
  the deck group of the compositum is the wreath product. The repo already has the compositum /
  product machinery: `$L/Rigidity/RET/{Product,ProductTranslate,ProductGeometric}.lean`
  (`IsAffineDeckGroup.prod`, `IsGeometricGaloisCover.prod`). This is the closest existing analogue
  and should be reusable — beware, `Product.lean` is the repo's most expensive file.
* (2c) **[M]** Descent of the compositum to k(t_h) with the H-permutation action on the variables.

*Value:* high — this is the whole engine.
*Risk:* medium. The linear-disjointness bookkeeping is where these proofs always bloat.

### Milestone 3 — Multivariable Hilbert irreducibility over ℚ. **[M]**

`$L/Hilbert/HilbertIrreducibility.lean` gives the one-variable statement with integer
specializations. Ikeda needs |H| variables. The standard reduction (Fried–Jarden §12.1) is:
specialize one variable at a time, keeping the others generic. Formalizing "ℚ(t₂,…,t_n) is
Hilbertian because ℚ is" in the generality of Fried–Jarden Ch. 13 is **[L]**; formalizing only
the *concrete* iterated specialization needed for the wreath product is **[M]**.

*Value:* high; also unblocks other multivariable constructions.
*Risk:* medium — the interaction between the existing `specialize`/`reducibleLocus` API and a
tower of specializations may need the whole file re-architected.

### Milestone 4 — Ikeda's theorem. **[M, given 1–3]**

```
theorem ikeda (k Hilbertian, char 0) (L/k Galois with group H) (A finite abelian, H-action) :
  ∃ F/k Galois, Gal(F/k) ≃* A ⋊[φ] H,  compatibly with L
```
Assemble: Milestone 2 gives A ≀ᵣ H regularly over k(t_h); Milestone 3 specializes; (2a) plus
`IsInverseGalois.quotient` cuts down to A ⋊ H. State it in the repo's `IsInverseGalois` /
`IsRegularGaloisGroupOverBase` vocabulary so it plugs into the Catalogue.

*Value:* **highest value/effort ratio in this document.**

### Milestone 5 — Semiabelian groups. **[M, given 4]**

* (5a) **[S]** Define `IsSemiabelian : Type* → Prop` inductively (Dentzer Def. 2.1: closed under
  quotients and A ⋊ H).
* (5b) **[S–M]** `IsSemiabelian G → IsInverseGalois G` by induction, using Milestone 4 and
  `IsInverseGalois.quotient`.
* (5c) **[M]** Concrete corollaries worth stating in `Catalogue.lean`: every finite nilpotent
  group of class ≤ 2 is semiabelian; every finite solvable group with abelian Sylow subgroups is
  semiabelian; every iterated wreath product of abelian groups. Each needs the corresponding
  group-theoretic lemma, none of which is in Mathlib.

*Value:* this is the deliverable. It is the largest new family of solvable groups over ℚ that is
reachable at all with current Mathlib.

### Milestone 6 (optional, high value elsewhere) — Split-density of primes. **[M–L]** — **DONE**, see §0

Prove: *for K/ℚ Galois of degree n, the set of rational primes splitting completely in K has
Dirichlet density 1/n; in particular, for A ⊊ B with B/ℚ Galois, infinitely many primes split
completely in A but not in B* (statement (★) of §1.5).

Path: (6a) prove `n ↦ #{I ⊴ 𝒪_K : absNorm I = n}` is multiplicative, apply
`ArithmeticFunction.IsMultiplicative.eulerProduct` to get the Euler product for
`NumberField.dedekindZeta`; (6b) combine with
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` to get
`Σ_{q split in K} q^{-s} ~ (1/n) log(1/(s-1))`; (6c) conclude.

*Value:* this is the **only** ingredient of Chebotarev that Scholz–Reichardt actually needs, it is
the natural first step toward a real Chebotarev in Mathlib, and it would be a genuine Mathlib
contribution independent of this project. It also subsumes Serre's Lemma 2.1.4 (existence of
completely split primes) as a corollary.
*Risk:* low-to-medium; the analytic scaffolding is all present.

### Milestone 7 — Serre's Lemma 2.1.4, elementary version. **[S–M]** — **DONE**, see §0

*"For a finite extension E/ℚ there are infinitely many primes splitting completely in E,"* by
Serre's counting argument (values of f, smooth-number counting). Independent of Milestone 6 and
much cheaper. Uses the same style of estimate as `$L/NumberTheory/PrimeLowerBound.lean`.

*Value:* moderate on its own; it is the split case of Scholz–Reichardt (item 1 of §1.4) and a
useful standalone lemma.

### Milestone 8 — Kronecker–Weber. **[XL]**

Needed for Serre's Lemma 2.1.6 (item 5 of §1.4), i.e. for *any* progress on the non-split case of
Scholz–Reichardt. Absent from Mathlib. There is a known Lean-community interest in this but no
landed formalization. **6–18 months.** Consider only as a Mathlib contribution in its own right,
not as a step in this project.

### Milestone 9 — Brauer group with its group law, local invariants, and Albert–Brauer–Hasse–Noether. **[XXL]**

Needed for Serre's Lemma 2.1.5 (item 2 of §1.4). Mathlib's `BrauerGroup` is a bare quotient type
with **no multiplication**. To get to ABHN one needs: the group law, `Br(K) ≅ H²(Gal, K̄ˣ)`
(which needs the H²-↔-crossed-product dictionary, itself absent), `Br(ℚ_p) ≅ ℚ/ℤ` (local CFT), and
the global exact sequence (global CFT). **Multi-year.**

**Update (2026-08-21): the first two are done**, see §0.1 — the group law, Skolem–Noether, the
double centralizer theorem, Wedderburn in the split case, Galois descent, the crossed product, and
`Br(L/K) ≅ H²(Gal(L/K), Lˣ)` for every finite Galois `L/K`, together with the cyclic case
`Br(L/K) ≅ Kˣ/N(Lˣ)` and `Br(ℂ/ℝ) ≅ ℤ/2`. What remains of this milestone is exactly the arithmetic:
`Br(ℚ_p) ≅ ℚ/ℤ` and the global exact sequence. Note that Mathlib cannot yet even state the first —
`IsNonarchimedeanLocalField` has no instances, so `ℚ_[p]` must first be equipped with
`ValuativeRel`, `IsValuativeTopology` and `LocallyCompactSpace`.

### Milestone 10 — Scholz–Reichardt. **[XXL, gated on 8 and 9]**

Only meaningful after 6/7 + 8 + 9. Then the remaining work (the (S_N) induction, the linear
disjointness Lemma 2.1.9, the local liftability analysis, the character-correction bookkeeping) is
itself an **[L]**–**[XL]** project. Realistically 2+ years from today.

### Milestone 11 — Shafarevich. **[XXL, gated on 10 + Grunwald–Wang + Poitou–Tate]**

Adds Grunwald–Wang (**[XXL]**, needs CFT — but see §0.24: the power-class form for a squarefree
exponent is landed, so what is left of this item is the character form), Poitou–Tate duality
(**[XXL]**, needs profinite group
cohomology which Mathlib entirely lacks), the (i,j)-filtration and shrinking machinery
(**[L]**, mostly elementary — Chevalley–Warning is already in Mathlib), and the Frattini/Fitting
reduction (**[M]**; the Fitting subgroup does not appear to exist in Mathlib and would need
defining). **Not attemptable this decade without a Mathlib class field theory project.**

### Recommended ordering

```
1 → 2 → 3 → 4 → 5        (the deliverable: semiabelian groups over ℚ)
        ⌐ 7              (cheap, independent, useful)
        ⌐ 6              (Mathlib contribution; the only Chebotarev SR needs)
                8, 9, 10, 11   ← do not start
```

Realistic total for Milestones 1–5: **3–6 months** of concentrated work, with Milestone 2 the
likely bottleneck. Milestones 6–7 add **1 month** and are separable.

### A warning about the regular route

Serre's Remark 4 after Theorem 2.1.1 is worth repeating: **it is not known whether an arbitrary
ℓ-group is the Galois group of a regular extension of ℚ(T).** So the repository's
`IsRegularInverseGalois` predicate — the backbone of everything in `Catalogue.lean` — *cannot*
be the target for solvable groups; there is no theorem to formalize. Ikeda's theorem lands in
`IsInverseGalois`, not `IsRegularInverseGalois`, and the wreath-product construction of
Milestone 2 is regular only over the multivariable base k(t_h : h ∈ H), not over k(T). Any
milestone plan that tries to route solvable groups through `IsRegularInverseGalois` is attempting
an open problem. (Dentzer's paper studies exactly which semiabelian groups *do* have geometric
realizations — that is the correct reference if a regular statement is ever wanted.)

---

## Sources

* J.-P. Serre, *Topics in Galois Theory*, Harvard 1988, notes by H. Darmon —
  <https://www.ms.uky.edu/~sohum/ma561/notes/workspace/books/serre_galois_theory.pdf>
  (§2.1 Thm 2.1.1, Def. 2.1.2, Thm 2.1.3, Lemmas 2.1.4–2.1.9, Thm 2.1.11).
* A. Schmidt, K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups* —
  <https://arxiv.org/abs/math/9809211> (Thms 1, 13, 14, 15; Props 2, 11, 16, 17).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323,
  Ch. IX §6 — <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>.
* G. Malle, B. H. Matzat, *Inverse Galois Theory*, Springer Monographs in Mathematics, 1999,
  Ch. IV "Embedding Problems" — <https://link.springer.com/chapter/10.1007/978-3-662-12123-8_4>.
* M. D. Fried, M. Jarden, *Field Arithmetic*, 3rd ed., Springer 2008, §§12.1, 13.7, 16.3, 16.4,
  16.8 — <https://link.springer.com/book/10.1007/978-3-540-77270-5>.
* O. Wittenberg, *Park City lecture notes: around the inverse Galois problem*, arXiv:2302.13719 —
  <https://arxiv.org/abs/2302.13719> (Problems 1.1, 1.9, 2.1; Examples 1.10–1.12; Thms 1.21, 1.22,
  1.23; Remark 2.2).
* H. W. Lenstra, Jr., *Rational functions invariant under a finite abelian group*, Invent. Math.
  **25** (1974), 299–325 — <https://eudml.org/doc/142292>.
* R. Dentzer, *On geometric embedding problems and semiabelian groups*, manuscripta math. **86**
  (1995), 199–216 — <https://link.springer.com/article/10.1007/BF02567989>.
* F. Legrand, *On finite embedding problems with abelian kernels*, J. Algebra **595** (2022),
  633–659 — <https://hal.science/hal-03517543v1>.
* P. Schmid, *Realizing 2-groups as Galois groups following Shafarevich and Serre*,
  Algebra & Number Theory **12** (2018), 2387–2401 — <https://projecteuclid.org/euclid.ant/1550113226>.
* D. Harbater, *The Shafarevich Conjecture in inverse Galois theory* —
  <https://www2.math.upenn.edu/~harbater/sc1.pdf>.
* Wikipedia, *Shafarevich's theorem on solvable Galois groups* —
  <https://en.wikipedia.org/wiki/Shafarevich%27s_theorem_on_solvable_Galois_groups>;
  *Semiabelian group* — <https://en.wikipedia.org/wiki/Semiabelian_group>.
