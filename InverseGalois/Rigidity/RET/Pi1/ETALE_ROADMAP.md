# Étale fundamental group roadmap — the honest option-C decomposition

Goal: shrink the sole transcendental input behind `inertiaRootData_exists`
(`Descent/Tower.lean`) to the *smallest recognizable* Riemann-existence comparison, by
building — as genuine, axiom-free Lean — everything on either side of it. This is the
"build the from-scratch algebraic/étale π₁ theory" fork.

## The one thing that stays transcendental (and why C cannot remove it)

The chain behind `inertiaRootData_exists` needs, for the punctured line over `ℚ̄`:

>   π₁^tame(ℙ¹_ℚ̄ ∖ {r points})  ≅  sphereCompletion r
>        ( = profinite completion of  ⟨x₀,…,x_{r-1} | ∏ xᵢ = 1⟩ )

This isomorphism **is** the Riemann Existence Theorem. It compares the *algebraic* (étale)
fundamental group with a *topological/analytic* presentation (free profinite on `r-1`
generators, product-one). There is no algebraic proof: it is the comparison of the algebraic
and complex-analytic π₁ (GAGA + van Kampen on the punctured sphere). Building the étale π₁ in
full does **not** eliminate this step — it only lets us *restate* it as a clean group-theoretic
comparison and prove everything else. Areas 3 (topological π₁ / covering spaces with a computed
π₁) and 6 (GAGA / Riemann surfaces / analytification) are essentially absent from Mathlib, so
this comparison is the irreducible floor.

**Net effect of option C:** the cut moves from one *bundled* `sorry` (`inertiaRootData_exists`,
which fuses cover-existence + inertia data + descent) to one *minimal* comparison isomorphism,
with the cover↔extension dictionary and the tame-inertia/Fried layer promoted to genuine proofs.
Strictly more honest, strictly smaller transcendental surface.

## Three layers

### (I) Covers ↔ finite extensions — Grothendieck–Galois dictionary  [BUILDABLE]

Instantiate Mathlib's abstract Galois-category machinery
(`CategoryTheory.Galois`: `GaloisCategory`, `FiberFunctor`, `IsFundamentalGroup`,
`functorToContAction : C ⥤ ContAction FintypeCat (Aut F)` an equivalence) for the category of
**finite étale algebras over a field** `K`, with fibre functor `A ↦ (A →ₐ[K] Ω)` into finite
`Gal(Ω/K)`-sets. Fundamental group `Aut F ≅ Gal(Ω/K) = Field.absoluteGaloisGroup K`.

Foundation (Area 2, the main gap). Key Mathlib assets:
* `Algebra.Etale.iff_exists_algEquiv_prod` (`RingTheory/Etale/Field.lean:208`):
  finite étale `K`-algebra `≃ₐ` finite product of finite separable field extensions. **The
  structural engine.**
* `AlgHom.card` (`FieldTheory/PrimitiveElement.lean:364`):
  `Fintype.card (E →ₐ[F] K) = finrank F E` for finite separable `E`, `K` alg. closed. **Degree.**
* `Field.Emb`, `Field.finSepDegree` (`FieldTheory/SeparableDegree.lean`).
* `Field.absoluteGaloisGroup`, `IsGaloisGroup` (unwired to `Aut F` — the target identification).

Genuine leaves, easiest first:
1. ✅ **LANDED** (`Etale/Fiber.lean`) — `(A →ₐ[K] Ω)` finite for finite étale `A`;
   `natCard_algHom_eq_finrank_of_etale : Nat.card (A →ₐ[K] Ω) = finrank K A`.
   Crux leaf DONE: `reassemble_bijective` gives `Σ i, (Lᵢ →ₐ[K] Ω) ≃ ((Π i, Lᵢ) →ₐ[K] Ω)` when
   `Ω` is a field (orthogonal idempotents `Pi.single i 1` map to `{0,1}`, exactly one to `1`);
   `natCard_algHom_pi` is the reusable degree-sum lemma (not in Mathlib).
2. ✅ **LANDED** (`Etale/Fiber.lean`) — `fibreMulAction : MulAction (Ω ≃ₐ[K] Ω) (A →ₐ[K] Ω)` by
   post-composition (`fibre_smul_apply`). Continuity of the action: still owed (needs the profinite
   topology on `Aut F` / `Gal(Ω/K)` — deferred to (I).5).
3. ✅ **LANDED** (`Etale/Fiber.lean`) — **the object-level dictionary is now complete (both
   directions + faithfulness + torsor):**
   * connected ⇒ transitive: `fibre_isPretransitive : IsPretransitive (Ω ≃ₐ[K] Ω) (E →ₐ[K] Ω)` for
     `E` a field, `Ω / K` normal (via `AlgEquiv.liftNormal` on the corestricted image isomorphism);
     `fibre_nonempty` (via `IsAlgClosed.lift`) makes the fibre of a field a *single nonempty* orbit.
   * orbit decomposition: `reassemble_smul` shows the product↔sigma bijection is Gal-equivariant, so
     the orbits on a product's fibre are exactly its field factors.
   * **transitive ⇒ connected (converse)**: `subsingleton_of_isPretransitive` (product form) and
     `subsingleton_of_algEquiv_pi_of_isPretransitive` (étale-algebra form, via `precompActionHom` +
     `IsPretransitive.of_surjective_map`) — a transitive fibre forces a single field factor.
   * **functor faithfulness**: `separating_of_etale` (nonzero `a` detected by some `f : A →ₐ[K] Ω`,
     via the field-factor decomposition + `IsAlgClosed.lift`) ⇒ `faithful_of_etale` (morphisms of
     finite étale algebras are determined by their action on fibres).
   * **torsor trivialisation / fibre-count**: `natCard_fibre_eq_card_aut_of_normal` —
     `Nat.card (E →ₐ[K] Ω) = Nat.card (E ≃ₐ[K] E)` for `E / K` normal (base-point-free wrapper of
     Mathlib `Normal.algHomEquivAut`, installing the `E`-algebra structure on `Ω` from a chosen base
     embedding). The object-level seed of (I).5 `Aut F ≅ Gal`.
   * ✅ **categorical substrate LANDED** (`Etale/Category.lean`): the finiteness
     `finite_algHom_of_etale : Finite (A →ₐ[K] Ω)` (from the field-factor decomposition + the sigma
     bijection); the category `FiniteEtaleAlgCat K := (isFiniteEtale K).FullSubcategory` (full
     subcategory of `CommAlgCat K` on `Algebra.Etale K`); and the **fibre functor** as an honest
     `CategoryTheory.Functor` `fibreFunctor K Ω : (FiniteEtaleAlgCat K)ᵒᵖ ⥤ FintypeCat`,
     `A ↦ (A →ₐ[K] Ω)`, morphisms ↦ pre-composition. Plus the Galois action on its values
     (`fibreMulActionObj`) and its **naturality** `IsNaturalSMul (fibreFunctor K Ω) (Ω ≃ₐ[K] Ω)` ⟹
     the canonical `PreGaloisCategory.toAut : (Ω ≃ₐ[K] Ω) →* Aut (fibreFunctor K Ω)` is now available.
4. Verify `PreGaloisCategory` / `GaloisCategory` axioms G1–G6 for `(FiniteEtaleAlgCat K)ᵒᵖ`
   (terminal, pullbacks, finite coproducts, finite-group quotients, mono = summand, fibre
   preserves + reflects). Each is real commutative algebra — the bulk of the work. The fibre functor
   and its `FintypeCat` target now exist (leaf 3), so these can be stated directly against it.
   * ✅ **closure bricks LANDED** (`Etale/Closure.lean`): the commutative-algebra facts feeding the
     (co)limit-existence fields — `Algebra.Etale.prod` (`A × B` finite étale, via the field-factor
     characterisation + the gluing `AlgEquiv` `prodPiSumAlgEquiv : ((∀ i, P i) × (∀ j, Q j)) ≃ₐ[K]
     ∀ k : I ⊕ J, Sum.elim P Q k`), `Algebra.Etale.tensorProduct` (`A ⊗[K] B` finite étale, via
     `Etale.baseChange` + `Etale.comp`), and the base `Algebra.Etale K K` (inference).  KEY GOTCHA:
     route the ring structure on `Sum.elim P Q k` through a single `Field` instance (`sumElimField`,
     private forall-shaped) so `CommRing` derives canonically — a separate `CommRing` path gives a
     stuck-`Sum.rec` diamond that breaks the `iff_exists_algEquiv_prod.mpr` witness matching.
   * ✅ **field G1 (`hasTerminal`) LANDED** (`Etale/Category.lean`): `base K = ⟨CommAlgCat.of K K, _⟩`
     is the initial object of `FiniteEtaleAlgCat K` (`baseIsInitial`, via `CommAlgCat.isInitialSelf`
     transported through `ObjectProperty.homMk`/`hom_ext`), hence `op (base K)` is terminal in the
     opposite (`opBaseIsTerminal` via `terminalOpOfInitial`) and `HasTerminal (FiniteEtaleAlgCat K)ᵒᵖ`
     is an instance.
   * ✅ **field G2 (`hasFiniteCoproducts`) + finite products LANDED** (`Etale/Limits.lean`):
     `Algebra.Etale.pi` (a finite `Pi` of finite étale algebras is finite étale, via the field-factor
     characterisation + the sigma-recurry `AlgEquiv` `piCurryAlgEquiv`); iso-closure of
     `isFiniteEtale K`; `piConeIsLimit` (the `Pi`-algebra IS the categorical product in `CommAlgCat K`
     of a finite discrete diagram — Mathlib lacks this identification); hence
     `IsClosedUnderLimitsOfShape (Discrete J)` (universe-`u`) and, transported along
     `Discrete (ULift (Fin n)) ≌ Discrete (Fin n)` via `IsClosedUnderLimitsOfShape.of_equivalence`,
     `HasFiniteProducts (FiniteEtaleAlgCat K)`; dualised to `HasFiniteCoproducts
     (FiniteEtaleAlgCat K)ᵒᵖ` by `hasFiniteCoproducts_opposite`.  UNIVERSE GOTCHA: `iff_exists_algEquiv_prod`
     pins index+factors to `Type u`, so `Algebra.Etale.pi`/`piCone`/closure are `Type u`; the
     `Fin n : Type 0` shape demanded by `HasFiniteProducts` is reached only via the ULift equivalence.
   * **The clean categorical path (scouted, ready to build).** `CommAlgCat R` already has `HasLimits`
     and `HasColimits` (`Algebra/Category/CommAlgCat/Basic.lean:216,220`), and Mathlib provides
     `ObjectProperty.IsClosedUnder{Limits,Colimits}OfShape` + the full-subcategory (co)limit-creation
     helpers `CategoryTheory.Limits.FullSubcategory.{hasLimitsOfShape_of_closedUnderLimits,
     createsColimitFullSubcategoryInclusionOfClosed,…}`.  So the four (co)limit-existence fields of
     `PreGaloisCategory (FiniteEtaleAlgCat K)ᵒᵖ` reduce to `IsClosedUnder{Limits,Colimits}OfShape`
     instances on `isFiniteEtale K`, via the C↔Cᵒᵖ duality: terminal in Cᵒᵖ = initial `K` in C;
     finite coproducts in Cᵒᵖ = finite products `A × B` in C; pullbacks in Cᵒᵖ = pushouts `A ⊗_K B`
     in C.  Remaining work for these fields = identify the *ambient categorical* (co)limit in
     `CommAlgCat K` with the concrete construction (`K`, `A × B`, `A ⊗[K] B`) and invoke the closure
     bricks.  The one genuinely hard field is still `monoInducesIsoOnDirectSummand` (mono = coproduct
     summand; template = Mathlib `Galois/Examples.lean` `imageComplement`).
5. `IsFundamentalGroup (fibreFunctor K Ω) (Ω ≃ₐ[K] Ω)`; `toAutMulEquiv` ⇒ `Aut F ≅ Gal(Ω/K)`.
   `IsNaturalSMul` (leaf 3) is the first of the four `IsFundamentalGroup` fields; the remaining three
   (`transitive_of_isGalois`, `continuous_smul`, `non_trivial'`) need the `IsGalois` object notion and
   the topology on `Aut F` — blocked on leaf 4 (`PreGaloisCategory`).

### (II) The minimal transcendental comparison  [TRANSCENDENTAL — stays owed]

Specialize (I) to `K = ℚ̄(T)`, restrict to the full subcategory of covers unramified outside
`S = {r points}` (ramification via Area 5: `Ideal.ramificationIdx`), take the tame quotient
(tame = `ramificationIdx` coprime to residue characteristic). Then the sole owed input is the
comparison isomorphism above (RET). State it as a single documented goal; do **not** ATP it.

### (III) Tame inertia cyclic + Fried's cyclotomic formula  [BUILDABLE]

On the concrete extension produced by (I)+(II), the inertia data of `InertiaRootData`. Area 5 is
strong: `Ideal.ramificationIdx`/`inertiaDeg`, `sum_ramification_inertia`,
`RamificationInertia/Galois.lean`, `RingTheory/Invariant/` (`stabilizerQuotientInertiaEquiv`),
`IsPrimitiveRoot.autToPow`, `cyclotomicCharacter`. The repo already has the group-level bricks in
`Descent/TameCharacter.lean` (tame character `θ`, `conj_eq_pow_cyclotomic_of_θInjective`) and the
AKLB/ramification bricks (`GeomAKLB.lean`, `TameRamification.lean`). Missing: `tame` predicate /
Abhyankar (build via coprimality); wire the group-level Fried bricks to the concrete inertia of the
(I)+(II) extension.

## Attack order

`(I).1` (fibre + degree, self-contained, sorry-free) → `(I).2–3` → `(III)` group→concrete wiring
(reuses existing `TameCharacter`/AKLB) → `(I).4` (G1–G6, the long pole) → `(I).5` (fundamental
group identification) → state `(II)` as the single owed comparison → assemble into
`inertiaRootData_exists`, replacing the current bundled `sorry` with the `(II)` comparison.

Files land under `Pi1/Etale/`. First: `Pi1/Etale/Fiber.lean` — (I).1, fully sorry-free.
