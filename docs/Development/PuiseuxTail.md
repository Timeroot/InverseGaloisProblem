# Status: `convergent_laurent_tail_bound` and the Puiseux tail infrastructure

## Headline

`DorgeBauer.convergent_laurent_tail_bound` is now **proved and transitively `sorry`-free**
(axioms: only `propext`, `Classical.choice`, `Quot.sound`).  It was previously one of the two
deep analytic `sorry`s behind `puiseux_tail_of_root_growth`.

To make it provable (and faithful), one hypothesis was added:

```
(hgana : AnalyticOnNhd ℝ g (Set.Ioi (T₀ : ℝ)))
```

i.e. the real branch `g` is real-analytic on the open ray.  This is genuinely needed: without
it a *smooth* algebraic branch that happens to equal a polynomial only on a tail could not be
recognised as a polynomial on all of `[T₀, ∞)`, which is exactly the step that contradicts
`hnp`.  It holds for every real algebraic branch, and is supplied to the caller
`puiseux_tail_of_root_growth` via the new lemma `real_branch_analytic` (the standard fact
"a `C^∞` root of a monic polynomial family is real-analytic", recorded as an honest `sorry`).

Note on the exponent condition `∀ i : ℕ, s ≠ (i : ℝ)`: this says `s` is not a *natural*
number.  A negative integer exponent is allowed, so e.g. `g = √(x²+1)` (Puiseux expansion
`x + ½x⁻¹ − ⅛x⁻³ + …`) is handled with `s = -1` — non-polynomiality (`hnp`), not ramification,
is exactly the right hypothesis.

## New general infrastructure (`InverseGalois/LaurentInfra.lean`), all `sorry`-free

* `analytic_taylor_remainder_bound` — Taylor expansion with an analytic (locally bounded)
  remainder, scalar complex case.
* `iteratedDeriv_im_zero_of_real_on_pos` — Schwarz reflection: an analytic function on a disk
  centred at `0` that is real on `(0, r)` has real Taylor coefficients at `0`.

## New setup infrastructure (`InverseGalois/PuiseuxTail.lean`), all `sorry`-free

* `laurent_cpow_term`, `laurent_sphere_identity` — `cpow` algebra turning a `w`-Laurent
  expansion (`w = z⁻¹^{1/e}`) into a `z`-Puiseux expansion with real exponents `(Kf-m)/e`.
* `laurent_G_poly_of_vanishing` — an analytic function with vanishing high Taylor
  coefficients equals its Taylor polynomial.
* `laurent_tail_term_bound` — `‖z^σ‖ ≤ 2^{|s'|} x^{s'}` on `sphere x (x/2)` for `σ ≤ s'`.
* `laurent_coeff_real` — reality of the removable-extension coefficients (via reflection).
* `laurent_H_expansion_of_G` — the order-`n` on-sphere Puiseux expansion of `H` with a
  bounded remainder.
* `laurent_nonnat_exp` — non-polynomiality (`hnp`) yields a non-natural exponent with a
  nonzero coefficient.
* `eq_poly_of_tail_of_analytic` — analytic on `Ioi T₀` + equal to a polynomial on a tail ⇒
  equal on `[T₀, ∞)`.
* `laurentPoly` / `laurentI` / `laurentA` + `laurent_principal_eq` — the finite Puiseux
  principal part reassembles the order-`n` partial sum.

## Decomposition of `monodromy_ramification_index` (new)

`monodromy_ramification_index` is **no longer a `sorry`**: it is now assembled from two
pieces, isolating the genuinely deep content from the provable bookkeeping.

* `ramified_root_section` — the *deep* monodromy core (the single remaining `sorry` in the
  file).  It produces the ramification index `e`, a punctured-disk radius `ρ`, a threshold
  `Tr`, and a single-valued **holomorphic** `F` on `{ w | 0 < ‖w‖ < ρ }` such that
  * `F w` is a genuine root of the specialised family at `z = (w⁻¹) ^ e` (covering-space
    relation pulled back through `w ↦ w⁻ᵉ`), and
  * `H z = F (z⁻¹ ^ (1/e))` on the tail spheres.
  It carries **no** growth/pole data — that is now derived separately.  This is the
  fundamental group of the annulus at infinity acting on the fibre of the covering
  `rootProj` (`InverseGalois/BranchAnalytic.lean`), producing the ramification index; the
  convergent Newton–Puiseux / monodromy theory of algebraic functions is not in Mathlib.

* `root_pole_bound` — **proved, `sorry`-free**.  Any `F` that is, at each `w` of a punctured
  disk of radius `ρ ≤ 1`, a root of the *monic* specialised family at `z = (w⁻¹) ^ e`
  automatically satisfies a finite-order pole bound `‖F w‖ ≤ Cf / ‖w‖ ^ Kf`.  This is the
  Cauchy root bound (`cauchy_root_bound_max`) transported through the covering `w ↦ w⁻ᵉ`
  (`‖z‖ = ‖w‖^{-e}`), with `Kf = e · N` where `N` bounds the degrees of the coefficient
  polynomials.  It replaces what used to be folded into the deep `sorry`.

`monodromy_ramification_index` itself is proved glue: it derives `1 ≤ P.natDegree` (P has a
complex root), invokes `ramified_root_section`, shrinks `ρ` to `≤ 1`, and applies
`root_pole_bound`.

## Remaining `sorry`s in the file

* `ramified_root_section` — the deep monodromy / ramification-index core (see above); the
  sole remaining `sorry` in the file.

(`real_branch_analytic` is proved; its docstring text mentioning `sorry` is stale prose.)

Thus the "convergent Laurent/Puiseux with growth control" half is fully formalised, the
finite-order pole bound is now proved, and the only deep residual behind
`puiseux_tail_of_root_growth` is the monodromy input `ramified_root_section`.

## Update: `ramified_root_section` factored through a proved separable radical reduction

`ramified_root_section` is **no longer a `sorry`** — it is now proved glue built from two
pieces:

* `ComplexSeparableReduction.exists_complex_separable_reduction`
  (new file `InverseGalois/ComplexSeparableReduction.lean`) — **proved and `sorry`-free**
  (axioms: only `propext`, `Classical.choice`, `Quot.sound`).  This is the complex/integer
  analogue of `SmoothSeparableReduction.exists_smooth_separable_reduction_real`: for a monic
  `P : ℤ[x][Y]` of positive `Y`-degree, its radical `Q := radical P` in the UFD `ℤ[x][Y]` is
  monic, divides `P`, has the same roots under every complex specialisation
  `·.map (evalIntPolyComplex z)`, and is *separable* on an annulus `{ z | B < ‖z‖ }`.
  Supporting lemmas (all proved): `radical_monic_int`, `dvd_radical_pow_int`,
  `squarefree_map_frac_int`, `exists_bezout_of_squarefree_int`, `roots_radical_iff`.

* `separable_ramified_root_section` — the pure covering-space / monodromy core, now with
  separability supplied as a **hypothesis** (so `DorgeBauer.rootProj` is a genuine covering
  map over the annulus).  This is the remaining `sorry`: the fundamental group of the annulus
  acting on the fibre, the ramification index `e`, and the `e`-fold-cover trivialisation
  producing the single-valued holomorphic `F`.  This convergent Newton–Puiseux / monodromy
  theory is not available in Mathlib.

`ramified_root_section` derives `1 ≤ P.natDegree`, invokes the reduction to get the separable
radical family `Q`, enlarges the threshold so the tail balls lie in the annulus, transports
the root hypothesis `H`-is-a-root from `P` to `Q` (via `roots_radical_iff`), applies
`separable_ramified_root_section`, and transports the resulting root property back from `Q`
to `P`.

Net effect: the algebraic squarefree-reduction half of the old deep `sorry` is now fully
formalised; the sole remaining deep residual behind `puiseux_tail_of_root_growth` is the
pure covering-space monodromy input `separable_ramified_root_section`.

## Update: `separable_ramified_root_section` is now proved (chain fully `sorry`-free)

The last deep residual, `separable_ramified_root_section` (the pure covering-space / monodromy
core), is now **proved**.  Consequently `ramified_root_section`,
`monodromy_ramification_index`, and `puiseux_tail_of_root_growth` are all transitively
`sorry`-free (axioms: only `propext`, `Classical.choice`, `Quot.sound`).

The monodromy argument was formalised via the universal cover of the annulus at infinity
`U = {z | B < ‖z‖}` by the right half-plane `P = {ζ | Real.log B < ζ.re}` through
`ζ ↦ Complex.exp ζ`, in a new file `InverseGalois/RamifiedSection.lean` (all lemmas proved,
`sorry`-free):

* `branch_unique_on_connected` / `branch_unique_on_connected_comp` — uniqueness of a
  continuous root branch on a preconnected separable domain (identity / with substitution),
  by a clopen argument through `complex_branch_at_simple_root_unique`.
* `root_comp_holomorphic` — a continuous root of a separable family pulled back through a
  holomorphic substitution is holomorphic (local implicit-function branches).
* `exists_exp_lift` — the covering-space lift of `exp` (Mathlib's
  `IsCoveringMapOn.existsUnique_continuousMap_lifts`) gives a continuous single-valued root
  branch `g` on `P`.
* `exists_periodic_exp_lift` — pigeonhole on the finite fibre + lift uniqueness yields the
  ramification index `e ≥ 1` with `g` of period `2πi·e`.
* `periodic_log_comp_continuous` — `w ↦ g (-(e)·log w)` is continuous on the punctured disk
  (the two complementary log-cut branches glue by periodicity).
* `cpow_neg_e_log` — the substitution identity `-(e)·log (z⁻¹ ^ (1/e)) = log z` on the right
  half-plane.
* `branch_match_real_ray` / `branch_match_tail` — `H = g ∘ log` on the ball centres and hence
  on the tail spheres (uniqueness of continuation + continuity up to the boundary).

`separable_ramified_root_section` in `PuiseuxTail.lean` is now pure assembly on top of these.

(Also fixed a latent, build-cache-masked type error in `monodromy_ramification_index`:
`Nat.le_zero.mp` on a `_ < 1` hypothesis, replaced by `Nat.lt_one_iff.mp`.)
