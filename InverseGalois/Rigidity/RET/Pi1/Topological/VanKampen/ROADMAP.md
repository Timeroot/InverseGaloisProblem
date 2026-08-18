# Seifert–van Kampen from scratch — build roadmap

Goal: prove the topological van Kampen theorem for `π₁`, then the free-product corollary, then
apply it to close **link C** general `r` (`π₁^top(S² ∖ r pts) ≅ Γ_r`). Mathlib has NO van Kampen,
no wedge/pushout of spaces; the categorical `Limits/VanKampen.lean` is about van-Kampen *colimits*,
unrelated.

## Formulation chosen

**Groupoid functor universal property** (Ronnie Brown form) as the core — it avoids basepoint /
path-correction bookkeeping (we map *paths* to morphisms, not *loops* to group elements):

> Let `X` be a topological space, `U V : Set X` open with `U ∪ V = univ`, `W := U ∩ V`.
> For any category `H` and functors `F_U : π(U) ⥤ H`, `F_V : π(V) ⥤ H` that agree on `π(W)`
> (`F_U ∘ πₘ ι_UW = F_V ∘ πₘ ι_VW`), there is a **unique** functor `F : π(X) ⥤ H` with
> `F ∘ πₘ jU = F_U` and `F ∘ πₘ jV = F_V`.
> Equivalently: the square `π(W) → π(U); π(W) → π(V) → π(X)` is a pushout in `Cat`/`Grpd`.

Then:
- **Group form**: restrict to vertex group at `x₀ ∈ W`; when `U,V,W` path-connected, the vertex
  group at `x₀` of `π(X)` is `π₁(X,x₀)`, and the pushout of groupoids descends to a pushout of
  groups = amalgamated free product `π₁(U) *_{π₁(W)} π₁(V)`.
- **Free-product corollary**: `W` simply connected ⇒ `π₁(W)=1` ⇒ `π₁(X) ≅ π₁(U) * π₁(V)` (`Coprod`).

## The analytic core (the genuinely hard part)

1. **Path subdivision** (`Subdivision.lean`): for `γ : Path a b` in `X` and the open cover `{U,V}`,
   there is `n` and a partition `0 = t₀ < … < t_n = 1` with `γ '' [tₖ,tₖ₊₁] ⊆ U` or `⊆ V`.
   Via Lebesgue number lemma on `[0,1]` (compact metric) + uniform continuity of `γ`. Then `γ` is
   reparam-homotopic to the concatenation of its subpaths `γ.truncate tₖ tₖ₊₁`.
2. **Homotopy subdivision** (`Subdivision.lean`): for `G : [0,1]² → X` continuous, an `n×n` grid
   with each cell `[i/n,(i+1)/n]×[j/n,(j+1)/n]` mapped into `U` or `V`. Lebesgue on `[0,1]²`.

## The functor construction (`Core.lean`)

- `F.obj x := F_U x` if `x ∈ U` else `F_V x` (agree on `W`; total since `U ∪ V = univ`).
- `F.map [γ]`: subdivide `γ`, send each subpath (which lies in `U` or `V`) through `F_U`/`F_V`,
  compose. Well-defined:
  * independence of the *subdivision* (common refinement; a subpath split further composes the
    same because `F_U`/`F_V` are functors) — **medium**;
  * independence of the *homotopy class* — the **staircase argument** over the grid from homotopy
    subdivision: crossing one cell changes the path by a homotopy living in `U` (or `V`), which
    `F_U` (`F_V`) collapses; cells straddling into `W` use `F_U|W = F_V|W`. — **HARDEST**.
- Functor laws (`map_id`, `map_comp`) and the two restriction equalities `F ∘ jU = F_U` etc.
- Uniqueness: any such `F'` agrees on subpaths (each in `U` or `V`) hence on all of `π(X)`.

## Files

```
VanKampen/Subdivision.lean   -- Lebesgue → path & homotopy subdivision (analytic core)
VanKampen/Core.lean          -- the universal functor F + well-definedness + uniqueness
VanKampen/Pushout.lean       -- package as IsPushout in Cat/Grpd (statement form)
VanKampen/Group.lean         -- vertex-group descent: π₁(X) ≅ π₁(U) *_{π₁(W)} π₁(V)
VanKampen/FreeProduct.lean   -- W simply connected ⇒ π₁(X) ≅ π₁(U) * π₁(V) (Coprod)
```

Application to `Γ_r` (wedge of circles / punctured plane) is a *further* step needing a
wedge/deformation-retraction model; staged after the theorem itself.

## Beeline discipline

Stub statements first, get the file compiling with honest `sorry`s at the analytic leaves, then
fill leaves one at a time, full-building after each. Never let a `sorry` touch
`rigidity_realizable` (verify `#print axioms` = `[propext, Classical.choice, Quot.sound]`
after every full build). Docstrings never mention sorry / proof-status.
