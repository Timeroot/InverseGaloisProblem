# Comparator challenge

A [leanprover/comparator](https://github.com/leanprover/comparator) challenge for the
Riemann Existence Theorem as proven in this development:

> **Fix `r` distinct points of the affine line over `ℚ̄`.  Finite Galois covers of `ℙ¹`
> branched only over those points correspond to generating `r`-tuples with product `1` in a
> finite group** — a tuple builds a cover with those branch cycles (`ret_existence`), and
> every such cover has such a tuple of branch cycles (`ret_completeness`).  In particular
> every finite group is the Galois group of a finite Galois extension of `ℚ̄(T)`
> (`geometric_igp`).

| file | content |
| --- | --- |
| `Challenge.lean` | the three statements, with `sorry`, and only the definitions needed to state them |
| `Solution.lean` | the same definitions verbatim, then the proofs |
| `config.json` | the comparator configuration |

`Challenge.lean` is self-contained: it imports nothing from `InverseGalois`, and builds from
scratch, in about 200 lines,

* the inversion `T ↦ 1/T` of `ℚ̄(T)`, as the substitution of the transcendental element `T⁻¹`
  for the parameter — this is what reaches the point at infinity;
* `Cover`, a finite Galois extension `M / ℚ̄(T)` carrying its integral model
  `B = integralClosure ℚ̄[X] M`;
* inertia at the point `t`, as the inertia group (`Ideal.inertia`) of a maximal ideal of `B`
  lying over `(X - t)`, and its *distinguished* form, where the deck transformation generates
  that inertia group rather than merely belonging to it;
* unramifiedness outside a set of points, and unramifiedness at infinity, the latter through
  the type synonym `Twist φ M` — the field `M` with the base acting through the coordinate
  change `φ`.

The three theorems there are the development's `Rigidity.RET.geomRET` (in
`InverseGalois/Rigidity/RET/Completeness.lean`, statement in `RET/GeomRET.lean`) and
`isGeometricGaloisCover_of_finite` (`RET/ExistenceCovers.lean`), unfolded to their
definitions.

`Solution.lean` repeats those definitions unchanged — comparator requires every constant
reachable from the statement to be identical on both sides — and then identifies them with
the development's.  The identification is `rfl` throughout: `Cover` is
`Rigidity.RET.LineCover` field for field, `Cover.model` is `GeomAKLB.Bring`, `Cover.place` is
`GeomAKLB.placeP`, `Twist` is `Rigidity.RET.Twist`, and `ratFuncInv` is
`Rigidity.RET.invSubst`.

One wrinkle: comparator compares the two sides constant-for-constant, and the development names
shortcut instances (`InverseGalois/Core/InstanceShortcuts.lean`) for structures whose generic
instance search is slow.  Each is `inferInstance`, so the structure is unchanged, but the term
elaboration produces is not — with `InverseGalois` imported, `Cover.IsInertiaGenAt` would pick up
`integralClosure.algebraShortcut` where the challenge has `Subalgebra.algebra`.  `Solution.lean`
therefore switches those instances off with `attribute [-instance]` before repeating the
definitions.

Both modules are `lean_lib`s in the root `lakefile.toml`, so they share the built Mathlib.
Neither is a default target: `lake build` must stay `sorry`-free, and `Challenge` is not.

## Running it

Comparator needs its own binary plus `lean4export`.  `lean4export` must be built against
**this project's** toolchain (`v4.28.0`) so that it can read the project's `.olean`s; the
revision to use is the one comparator pins (`lake-manifest.json`), so that the export format
matches comparator's parser.  Comparator itself can be built with whatever toolchain its own
`lean-toolchain` asks for.

```bash
git clone https://github.com/leanprover/comparator /tmp/comparator
(cd /tmp/comparator && lake build comparator)

# lean4export at comparator's pinned revision, built against v4.28.0
git clone https://github.com/leanprover/lean4export /tmp/lean4export
cd /tmp/lean4export
git checkout "$(python3 -c "import json;print([p['rev'] for p in json.load(open('/tmp/comparator/lake-manifest.json'))['packages'] if p['name']=='lean4export'][0])")"
echo leanprover/lean4:v4.28.0 > lean-toolchain
lake build
```

Then, from the root of this repository:

```bash
lake build Challenge Solution

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- bash -c \
  'COMPARATOR_LEAN4EXPORT=/tmp/lean4export/.lake/build/bin/lean4export \
   lake env /tmp/comparator/.lake/build/bin/comparator extras/comparator/config.json'
```

which expects `landrun` on `PATH`.  On a machine without it, comparator's own
`scripts/fake-landrun.sh` runs the child processes unsandboxed:

```bash
COMPARATOR_LANDRUN=/tmp/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/tmp/lean4export/.lake/build/bin/lean4export \
lake env /tmp/comparator/.lake/build/bin/comparator extras/comparator/config.json
```

Either way the last line is

```
Your solution is okay!
```

Comparator checks that the two statements agree constant-for-constant, that the solution's
axioms are within `propext`, `Quot.sound`, `Classical.choice`, and that Lean's kernel accepts
a replay of the exported solution.  The replay is the expensive part; `Solution` reaches all
of `InverseGalois`, so allow well over the fifteen minutes a small development takes.
