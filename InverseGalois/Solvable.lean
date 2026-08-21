import InverseGalois.Solvable.ChiefSeries
import InverseGalois.Solvable.Nilpotent
import InverseGalois.Solvable.Wreath

/-!
# Solvable groups as Galois groups

Shafarevich's theorem states that every finite solvable group is a Galois group over `ℚ`.  Its
proof is arithmetic — it runs through embedding problems, class field theory and the
Grunwald–Wang theorem — and the *regular* analogue over `ℚ(T)` is not known even for `p`-groups.
This directory collects the group-theoretic reductions that organize the approach, each of them
free of arithmetic input and applicable to both realization predicates of the development.

* `InverseGalois.Solvable.ChiefSeries` peels a finite solvable group apart along elementary
  abelian normal subgroups, reducing the problem to embedding problems with elementary abelian
  kernel.
* `InverseGalois.Solvable.Nilpotent` assembles a finite nilpotent group from its Sylow subgroups,
  reducing the nilpotent case to `p`-groups.
* `InverseGalois.Solvable.Wreath` presents every semidirect product `A ⋊[φ] H` with `A` abelian as
  a quotient of the single regular wreath product `A ≀ᵣ H`, so that a realization of the wreath
  product realizes every split extension of `H` by `A` at once.
-/
