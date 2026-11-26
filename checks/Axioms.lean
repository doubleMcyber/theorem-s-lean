/-
Prints the statements `TheoremSFin` and `TheoremSFin'`, checks that `theoremSFin` and `theoremSFin'` prove
them, and prints the axioms they depend on. Run after `lake build` with

    lake env lean checks/Axioms.lean

The expected axioms are `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
-/
import TheoremS.Statement
import TheoremS.Bound

open TheoremS

#print TheoremSFin
#print TheoremSFin'

example : TheoremSFin := theoremSFin
example : TheoremSFin' := theoremSFin'

#print axioms theoremSFin
#print axioms theoremSFin'
