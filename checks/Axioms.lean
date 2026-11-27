/-
Prints the statements `TheoremSFin`, `TheoremSFin'` (finite model) and `TheoremSInf`, `TheoremSInf'`
(countable model), checks that `theoremSFin`, `theoremSFin'`, `theoremSInf` and `theoremSInf'` prove them,
and prints the axioms they depend on. Run after `lake build` with

    lake env lean checks/Axioms.lean

The expected axioms are `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
-/
import TheoremS.Statement
import TheoremS.Bound
import TheoremS.Inf.Statement
import TheoremS.Inf.Bound

open TheoremS

#print TheoremSFin
#print TheoremSFin'

example : TheoremSFin := theoremSFin
example : TheoremSFin' := theoremSFin'

#print axioms theoremSFin
#print axioms theoremSFin'

#print Inf.TheoremSInf
#print Inf.TheoremSInf'

example : Inf.TheoremSInf := Inf.theoremSInf
example : Inf.TheoremSInf' := Inf.theoremSInf'

#print axioms Inf.theoremSInf
#print axioms Inf.theoremSInf'
