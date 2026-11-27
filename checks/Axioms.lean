/-
Prints the statements `TheoremSFin`, `TheoremSFin'` (finite model), `TheoremSInf`, `TheoremSInf'`
(countable model) and `TheoremSMeasGen`, `TheoremSMeasGen'`, `TheoremSMeas`, `TheoremSMeas'` (measurable
outcome spaces), checks that `theoremSFin`, `theoremSFin'`, `theoremSInf`, `theoremSInf'`, `theoremSMeasGen`,
`theoremSMeasGen'`, `theoremSMeas` and `theoremSMeas'` prove them, and that `historyExists` and
`historyUnique` prove `HistoryExists` and `HistoryUnique`, and prints the axioms of all ten proofs. Run
after `lake build` with

    lake env lean checks/Axioms.lean

The expected axioms are `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
-/
import TheoremS.Statement
import TheoremS.Bound
import TheoremS.Inf.Statement
import TheoremS.Inf.Bound
import TheoremS.Meas.Statement
import TheoremS.Meas.Hist
import TheoremS.Meas.Bound

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

#print Meas.TheoremSMeasGen
#print Meas.TheoremSMeasGen'
#print Meas.TheoremSMeas
#print Meas.TheoremSMeas'

example : Meas.TheoremSMeasGen := Meas.theoremSMeasGen
example : Meas.TheoremSMeasGen' := Meas.theoremSMeasGen'
example : Meas.TheoremSMeas := Meas.theoremSMeas
example : Meas.TheoremSMeas' := Meas.theoremSMeas'
example : Meas.HistoryExists := Meas.historyExists
example : Meas.HistoryUnique := Meas.historyUnique

#print axioms Meas.theoremSMeasGen
#print axioms Meas.theoremSMeasGen'
#print axioms Meas.theoremSMeas
#print axioms Meas.theoremSMeas'
#print axioms Meas.historyExists
#print axioms Meas.historyUnique
