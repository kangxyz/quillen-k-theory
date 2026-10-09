import Quillen.Waldhausen.GilletWaldhausen.FiniteTermKEquivalence
import Quillen.PerfectComplexes.Strict
set_option pp.universes true in
#check @Quillen.Waldhausen.GilletWaldhausen.finiteTermKEquiv
open Lean in
run_cmd do
 let env ← getEnv
 let some info := env.find? `Quillen.Waldhausen.GilletWaldhausen.finiteTermKEquiv | throwError "missing"
 logInfo m!"Level parameters: {info.levelParams}"
