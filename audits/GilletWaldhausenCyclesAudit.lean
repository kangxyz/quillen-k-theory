import Lean.Util.CollectAxioms
import Quillen.Waldhausen.GilletWaldhausen.AcyclicCycles

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == `Quillen.Waldhausen.GilletWaldhausen.AcyclicCycles do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  logInfo m!"Audited all {count} cycle-closure-origin declarations, including private/generated declarations; only propext, Classical.choice, Quot.sound."

#print axioms Quillen.Waldhausen.GilletWaldhausen.cycleSequence_shortExact
#print axioms Quillen.Waldhausen.GilletWaldhausen.cycles_mem
#print axioms Quillen.Waldhausen.GilletWaldhausen.subcategoryCycleSequence_conflation

universe v u
open CategoryTheory CategoryTheory.Limits Quillen
attribute [local instance] Abelian.hasFiniteBiproducts

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    (K : CochainComplex A ℤ) (hterms : ∀ n, P (K.X n))
    (hK : K.Acyclic) (b : ℤ) (hb : ∀ n, b < n → IsZero (K.X n)) (n : ℤ) :
    P (K.cycles n) :=
  Waldhausen.GilletWaldhausen.cycles_mem P K hterms hK b hb n
