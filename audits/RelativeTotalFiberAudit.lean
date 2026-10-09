import Quillen.Waldhausen.Fibration.AllWeak.TotalFiberSquare
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.TotalFiber,
    `Quillen.Waldhausen.Fibration.AllWeak.TotalFiberSquare]
  let mut counts : Array Nat := #[0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (· + 1)
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing defining module {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless counts == #[15,16] do throwError "Unexpected original counts {counts}"
  logInfo m!"Audited all original total-fiber comparison origins: {counts}"
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Topology Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)
example : RelativeRows.totalFiberInclusion N ≫ TheoremA.diagonalMap (RelativeRows.tailSRows N) =
    SSet.const (RelativeRows.ordinaryTotalZeroVertex (acyclicStructure N)) :=
  RelativeRows.totalFiberInclusion_tail N
example : RelativeRows.totalTailMap N =
    (SSet.toTop.map (TheoremA.diagonalMap (RelativeRows.tailSRows N))).hom := rfl
example (x : V.Delooping) :
    RelativeRows.totalTailMap N (SSet.toTop.map (RelativeRows.totalFiberInclusion N) x) =
      RelativeRows.ordinaryTotalBasepoint (acyclicStructure N) :=
  RelativeRows.totalTailMap_totalFiberInclusion N x
example (x : V.Delooping) : (RelativeRows.totalTailFiberComparison N x).1.1 =
    SSet.toTop.map (RelativeRows.totalFiberInclusion N) x := rfl
example (x : V.Delooping) : (RelativeRows.totalTailFiberComparison N x).1.2 =
    ContinuousMap.const unitInterval (RelativeRows.ordinaryTotalBasepoint (acyclicStructure N)) := rfl
example (x : V.Delooping) (t : unitInterval) : (RelativeRows.totalTailFiberComparison N x).1.2 t =
    RelativeRows.ordinaryTotalBasepoint (acyclicStructure N) := rfl
example : RelativeRows.totalTailFiberComparison N V.kBasepoint =
    HomotopyFiber.basepoint (RelativeRows.totalTailMap N)
      (RelativeRows.ordinaryTotalBasepoint (acyclicStructure N)) (RelativeRows.totalBasepoint N)
      (RelativeRows.totalTailMap_basepoint N) := RelativeRows.totalTailFiberComparison_basepoint N
example (W : Structure C) : (AllWeak.ordinaryTotalHomeomorph W : C(
    |TheoremA.diagonalSSet (RelativeRows.ordinarySRows (acyclicStructure (AllWeak.nested W)))|,
    |TheoremA.diagonalSSet (RelativeRows.ordinarySRows W)|)) =
    (SSet.toTop.map (AllWeak.ordinaryDiagonalIso W).hom).hom := rfl
example (W : Structure C) :
    AllWeak.ordinaryTotalInclusionMap W
      (RelativeRows.ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested W))) =
        RelativeRows.ordinaryTotalBasepoint W := AllWeak.ordinaryTotalInclusionMap_basepoint W
example : (AllWeak.ordinaryTotalInclusionMap (acyclicStructure N)).comp
    (RelativeRows.totalTailMap (AllWeak.nested (acyclicStructure N))) =
      (RelativeRows.totalTailMap N).comp (AllWeak.relativeTotalInclusionMap N) :=
  AllWeak.relativeTotalInclusion_tail N
example : (AllWeak.relativeTailFiberMap N).comp
    (RelativeRows.totalTailFiberComparison (AllWeak.nested (acyclicStructure N))) =
      (RelativeRows.totalTailFiberComparison N).comp (acyclicInclusionMap N) :=
  AllWeak.relativeTailFiberMap_totalTailFiberComparison N
example (z : HomotopyFiber (RelativeRows.totalTailMap (AllWeak.nested (acyclicStructure N)))
    (RelativeRows.ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested (acyclicStructure N))))) :
    (AllWeak.relativeTailFiberMap N z).1.1 = AllWeak.relativeTotalInclusionMap N z.1.1 := rfl
example (z : HomotopyFiber (RelativeRows.totalTailMap (AllWeak.nested (acyclicStructure N)))
    (RelativeRows.ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested (acyclicStructure N))))) :
    (AllWeak.relativeTailFiberMap N z).1.2 =
      (AllWeak.ordinaryTotalInclusionMap (acyclicStructure N)).comp z.1.2 := rfl
example (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    (AllWeak.relativeTailFiberMap N
      (RelativeRows.totalTailFiberComparison (AllWeak.nested (acyclicStructure N)) x)).1.2 t =
      RelativeRows.ordinaryTotalBasepoint (acyclicStructure N) :=
  AllWeak.ordinaryTotalInclusionMap_basepoint (acyclicStructure N)
example (W : Structure C) :
    RelativeRows.ordinaryTotalZeroVertex W =
      zeroSimplex (QuotientRows.waldhausenStructure W ⦋0⦌).cof
        (QuotientRows.waldhausenStructure W ⦋0⦌).weq
        (QuotientRows.zero W ⦋0⦌) (QuotientRows.isZero W ⦋0⦌) (op ⦋0⦌) := rfl
