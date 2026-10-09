import Lean.Util.CollectAxioms
import Quillen.Topology.Realization.BisimplicialEquivalence

/-! Transitive foundation audit of every declaration from the seven-module
generic bisimplicial realization proof, including private/generated ones. -/
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Topology.Realization.MapEquivalence,
    `Quillen.Topology.Realization.BisimplicialLatching,
    `Quillen.Topology.Realization.BisimplicialLatchingIntersections,
    `Quillen.Topology.Realization.BisimplicialLatchingEquivalences,
    `Quillen.Topology.Realization.BisimplicialSkeleton,
    `Quillen.Topology.Realization.BisimplicialSkeletonAttachment,
    `Quillen.Topology.Realization.BisimplicialEquivalence]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless modules.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count = 164 do throwError "Expected frozen 164-declaration scope; audited {count}"
  logInfo m!"Audited all {count} declarations from the seven bisimplicial realization modules, including private/generated ones."

#print axioms Quillen.BisimplicialRealization.partialLatching_preimage_degeneracy
#print axioms Quillen.BisimplicialRealization.partialLatching_isPushout
#print axioms Quillen.BisimplicialRealization.latchingMap_isRealizationEquivalence
#print axioms Quillen.BisimplicialRealization.stageCoconeIsColimit
#print axioms Quillen.BisimplicialRealization.attachment_isPushout
#print axioms Quillen.BisimplicialRealization.diagonalMap_isRealizationEquivalence
#print axioms Quillen.BisimplicialRealization.diagonalRealizationHomotopyEquiv
#print axioms Quillen.BisimplicialRealization.diagonalRealizationHomotopyEquiv_toFun

noncomputable section
open CategoryTheory
open scoped Simplicial Topology
universe u

example {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (e : ∀ n, ContinuousMap.HomotopyEquiv |X.obj (Opposite.op ⦋n⦌)| |Y.obj (Opposite.op ⦋n⦌)|)
    (he : ∀ n, (e n).toFun = (SSet.toTop.map (η.app (Opposite.op ⦋n⦌))).hom) :
    (Quillen.BisimplicialRealization.diagonalRealizationHomotopyEquiv η e he).toFun =
      (SSet.toTop.map (Quillen.TheoremA.diagonalMap η)).hom := rfl

example {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (h : ∀ n, Quillen.IsRealizationEquivalence (η.app (Opposite.op ⦋n⦌))) :
    Quillen.IsRealizationEquivalence (Quillen.TheoremA.diagonalMap η) :=
  Quillen.BisimplicialRealization.diagonalMap_isRealizationEquivalence η h
