import Quillen.Topology.Realization.OrdinalSubdivisionBisimplicial
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.Realization.OrdinalSubdivision,
    `Quillen.Topology.Realization.OrdinalSubdivisionSimplex,
    `Quillen.Topology.Realization.OrdinalSubdivisionRealization,
    `Quillen.Topology.Realization.OrdinalSubdivisionBisimplicial]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 89 do throwError "Expected 89 ordinary subdivision origins, got {count}"
  logInfo m!"Audited all {count} ordinary subdivision declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial
universe u
namespace Quillen.OrdinalSubdivision
example (n : SimplexCategory) : δ.obj n = Edgewise.joinObj n n := rfl
example {n m : SimplexCategory} (f : n ⟶ m) : δ.map f = Edgewise.joinMap f f := rfl
example (X : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (endpoint X).app n = X.map (first.app n.unop).op := rfl
example (n : ℕ) : ContractibleSpace |subdivision (Δ[n] : SSet.{u})| := contractibleSpace_simplex n
example (X : SSet.{u}) : ContinuousMap.HomotopyEquiv |subdivision X| |X| := realizationHomotopyEquiv X
example (X : SSet.{u}) : (realizationHomotopyEquiv X).toFun = (SSet.toTop.map (endpoint X)).hom := rfl
example {X Y : SSet.{u}} (f : X ⟶ Y) :
    (realizationHomotopyEquiv Y).toFun.comp (SSet.toTop.map (subdivisionFunctor.map f)).hom =
      (SSet.toTop.map f).hom.comp (realizationHomotopyEquiv X).toFun := realizationHomotopyEquiv_naturality f
example {X : SSet.{u}} (x : X _⦋0⦌) :
    realizationHomotopyEquiv X (realizationPoint (vertex x)) = realizationPoint x :=
  realizationHomotopyEquiv_vertex x
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (δ.op ⋙ X)| |TheoremA.diagonalSSet X| :=
  horizontalRealizationHomotopyEquiv X
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (horizontalRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (horizontalEndpoint X))).hom := rfl
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (firstIndexRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap
        (Functor.whiskerLeft (δ.op ⋙ X) endpointNatTrans))).hom := rfl
end Quillen.OrdinalSubdivision
