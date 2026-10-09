import Lean.Util.CollectAxioms
import Quillen.Topology.Realization.ProductFiber
import Quillen.Waldhausen.SConstruction.Connected

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`Quillen.Topology.HomotopyFiber.CompactLifting,
    `Quillen.Topology.HomotopyFiber.Product,
    `Quillen.Topology.Realization.ProductFiber,
    `Quillen.Waldhausen.SConstruction.Connected]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    seen := seen.insert origin
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 43 do throwError "Expected 43 relative-fiber topology origins, got {count}"
  unless seen.size == 4 do throwError "Missing defining module"
  logInfo m!"Audited all {count} origins of the four actual relative-fiber topology layers."

noncomputable section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Quillen
open scoped Simplicial Topology
universe u v w
section Generic
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(Y, Z)) (e : C(X, Y)) (he : Function.Injective e) (hl : HasCompactSourceLifts e) (z : Z)
example (p : HomotopyFiber (f.comp e) z) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (HomotopyFiber.sourceMap f e z) (x := p) rfl) :=
  HomotopyFiber.sourceMap_homotopyGroupMap_bijective f e he hl z p 0
example (p : HomotopyFiber (f.comp e) z) :
    (HomotopyFiber.sourceMap f e z p).1 = (e p.1.1, p.1.2) := rfl
end Generic
section ActualProduct
open ProductRealization
variable (X Y : SSet.{u}) (y : Y _⦋0⦌) (x : |X|)
example (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (fiberInclusion X Y y) (x := x) rfl) :=
  fiberInclusion_bijective X Y y x n
example : Function.Bijective
    (homotopyGroupMap (N := Fin 0) (fiberInclusion X Y y) (x := x) rfl) :=
  fiberInclusion_bijective X Y y x 0
example : (fiberInclusion X Y y x).1.2 = ContinuousMap.const _ (realizationPoint y) := rfl
example : (fiberProjection X Y (realizationPoint y)).comp (fiberInclusion X Y y) =
    ContinuousMap.id |X| := fiberProjection_inclusion X Y y
end ActualProduct
section ActualWaldhausen
open Waldhausen
variable {C : Type u} [Category.{v} C] (W : Structure C)
example : PathConnectedSpace W.Delooping := inferInstance
example (x : W.Delooping) : Path W.kBasepoint x := kBasepointPath W x
example (Z : C) (hZ : CategoryTheory.Limits.IsZero Z) :
    Joined (basepoint W.cof W.weq Z hZ) W.kBasepoint := zero_vertex_joined_basepoint W Z hZ
end ActualWaldhausen
