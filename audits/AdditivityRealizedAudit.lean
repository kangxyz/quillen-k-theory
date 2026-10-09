import Lean.Util.CollectAxioms
import Quillen.Waldhausen.Additivity.RealizedAdditivity
import Quillen.Waldhausen.GilletWaldhausen.TruncationCofibrationSequence

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[
    `Quillen.Waldhausen.Additivity.CofiberEndpoint,
    `Quillen.Waldhausen.Additivity.CofibrationSequence,
    `Quillen.Waldhausen.Additivity.CoproductAlgebra,
    `Quillen.Waldhausen.Additivity.DeformationMap,
    `Quillen.Waldhausen.Additivity.EndpointFamilies,
    `Quillen.Waldhausen.Additivity.EndpointHomotopies,
    `Quillen.Waldhausen.Additivity.EndpointNaturality,
    `Quillen.Waldhausen.Additivity.IntervalArrows,
    `Quillen.Waldhausen.Additivity.IntervalEndpoints,
    `Quillen.Waldhausen.Additivity.MixedDiagrams,
    `Quillen.Waldhausen.Additivity.PushoutCofibrations,
    `Quillen.Waldhausen.Additivity.PushoutEndpoints,
    `Quillen.Waldhausen.Additivity.PushoutFunctor,
    `Quillen.Waldhausen.Additivity.PushoutInterchange,
    `Quillen.Waldhausen.Additivity.PushoutPreservation,
    `Quillen.Waldhausen.Additivity.RealizationHomotopy,
    `Quillen.Waldhausen.Additivity.RealizedAdditivity,
    `Quillen.Waldhausen.Additivity.SplitSequence,
    `Quillen.Waldhausen.Additivity.SumDiagrams,
    `Quillen.Waldhausen.Additivity.ZeroFactorization]
  let mut count : Nat := 0
  let mut modules : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    modules := modules.insert origin
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless modules.size == wanted.size do
    throwError "Expected {wanted.size} defining modules, found {modules.size}"
  logInfo m!"Audited all {count} declarations across {modules.size} frozen additivity modules."

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.Additivity
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
  {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

example : (deloopingMap hs.exactG).hom.Homotopic
    (deloopingMap (sumFunctor_isExact V W hs.exactH hs.exactF)).hom :=
  deloopingMap_additivity V W a b hs

example : (deloopingMap hs.exactG).hom.Homotopy
    (deloopingMap (sumFunctor_isExact V W hs.exactH hs.exactF)).hom :=
  additivityHomotopy V W a b hs

namespace ActualTruncationConsumer
open GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  [(abelianExactStructure A).IsExtensionClosed P]

def truncationAdditivityHomotopy (n : ℤ) := by
  let V := ofExactCategory (boundedAcyclicExactStructure P)
  letI := hasBinaryCoproducts V
  exact additivityHomotopy V V (boundedAcyclicTruncationInclusion P n)
    (boundedAcyclicTruncationProjection P n) (boundedAcyclicTruncation_isCofibrationSequence P n)

end ActualTruncationConsumer
