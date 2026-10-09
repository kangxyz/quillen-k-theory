import Lean.Util.CollectAxioms
import Quillen.Waldhausen.Additivity.BasedAdditivity
import Quillen.Waldhausen.GilletWaldhausen.TruncationCofibrationSequence

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[
    `Quillen.Waldhausen.Additivity.BasedAdditivity,
    `Quillen.Waldhausen.Additivity.BasedHomotopyTools,
    `Quillen.Waldhausen.Additivity.DiagonalKMap,
    `Quillen.Waldhausen.Additivity.DiagramIso,
    `Quillen.Waldhausen.Additivity.MixedEndpointHomotopy,
    `Quillen.Waldhausen.Additivity.NormalizeFunctor,
    `Quillen.Waldhausen.Additivity.NormalizedDeformationMap,
    `Quillen.Waldhausen.Additivity.NormalizedEndpointFamilies,
    `Quillen.Waldhausen.Additivity.NormalizedEndpointHomotopies,
    `Quillen.Waldhausen.Additivity.NormalizedMixedDiagrams,
    `Quillen.Waldhausen.Additivity.NormalizedMixedHomotopy,
    `Quillen.Waldhausen.Additivity.NormalizedPushout,
    `Quillen.Waldhausen.Additivity.NormalizedSumMap,
    `Quillen.Waldhausen.Additivity.NormalizedZeroMaps,
    `Quillen.Waldhausen.Additivity.SubdivisionBasepoint]
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
  unless count == 148 do
    throwError "Expected the frozen count148, found {count}"
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

example (n : ℕ) :
    KMap hs.exactG n = KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n :=
  KMap_additivity V W a b hs n

example :
    ((realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)).comp
      (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))).HomotopyRel
      (realizedDiagonalMap (normalizedSumMap V W hs.exactH hs.exactF))
      {subdivisionBasepoint V} :=
  subdividedBasedAdditivityHomotopy V W a b hs

example (n : ℕ) :
    KMap hs.exactG n = piMap n (deloopingMap hs.exactG.rebase).hom
      (rebasedDeloopingMap_basepoint V W hs.exactG) :=
  KMap_eq_rebased_piMap V W hs.exactG n

namespace ActualTruncationConsumer
open GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  [(abelianExactStructure A).IsExtensionClosed P]

theorem truncationCanonicalKMapAdditivity (n : ℤ) (k : ℕ) :
    let V := ofExactCategory (boundedAcyclicExactStructure P)
    letI := hasBinaryCoproducts V
    let hs := boundedAcyclicTruncation_isCofibrationSequence P n
    KMap hs.exactG k = KMap (sumFunctor_isExact V V hs.exactH hs.exactF) k := by
  let V := ofExactCategory (boundedAcyclicExactStructure P)
  let := hasBinaryCoproducts V
  exact KMap_additivity V V (boundedAcyclicTruncationInclusion P n)
    (boundedAcyclicTruncationProjection P n) (boundedAcyclicTruncation_isCofibrationSequence P n) k

end ActualTruncationConsumer
