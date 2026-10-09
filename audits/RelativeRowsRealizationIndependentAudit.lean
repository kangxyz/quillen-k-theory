import Quillen.Waldhausen.Fibration.RelativeRows.Realization
import Quillen.Waldhausen.Fibration.RelativeRows.LocalFiber
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.Realization, `Quillen.Waldhausen.Fibration.RelativeRows.LocalFiber]
  let mut count : Nat := 0
  for origin in targets do
    let mut subtotal : Nat := 0
    for (name, _) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless env.header.moduleNames[index.toNat]! == origin do continue
      count := count + 1
      subtotal := subtotal + 1
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{origin}: {name} depends on unsupported assumption {dependency}"
      logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
    logInfo m!"ORIGIN_COUNT {origin}: {subtotal}"
  unless count == 24 do throwError "Expected 24 relative-row-realization origins, got {count}"
  unless count == 24 do throwError "Expected24 relative realization origins, got {count}"
  logInfo m!"Audited all {count} relative-row-realization declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows
section Categorical
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (n : SimplexCategory) [HasBinaryCoproducts (Obj N n)]
example : Additivity.sumFunctor (tailQuotientFunctor N n) (cutFunctor N n) ≅
    firstTail N n ⋙ splitFunctor N n := internalSumSplitIso N n
end Categorical
section Common
variable {C : Type u} [Category.{u} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (n : SimplexCategory)
example : ContinuousMap.HomotopyEquiv (waldhausenStructure N n).Delooping
    (ExtensionCategory.productStructure V (QuotientRows.waldhausenStructure (acyclicStructure N) n)).Delooping :=
  firstTailRealizationHomotopyEquiv N n
example : (firstTailRealizationHomotopyEquiv N n).toFun = (deloopingMap (firstTail_exact N n)).hom :=
  firstTailRealizationHomotopyEquiv_toFun N n
example : (firstTailRealizationHomotopyEquiv N n).invFun = splitRealizationMap N n :=
  firstTailRealizationHomotopyEquiv_invFun N n
example : ContinuousMap.HomotopyEquiv |(relativeSRows N).obj (op n)|
    |sSet V.cof V.weq ⊗ (ordinarySRows (acyclicStructure N)).obj (op n)| :=
  firstTailSSetRealizationHomotopyEquiv N n
example : (firstTailSSetRealizationHomotopyEquiv N n).toFun =
    (SSet.toTop.map (firstTailSSet N n)).hom := firstTailSSetRealizationHomotopyEquiv_toFun N n
example : firstTailSSet N n ≫ snd _ _ = (tailSRows N).app (op n) := firstTailSSet_snd N n
example : firstTailSSet N n ≫ fst _ _ = sSetMap (first_exact N n) := firstTailSSet_fst N n
example : (fiberSRows N).app (op n) ≫ firstTailSSet N n =
    ProductRealization.vertexSection (sSet V.cof V.weq)
      ((ordinarySRows (acyclicStructure N)).obj (op n)) (tailZeroVertex N n) := fiber_firstTailSSet N n
example (x : |(relativeSRows N).obj (op n)|) :
    (firstTailSSetRealizationHomotopyEquiv N n).toFun x = SSet.toTop.map (firstTailSSet N n) x := by
  rw [firstTailSSetRealizationHomotopyEquiv_toFun]
example [HasBinaryCoproducts (Obj N n)] :
    ((deloopingMap (splitFunctor_exact N n)).hom.comp (deloopingMap (firstTail_exact N n)).hom).Homotopic
      (ContinuousMap.id (waldhausenStructure N n).Delooping) := firstTail_split_homotopic N n
example [HasBinaryCoproducts (Obj N n)] :
    ((deloopingMap (firstTail_exact N n)).hom.comp (deloopingMap (splitFunctor_exact N n)).hom).Homotopic
      (ContinuousMap.id (ExtensionCategory.productStructure V
        (QuotientRows.waldhausenStructure (acyclicStructure N) n)).Delooping) := split_firstTail_homotopic N n
example : rowFiberProjection N n = (SSet.toTop.map ((tailSRows N).app (op n))).hom := rowFiberProjection_eq N n
example (x : |sSet V.cof V.weq|) : (rowFiberInclusion N n x).1.1 =
    SSet.toTop.map ((fiberSRows N).app (op n)) x := rfl
example (x : |sSet V.cof V.weq|) : (rowFiberInclusion N n x).1.2 =
    ContinuousMap.const _ (realizationPoint (tailZeroVertex N n)) := rfl
example (x : |sSet V.cof V.weq|) (k : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin k) (rowFiberInclusion N n) (x := x) rfl) :=
  rowFiberInclusion_bijective N n x k
example (x : |sSet V.cof V.weq|) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (rowFiberInclusion N ⦋0⦌) (x := x) rfl) :=
  rowFiberInclusion_bijective N ⦋0⦌ x 0
end Common
end Quillen.Waldhausen.Fibration.RelativeRows
