import Quillen.Waldhausen.Fibration.AllWeak.CanonicalFiberFactorization
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.Waldhausen.Approximation.Properties
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.Fibration.AllWeak.CanonicalFiberFactorization
  let mut count := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count > 0 do throwError "Missing source origins"
  logInfo m!"Audited all original canonical-fiber-factorization origins: {count}"
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Topology
universe u v
section Generic
variable {C : Type u} [Category.{v} C] (W : Structure C)
example (x : W.Delooping) (t : unitInterval) :
    AllWeak.changeWeakNullhomotopy W (t,x) =
      AllWeak.contraction W (t,changeWeakMap (AllWeak.nested W) x) := rfl
example (x : W.Delooping) : (AllWeak.changeWeakFiberLift W x).1.1 = x := rfl
example (x : W.Delooping) (t : unitInterval) :
    (AllWeak.changeWeakFiberLift W x).1.2 t =
      AllWeak.contraction W (t,changeWeakMap (AllWeak.nested W) x) := rfl
example : (AllWeak.changeWeakFiberLiftEquiv W).toFun = AllWeak.changeWeakFiberLift W := rfl
example : (AllWeak.changeWeakFiberLiftEquiv W).invFun =
    HomotopyFiber.projection (changeWeakMap (AllWeak.nested W))
      (AllWeak.waldhausenStructure W).kBasepoint := AllWeak.changeWeakFiberLiftEquiv_invFun W
example : (HomotopyFiber.projection (changeWeakMap (AllWeak.nested W))
    (AllWeak.waldhausenStructure W).kBasepoint).comp (AllWeak.changeWeakFiberLift W) =
      ContinuousMap.id _ := rfl
example : AllWeak.changeWeakFiberLift W W.kBasepoint =
    HomotopyFiber.basepoint (changeWeakMap (AllWeak.nested W))
      (AllWeak.waldhausenStructure W).kBasepoint W.kBasepoint
        (changeWeakMap_basepoint (AllWeak.nested W)) := AllWeak.changeWeakFiberLift_basepoint W
example (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (AllWeak.changeWeakFiberLift W)
      (x := W.kBasepoint) (AllWeak.changeWeakFiberLift_basepoint W)) :=
  AllWeak.changeWeakFiberLift_bijective W n
example : Function.Bijective
    (homotopyGroupMap (N := Fin 0) (AllWeak.changeWeakFiberLift W)
      (x := W.kBasepoint) (AllWeak.changeWeakFiberLift_basepoint W)) :=
  AllWeak.changeWeakFiberLift_bijective W 0
end Generic
section Canonical
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]
example : (AllWeak.acyclicFiberSquareMap N).comp
    (AllWeak.changeWeakFiberLift (acyclicStructure N)) = canonicalFiberMap N :=
  AllWeak.acyclicFiberSquareMap_changeWeakFiberLift N
example (x : (acyclicStructure N).Delooping) :
    (AllWeak.acyclicFiberSquareMap N
      (AllWeak.changeWeakFiberLift (acyclicStructure N) x)).1.1 = acyclicInclusionMap N x := rfl
example (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    (AllWeak.acyclicFiberSquareMap N
      (AllWeak.changeWeakFiberLift (acyclicStructure N) x)).1.2 t =
      acyclicNullhomotopy N (t,x) := AllWeak.contraction_acyclicNullhomotopy N t x
example (z : HomotopyFiber (changeWeakMap (AllWeak.nested (acyclicStructure N)))
    (AllWeak.waldhausenStructure (acyclicStructure N)).kBasepoint) (t : unitInterval) :
    (AllWeak.acyclicFiberSquareMap N z).1.2 t =
      deloopingMap (AllWeak.acyclicInclusion_exact N) (z.1.2 t) := rfl
example : AllWeak.acyclicFiberSquareMap N
    (HomotopyFiber.basepoint (changeWeakMap (AllWeak.nested (acyclicStructure N)))
      (AllWeak.waldhausenStructure (acyclicStructure N)).kBasepoint (acyclicStructure N).kBasepoint
      (changeWeakMap_basepoint (AllWeak.nested (acyclicStructure N)))) =
    HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
      (changeWeakMap_basepoint N) := AllWeak.acyclicFiberSquareMap_basepoint N
example : (canonicalFiberMap N).Homotopic
    ((AllWeak.acyclicFiberSquareMap N).comp (AllWeak.changeWeakFiberLift (acyclicStructure N))) := by
  rw [AllWeak.acyclicFiberSquareMap_changeWeakFiberLift]
end Canonical
section Scheme
open GilletWaldhausen AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
local instance fiberFactorizationSchemeSaturated (X : Scheme.{u}) :
    (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq.HasTwoOutOfThreeProperty :=
  complexSubcategory_saturated _
example (X : Scheme.{u}) :
    (AllWeak.acyclicFiberSquareMap (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))).comp
      (AllWeak.changeWeakFiberLift
        (acyclicStructure (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)))) =
      canonicalFiberMap (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) :=
  AllWeak.acyclicFiberSquareMap_changeWeakFiberLift _
end Scheme
