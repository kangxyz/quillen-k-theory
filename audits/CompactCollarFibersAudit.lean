import Quillen.CategoryTheory.TheoremB.CompactCollarFibers
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.CategoryTheory.TheoremB.CompactCollarFibers
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless count == 7 do throwError "Expected 7 origins, got {count}"
  logInfo m!"Audited all {count} compact collar fiber origins."
noncomputable section
open Quillen CategoryTheory
open scoped Topology unitInterval
universe u
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (q : C(F,B)) (e : ContinuousMap.HomotopyEquiv E F) (hq : HomotopyLiftingProperty q) (b : B)
  (hf : CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictMapOver (q.comp e.toFun) q e.toFun rfl b))
example : CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictFiberInclusion (q.comp e.toFun) b) :=
  HomotopyFiber.strictFiberInclusion_compactHELP_of_equiv q e hq b hf
example (K D : TopCat.{u}) [CompactSpace K] [CompactSpace D]
    (i : K ⟶ D) (hi : Quillen.TheoremA.homotopyExtensionProperty i)
    (a : C(K,{x : E // q (e.toFun x) = b}))
    (d : C(D,HomotopyFiber (q.comp e.toFun) b))
    (H : ((HomotopyFiber.strictFiberInclusion (q.comp e.toFun) b).comp a).Homotopy
      (d.comp i.hom)) :
    ∃ c : C(D,{x : E // q (e.toFun x) = b}), c.comp i.hom = a ∧
      ∃ V : ((HomotopyFiber.strictFiberInclusion (q.comp e.toFun) b).comp c).Homotopy d,
        ∀ t x,V (t,i x) = H (t,x) :=
  HomotopyFiber.strictFiberInclusion_compactHELP_of_equiv q e hq b hf K D i hi a d H
#check Quillen.DoubleCylinder.leftCollarComparisonFiber
#check Quillen.DoubleCylinder.rightCollarComparisonFiber
#check Quillen.DoubleCylinder.leftCollar_strictFiberInclusion_compactHELP
#check Quillen.DoubleCylinder.rightCollar_strictFiberInclusion_compactHELP
