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
  unless count == 7 do throwError "Expected fixed7, found {count}"
  logInfo m!"FIXED7 PASSED all {count} compact collar fiber origins."
noncomputable section
open Quillen CategoryTheory
open scoped Topology unitInterval
universe u
section Generic
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

example : (HomotopyFiber.sourceMap q e.toFun b).comp
    (HomotopyFiber.strictFiberInclusion (q.comp e.toFun) b) =
    (HomotopyFiber.strictFiberInclusion q b).comp
      (HomotopyFiber.strictMapOver (q.comp e.toFun) q e.toFun rfl b) := rfl
example (x : {x : E // q (e.toFun x) = b}) :
    (HomotopyFiber.strictFiberInclusion (q.comp e.toFun) b x).val.1 = x.val := rfl
example (x : {x : E // q (e.toFun x) = b}) (s : unitInterval) :
    (HomotopyFiber.strictFiberInclusion (q.comp e.toFun) b x).val.2 s = b := rfl
example : (HomotopyFiber.sourceEquiv q e b).toFun = HomotopyFiber.sourceMap q e.toFun b := rfl
end Generic

open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Quillen.DoubleCylinder
section OriginalCollars
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TheoremA.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') (cut : unitInterval)
example (hcut : 0 < cut) (hb : HomotopyLiftingProperty b.hom)
    (y : LeftCollar f' g' sq' cut)
    (hy : CompactHomotopyExtensionLiftingProperty
      (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut y)) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y) :=
  leftCollar_strictFiberInclusion_compactHELP sq sq' a b c wf wg cut hcut hb y hy
example (hcut : cut < 1) (hc : HomotopyLiftingProperty c.hom)
    (y : RightCollar f' g' sq' cut)
    (hy : CompactHomotopyExtensionLiftingProperty
      (rightCollarComparisonFiber sq sq' a b c wf wg cut hcut y)) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y) :=
  rightCollar_strictFiberInclusion_compactHELP sq sq' a b c wf wg cut hcut hc y hy
example (hcut : 0 < cut) (y : LeftCollar f' g' sq' cut)
    (x : {x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x = y}) :
    (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut y x).val.val =
      (leftCollarMap sq sq' a b c wf wg cut x.val,
        leftCollarProjection f g sq cut hcut x.val) := rfl
example (hcut : cut < 1) (y : RightCollar f' g' sq' cut)
    (x : {x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x = y}) :
    (rightCollarComparisonFiber sq sq' a b c wf wg cut hcut y x).val.val =
      (rightCollarMap sq sq' a b c wf wg cut x.val,
        rightCollarProjection f g sq cut hcut x.val) := rfl
example (y : LeftCollar f' g' sq' cut)
    (x : {x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x = y})
    (s : unitInterval) :
    (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y x).val.2 s = y := rfl
example (y : RightCollar f' g' sq' cut)
    (x : {x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x = y})
    (s : unitInterval) :
    (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y x).val.2 s = y := rfl
end OriginalCollars
