import Quillen.CategoryTheory.TheoremB.CompactCollarHomotopyFiberInput
import Quillen.Topology.HELP.FiberwiseWeakEquivalence
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.CategoryTheory.TheoremB.DoubleCylinderFiberCoordinates,
    `Quillen.CategoryTheory.TheoremB.CollarFiberCoordinates,
    `Quillen.CategoryTheory.TheoremB.CompactCollarFiberComparison,
    `Quillen.CategoryTheory.TheoremB.CompactCollarHomotopyFiberInput]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    seen := seen.insert origin
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axs}"
  unless seen.size == 4 do throwError "Missing collar-fiber origin"
  unless count == 92 do throwError "Expected 92 collar-fiber origins, found {count}"
  logInfo m!"Audited all {count} collar-fiber origins."
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Quillen Quillen.DoubleCylinder
open scoped Topology unitInterval
universe u
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TheoremA.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

example (y : B') (x : {x : B // b x = y}) :
    (leftEndFiberHomeomorph sq sq' a b c wf wg y x).val = e (Sum.inl x.val) := rfl
example (y : C') (x : {x : C // c x = y}) :
    (rightEndFiberHomeomorph sq sq' a b c wf wg y x).val = e (Sum.inr x.val) := rfl
example (y : A') (t : OpenInterval) (x : {x : A // a x = y}) :
    (interiorFiberHomeomorph sq sq' a b c wf wg y t x).val = l (x.val,ULift.up t.val) := rfl
example (y : B') (x : {x : B // b x = y}) :
    (leftEndFiberHomeomorph sq sq' a b c wf wg y).symm
      (leftEndFiberHomeomorph sq sq' a b c wf wg y x) = x :=
  (leftEndFiberHomeomorph sq sq' a b c wf wg y).symm_apply_apply x
example (cut : unitInterval) (hcut : 0 < cut) (y : B') (x : {x : B // b x = y}) :
    (leftCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y x).val =
      leftCollarInclusion f g sq cut hcut x.val := rfl
example (cut : unitInterval) (hcut : cut < 1) (y : C') (x : {x : C // c x = y}) :
    (rightCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y x).val =
      rightCollarInclusion f g sq cut hcut x.val := rfl
example (cut : unitInterval) (y : A') (t : OpenInterval) (ht : t.val < cut)
    (x : {x : A // a x = y}) :
    (leftCollarInteriorFiberHomeomorph sq sq' a b c wf wg cut y t ht x).val.val =
      l (x.val,ULift.up t.val) := rfl
example (y : A') (x : HomotopyFiber a.hom y) :
    (leftAttachingHomotopyFiberMap a b wf y x).val.2 = f'.hom.comp x.val.2 := rfl
example (y : A') (x : HomotopyFiber a.hom y) :
    (rightAttachingHomotopyFiberMap a c wg y x).val.2 = g'.hom.comp x.val.2 := rfl
example (y : A') :
    (HomotopyFiber.strictFiberInclusion b.hom (f' y)).comp (leftAttachingFiberMap a b wf y) =
      (leftAttachingHomotopyFiberMap a b wf y).comp (HomotopyFiber.strictFiberInclusion a.hom y) := rfl
example (cut : unitInterval) (hcut : 0 < cut)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingFiberMap a b wf y))
    (y : LeftCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut y) :=
  leftCollarComparisonFiber_compactHELP sq sq' a b c wf wg cut hcut hf y
example (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingHomotopyFiberMap a b wf y))
    (cut : unitInterval) (hcut : 0 < cut) (y : LeftCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y) :=
  leftCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hb hf cut hcut y
example (ha : HomotopyLiftingProperty a.hom) (hc : HomotopyLiftingProperty c.hom)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingHomotopyFiberMap a c wg y))
    (cut : unitInterval) (hcut : cut < 1) (y : RightCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y) :=
  rightCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hc hg cut hcut y
example (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingHomotopyFiberMap a b wf y))
    (cut : unitInterval) (hcut : 0 < cut) (y : LeftCollar f' g' sq' cut)
    (x : {z : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut z = y}) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y) (x := x) rfl) := by
  have h := leftCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hb hf cut hcut y
  exact (h.isWeakHomotopyEquivalence).homotopy_bijective x n
