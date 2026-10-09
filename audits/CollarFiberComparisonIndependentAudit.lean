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
  let mut counts : Array Nat := #[0,0,0,0]
  let mut count : Nat := 0
  for (name,_) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    count := count+1
    counts := counts.modify i (·+1)
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axs}"
  unless counts.all (· > 0) do throwError "Missing target origin"
  unless count == 92 && counts == #[25,40,16,11] do
    throwError "Expected fixed92 = 25+40+16+11, found {count}: {counts}"
  logInfo m!"FIXED92 PASSED {count}: {counts}"

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology Quillen Quillen.DoubleCylinder
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TheoremA.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') (cut : unitInterval)

example : IsEmbedding (fun x : B ↦ e (Sum.inl x)) := leftEnd_isEmbedding f g sq
example : IsEmbedding (fun x : C ↦ e (Sum.inr x)) := rightEnd_isEmbedding f g sq
example (x : D) (hx : height f g sq x = 0) : ∃ y : B,e (Sum.inl y) = x :=
  height_eq_zero_range f g sq x hx
example (x : D) (hx : height f g sq x = 1) : ∃ y : C,e (Sum.inr y) = x :=
  height_eq_one_range f g sq x hx
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
example (y : C') (x : {x : C // c x = y}) :
    (rightEndFiberHomeomorph sq sq' a b c wf wg y).symm
      (rightEndFiberHomeomorph sq sq' a b c wf wg y x) = x :=
  (rightEndFiberHomeomorph sq sq' a b c wf wg y).symm_apply_apply x
example (y : A') (t : OpenInterval) (x : {x : A // a x = y}) :
    (interiorFiberHomeomorph sq sq' a b c wf wg y t).symm
      (interiorFiberHomeomorph sq sq' a b c wf wg y t x) = x :=
  (interiorFiberHomeomorph sq sq' a b c wf wg y t).symm_apply_apply x
example (y : B') (x : {x : D // map sq sq' a b c wf wg x = e' (Sum.inl y)}) :
    leftEndFiberHomeomorph sq sq' a b c wf wg y
      ((leftEndFiberHomeomorph sq sq' a b c wf wg y).symm x) = x :=
  (leftEndFiberHomeomorph sq sq' a b c wf wg y).apply_symm_apply x
example (y : A') (t : OpenInterval)
    (x : {x : D // map sq sq' a b c wf wg x = l' (y,ULift.up t.val)}) :
    interiorFiberHomeomorph sq sq' a b c wf wg y t
      ((interiorFiberHomeomorph sq sq' a b c wf wg y t).symm x) = x :=
  (interiorFiberHomeomorph sq sq' a b c wf wg y t).apply_symm_apply x

example (y : LeftCollar f' g' sq' cut)
    (x : {x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x = y}) :
    (leftCollarFiberHomeomorph sq sq' a b c wf wg cut y x).val = x.val.val := rfl
example (y : RightCollar f' g' sq' cut)
    (x : {x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x = y}) :
    (rightCollarFiberHomeomorph sq sq' a b c wf wg cut y x).val = x.val.val := rfl
example (y : LeftCollar f' g' sq' cut) (x : {x : D // map sq sq' a b c wf wg x = y.val}) :
    ((leftCollarFiberHomeomorph sq sq' a b c wf wg cut y).symm x).val.val = x.val := rfl
example (y : RightCollar f' g' sq' cut) (x : {x : D // map sq sq' a b c wf wg x = y.val}) :
    ((rightCollarFiberHomeomorph sq sq' a b c wf wg cut y).symm x).val.val = x.val := rfl
example (hcut : 0 < cut) (y : B') (x : {x : B // b x = y}) :
    (leftCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y x).val =
      leftCollarInclusion f g sq cut hcut x.val := rfl
example (hcut : cut < 1) (y : C') (x : {x : C // c x = y}) :
    (rightCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y x).val =
      rightCollarInclusion f g sq cut hcut x.val := rfl
example (y : A') (t : OpenInterval) (ht : t.val < cut) (x : {x : A // a x = y}) :
    (leftCollarInteriorFiberHomeomorph sq sq' a b c wf wg cut y t ht x).val.val =
      l (x.val,ULift.up t.val) := rfl
example (y : A') (t : OpenInterval) (ht : cut < t.val) (x : {x : A // a x = y}) :
    (rightCollarInteriorFiberHomeomorph sq sq' a b c wf wg cut y t ht x).val.val =
      l (x.val,ULift.up t.val) := rfl
example : IsEmpty (LeftCollar f g sq 0) :=
  ⟨fun x ↦ not_lt_of_ge (show 0 ≤ height f g sq x.val from (height f g sq x.val).property.1) x.property⟩
example : IsEmpty (RightCollar f g sq 1) :=
  ⟨fun x ↦ not_lt_of_ge (show height f g sq x.val ≤ 1 from (height f g sq x.val).property.2) x.property⟩

example (y : A') (x : {x : A // a x = y}) : (leftAttachingFiberMap a b wf y x).val = f x.val := rfl
example (y : A') (x : {x : A // a x = y}) : (rightAttachingFiberMap a c wg y x).val = g x.val := rfl
example (hcut : 0 < cut) (y : B') : CompactHomotopyExtensionLiftingProperty
    (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut
      (leftCollarInclusion f' g' sq' cut hcut y)) :=
  leftCollarComparisonFiber_end_compactHELP sq sq' a b c wf wg cut hcut y
example (hcut : cut < 1) (y : C') : CompactHomotopyExtensionLiftingProperty
    (rightCollarComparisonFiber sq sq' a b c wf wg cut hcut
      (rightCollarInclusion f' g' sq' cut hcut y)) :=
  rightCollarComparisonFiber_end_compactHELP sq sq' a b c wf wg cut hcut y
example (hcut : 0 < cut) (y : A') (t : OpenInterval) (ht : t.val < cut)
    (hf : CompactHomotopyExtensionLiftingProperty (leftAttachingFiberMap a b wf y)) :
    CompactHomotopyExtensionLiftingProperty
      (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut (leftInteriorPoint sq' cut y t ht)) :=
  leftCollarComparisonFiber_interior_compactHELP sq sq' a b c wf wg cut hcut y t ht hf
example (hcut : cut < 1) (y : A') (t : OpenInterval) (ht : cut < t.val)
    (hg : CompactHomotopyExtensionLiftingProperty (rightAttachingFiberMap a c wg y)) :
    CompactHomotopyExtensionLiftingProperty
      (rightCollarComparisonFiber sq sq' a b c wf wg cut hcut (rightInteriorPoint sq' cut y t ht)) :=
  rightCollarComparisonFiber_interior_compactHELP sq sq' a b c wf wg cut hcut y t ht hg
example (hcut : 0 < cut)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingFiberMap a b wf y))
    (y : LeftCollar f' g' sq' cut) : CompactHomotopyExtensionLiftingProperty
      (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut y) :=
  leftCollarComparisonFiber_compactHELP sq sq' a b c wf wg cut hcut hf y
example (hcut : cut < 1)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingFiberMap a c wg y))
    (y : RightCollar f' g' sq' cut) : CompactHomotopyExtensionLiftingProperty
      (rightCollarComparisonFiber sq sq' a b c wf wg cut hcut y) :=
  rightCollarComparisonFiber_compactHELP sq sq' a b c wf wg cut hcut hg y
example (hcut : 0 < cut) (hb : HomotopyLiftingProperty b.hom)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingFiberMap a b wf y))
    (y : LeftCollar f' g' sq' cut) : CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y) :=
  leftCollar_strictFiberInclusion_compactHELP_of_edge sq sq' a b c wf wg cut hcut hb hf y
example (hcut : cut < 1) (hc : HomotopyLiftingProperty c.hom)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingFiberMap a c wg y))
    (y : RightCollar f' g' sq' cut) : CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y) :=
  rightCollar_strictFiberInclusion_compactHELP_of_edge sq sq' a b c wf wg cut hcut hc hg y
example (y : LeftCollar f' g' sq' cut)
    (x : {x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x = y}) (t : unitInterval) :
    (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y x).val.2 t = y := rfl
example (y : RightCollar f' g' sq' cut)
    (x : {x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x = y}) (t : unitInterval) :
    (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y x).val.2 t = y := rfl

-- The actual comparison's endpoint coordinate is the identity or original edge map.
example (hcut : 0 < cut) (y : B') (x : {x : B // b x = y}) :
    (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut
      (leftCollarInclusion f' g' sq' cut hcut y)
      (leftCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y x)).val.val.2 = x.val := by
  change leftCollarProjection f g sq cut hcut
    (leftCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y x).val = x.val
  rw [leftCollarEndFiberHomeomorph_val,leftCollarProjection_end]
example (hcut : cut < 1) (y : C') (x : {x : C // c x = y}) :
    (rightCollarComparisonFiber sq sq' a b c wf wg cut hcut
      (rightCollarInclusion f' g' sq' cut hcut y)
      (rightCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y x)).val.val.2 = x.val := by
  change rightCollarProjection f g sq cut hcut
    (rightCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y x).val = x.val
  rw [rightCollarEndFiberHomeomorph_val,rightCollarProjection_end]
example (hcut : 0 < cut) (y : A') (t : OpenInterval) (ht : t.val < cut)
    (x : {x : A // a x = y}) :
    (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut (leftInteriorPoint sq' cut y t ht)
      (leftCollarInteriorFiberHomeomorph sq sq' a b c wf wg cut y t ht x)).val.val.2 = f x.val := by
  exact leftCollarProjection_apply_cylinder f g sq cut hcut x.val (ULift.up t.val) ht
example (hcut : cut < 1) (y : A') (t : OpenInterval) (ht : cut < t.val)
    (x : {x : A // a x = y}) :
    (rightCollarComparisonFiber sq sq' a b c wf wg cut hcut (rightInteriorPoint sq' cut y t ht)
      (rightCollarInteriorFiberHomeomorph sq sq' a b c wf wg cut y t ht x)).val.val.2 = g x.val := by
  exact rightCollarProjection_apply_cylinder f g sq cut hcut x.val (ULift.up t.val) ht

example (y : A') (x : HomotopyFiber a.hom y) :
    (leftAttachingHomotopyFiberMap a b wf y x).val.1 = f x.val.1 := rfl
example (y : A') (x : HomotopyFiber a.hom y) :
    (rightAttachingHomotopyFiberMap a c wg y x).val.1 = g x.val.1 := rfl
example (y : A') (x : HomotopyFiber a.hom y) (t : unitInterval) :
    (leftAttachingHomotopyFiberMap a b wf y x).val.2 t = f' (x.val.2 t) := rfl
example (y : A') (x : HomotopyFiber a.hom y) (t : unitInterval) :
    (rightAttachingHomotopyFiberMap a c wg y x).val.2 t = g' (x.val.2 t) := rfl
example (y : A') :
    (HomotopyFiber.strictFiberInclusion b.hom (f' y)).comp (leftAttachingFiberMap a b wf y) =
      (leftAttachingHomotopyFiberMap a b wf y).comp (HomotopyFiber.strictFiberInclusion a.hom y) := rfl
example (y : A') :
    (HomotopyFiber.strictFiberInclusion c.hom (g' y)).comp (rightAttachingFiberMap a c wg y) =
      (rightAttachingHomotopyFiberMap a c wg y).comp (HomotopyFiber.strictFiberInclusion a.hom y) := rfl
example (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (y : A') (hf : CompactHomotopyExtensionLiftingProperty (leftAttachingHomotopyFiberMap a b wf y)) :
    CompactHomotopyExtensionLiftingProperty (leftAttachingFiberMap a b wf y) :=
  leftAttachingFiberMap_compactHELP a b wf ha hb y hf
example (ha : HomotopyLiftingProperty a.hom) (hc : HomotopyLiftingProperty c.hom)
    (y : A') (hg : CompactHomotopyExtensionLiftingProperty (rightAttachingHomotopyFiberMap a c wg y)) :
    CompactHomotopyExtensionLiftingProperty (rightAttachingFiberMap a c wg y) :=
  rightAttachingFiberMap_compactHELP a c wg ha hc y hg
example (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingHomotopyFiberMap a b wf y))
    (hcut : 0 < cut) (y : LeftCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y) :=
  leftCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hb hf cut hcut y
example (ha : HomotopyLiftingProperty a.hom) (hc : HomotopyLiftingProperty c.hom)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingHomotopyFiberMap a c wg y))
    (hcut : cut < 1) (y : RightCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y) :=
  rightCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hc hg cut hcut y
example (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingHomotopyFiberMap a b wf y))
    (hcut : 0 < cut) (y : LeftCollar f' g' sq' cut)
    (K L : TopCat.{u}) [CompactSpace K] [CompactSpace L] (i : K ⟶ L)
    (hi : TheoremA.homotopyExtensionProperty i)
    (s : C(K,{x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x = y}))
    (d : C(L,HomotopyFiber (leftCollarMap sq sq' a b c wf wg cut).hom y))
    (H : ((HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y).comp s).Homotopy
      (d.comp i.hom)) :
    ∃ k : C(L,{x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x = y}),
      k.comp i.hom = s ∧ ∃ V :
        ((HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y).comp k).Homotopy d,
        ∀ t x,V (t,i x) = H (t,x) :=
  leftCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hb hf cut hcut y
    K L i hi s d H
example (ha : HomotopyLiftingProperty a.hom) (hc : HomotopyLiftingProperty c.hom)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingHomotopyFiberMap a c wg y))
    (hcut : cut < 1) (y : RightCollar f' g' sq' cut)
    (K L : TopCat.{u}) [CompactSpace K] [CompactSpace L] (i : K ⟶ L)
    (hi : TheoremA.homotopyExtensionProperty i)
    (s : C(K,{x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x = y}))
    (d : C(L,HomotopyFiber (rightCollarMap sq sq' a b c wf wg cut).hom y))
    (H : ((HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y).comp s).Homotopy
      (d.comp i.hom)) :
    ∃ k : C(L,{x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x = y}),
      k.comp i.hom = s ∧ ∃ V :
        ((HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y).comp k).Homotopy d,
        ∀ t x,V (t,i x) = H (t,x) :=
  rightCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hc hg cut hcut y
    K L i hi s d H

-- Complete original homotopy-set maps, separately testing degree zero and components.
example (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingHomotopyFiberMap a b wf y))
    (hcut : 0 < cut) (y : LeftCollar f' g' sq' cut)
    (x : {x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x = y}) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y) (x := x) rfl) :=
  ((leftCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hb hf cut hcut y).isWeakHomotopyEquivalence).homotopy_bijective x n
example (ha : HomotopyLiftingProperty a.hom) (hc : HomotopyLiftingProperty c.hom)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingHomotopyFiberMap a c wg y))
    (hcut : cut < 1) (y : RightCollar f' g' sq' cut)
    (x : {x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x = y}) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y) (x := x) rfl) :=
  ((rightCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hc hg cut hcut y).isWeakHomotopyEquivalence).homotopy_bijective x n
example (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingHomotopyFiberMap a b wf y))
    (hcut : 0 < cut) (y : LeftCollar f' g' sq' cut)
    (x : {x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x = y}) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y) (x := x) rfl) :=
  ((leftCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hb hf cut hcut y).isWeakHomotopyEquivalence).homotopy_bijective x 0
example (ha : HomotopyLiftingProperty a.hom) (hc : HomotopyLiftingProperty c.hom)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingHomotopyFiberMap a c wg y))
    (hcut : cut < 1) (y : RightCollar f' g' sq' cut)
    (x : {x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x = y}) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y) (x := x) rfl) :=
  ((rightCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hc hg cut hcut y).isWeakHomotopyEquivalence).homotopy_bijective x 0
example (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingHomotopyFiberMap a b wf y))
    (hcut : 0 < cut) (y : LeftCollar f' g' sq' cut)
    (z : HomotopyFiber (leftCollarMap sq sq' a b c wf wg cut).hom y) :
    ∃ x, Joined (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y x) z :=
  ((leftCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hb hf cut hcut y).isWeakHomotopyEquivalence).component_surjective z
example (ha : HomotopyLiftingProperty a.hom) (hc : HomotopyLiftingProperty c.hom)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingHomotopyFiberMap a c wg y))
    (hcut : cut < 1) (y : RightCollar f' g' sq' cut)
    (z : HomotopyFiber (rightCollarMap sq sq' a b c wf wg cut).hom y) :
    ∃ x, Joined (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y x) z :=
  ((rightCollar_strictFiberInclusion_compactHELP_of_homotopyFibers sq sq' a b c wf wg ha hc hg cut hcut y).isWeakHomotopyEquivalence).component_surjective z
