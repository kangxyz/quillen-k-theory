/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.DoubleMappingCylinder.Cartesian
public import Quillen.Topology.DoubleMappingCylinder.Collapse
public import Quillen.Topology.HomotopyPullback.Symmetry

/-!
# The genuine homotopy-cartesian cofibrant pushout cube

For a strictly commuting map of ordinary TopCat pushout squares with
cofibrant corresponding legs, homotopy-cartesianness of the two incoming
squares implies homotopy-cartesianness of both outgoing squares. The proof
constructs double cylinders, applies finite homotopy-cartesian gluing, and
pastes with their actual homotopy-equivalent collapses.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.CartesianPushout

/-- Equal base maps identify their path-space pullbacks without changing
any actual coordinate. -/
def baseMapCongr {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    (f : C(X, B)) (g g' : C(A, B)) (h : g = g') : HomotopyPullback f g ≃ₜ HomotopyPullback f g'
      where
  toFun z := ⟨z.1, z.2.1, z.2.2.trans (ContinuousMap.congr_fun h z.1.1)⟩
  invFun z := ⟨z.1, z.2.1, z.2.2.trans (ContinuousMap.congr_fun h z.1.1).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The double mapping cylinder of the span `B ← A → C`, defined by its endpoint pushout. -/
abbrev Cylinder {A B C : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C) : TopCat.{u} :=
  pushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g)
/-- The canonical map of `A × I` into the double mapping cylinder of `f` and `g`. -/
abbrev cylinderLine {A B C : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C) : A ⊗ TopCat.I ⟶ Cylinder f g :=
  pushout.inl _ _
/-- The canonical map of `B ⊕ C` into the double mapping cylinder of `f` and `g`. -/
abbrev cylinderEnd {A B C : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C) : TopCat.of (B ⊕ C) ⟶ Cylinder f
    g :=
  pushout.inr _ _
theorem cylinderSquare {A B C : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C) :
    IsPushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g) (cylinderLine f g)
      (cylinderEnd f g) :=
  IsPushout.of_hasPushout _ _

variable {A B C P A' B' C' P' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ P'} {j' : C' ⟶ P'}
  (sq : IsPushout f g i j) (sq' : IsPushout f' g' i' j')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (wi : i ≫ p = b ≫ i') (wj : j ≫ p = c ≫ j')
  (hf : Quillen.homotopyExtensionProperty f) (hf' : Quillen.homotopyExtensionProperty f')

/-- The double-cylinder map induced by the strictly commuting span maps `a`, `b`, and `c`. -/
abbrev cylinderMap : Cylinder f g ⟶ Cylinder f' g' :=
  DoubleCylinder.map (cylinderSquare f g) (cylinderSquare f' g') a b c wf wg
/-- The canonical collapse from the source double mapping cylinder to the given source pushout
`P`. -/
abbrev collapse : Cylinder f g ⟶ P := DoubleCylinder.collapse (cylinderSquare f g) sq
/-- The canonical collapse from the target double mapping cylinder to the given target pushout
`P'`. -/
abbrev collapseBase : Cylinder f' g' ⟶ P' := DoubleCylinder.collapse (cylinderSquare f' g') sq'

include wi wj in
theorem collapse_square : p.hom.comp (collapse sq).hom =
    (collapseBase sq').hom.comp (cylinderMap a b c wf wg).hom :=
  congrArg TopCat.Hom.hom
    (DoubleCylinder.collapse_naturality (cylinderSquare f g) sq (cylinderSquare f' g') sq'
      a b c p wf wg wi wj).symm

/-- The two cofibrant collapses form a homotopy-cartesian square because
both horizontal maps are actual ordinary homotopy equivalences. -/
def collapseSquareEquiv : ContinuousMap.HomotopyEquiv (Cylinder f g)
    (HomotopyPullback p.hom (collapseBase sq').hom) :=
  Quillen.homotopyEquivCancelRight
    (a := HomotopyPullback.comparison p.hom (collapseBase sq').hom
      (cylinderMap a b c wf wg).hom (collapse sq).hom (collapse_square sq sq' a b c p wf wg wi wj))
    (HomotopyPullback.sourceProjectionEquivOfParameterEquiv p.hom (collapseBase sq').hom
      (DoubleCylinder.collapseHomotopyEquiv (cylinderSquare f' g') sq' hf') rfl) rfl
    (DoubleCylinder.collapseHomotopyEquiv (cylinderSquare f g) sq hf) rfl

@[simp] theorem collapseSquareEquiv_toFun :
    (collapseSquareEquiv sq sq' a b c p wf wg wi wj hf hf').toFun =
      HomotopyPullback.comparison p.hom (collapseBase sq').hom
        (cylinderMap a b c wf wg).hom (collapse sq).hom (collapse_square sq sq' a b c p wf wg wi
          wj) := rfl

variable
  (EL : ContinuousMap.HomotopyEquiv A (HomotopyPullback b.hom f'.hom))
  (hEL : EL.toFun = HomotopyPullback.comparison b.hom f'.hom a.hom f.hom (congrArg
    TopCat.Hom.hom wf))
  (ER : ContinuousMap.HomotopyEquiv A (HomotopyPullback c.hom g'.hom))
  (hER : ER.toFun = HomotopyPullback.comparison c.hom g'.hom a.hom g.hom (congrArg
    TopCat.Hom.hom wg))

include sq sq' wf wg wi wj hf hf' hEL hER in
/-- Actual canonical homotopy-cartesianness of the outgoing left square. -/
theorem exists_leftHomotopyEquiv :
    ∃ E : ContinuousMap.HomotopyEquiv B (HomotopyPullback p.hom i'.hom),
      E.toFun = HomotopyPullback.comparison p.hom i'.hom b.hom i.hom (congrArg TopCat.Hom.hom
        wi) := by
  let e0 := DoubleCylinder.Cartesian.leftEndHomotopyEquiv (cylinderSquare f g) (cylinderSquare
    f' g')
    a b c wf wg EL hEL ER hER
  let e1 := collapseSquareEquiv sq sq' a b c p wf wg wi wj hf hf'
  let E := HomotopyPullback.pastingHomotopyEquiv b.hom (cylinderMap a b c wf wg).hom p.hom
    (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f g)).hom (collapse sq).hom
    (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f' g')).hom (collapseBase sq').hom
    (DoubleCylinder.FiniteNormalization.left_square (cylinderSquare f g) (cylinderSquare f' g')
      a b c wf wg)
    (collapse_square sq sq' a b c p wf wg wi wj) e0
    (DoubleCylinder.Cartesian.leftEndHomotopyEquiv_toFun _ _ _ _ _ _ _ _ _ _ _) e1 rfl
  have hl : (collapse sq).hom.comp (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f
    g)).hom = i.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_leftEnd (cylinderSquare f g) sq)
  have hb : (collapseBase sq').hom.comp (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f'
    g')).hom = i'.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_leftEnd (cylinderSquare f' g') sq')
  refine ⟨E.trans (baseMapCongr p.hom _ i'.hom hb).toHomotopyEquiv, ?_⟩
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (b x, collapse sq (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f g) x),
      ContinuousMap.const unitInterval
        (collapseBase sq' (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f' g') (b x)))) =
    (b x, i x, ContinuousMap.const unitInterval (i' (b x)))
  exact Prod.ext rfl (Prod.ext (ContinuousMap.congr_fun hl x)
    (ContinuousMap.ext (fun _ ↦ ContinuousMap.congr_fun hb (b x))))

include sq sq' wf wg wi wj hf hf' hEL hER in
/-- The corresponding actual canonical outgoing right comparison. -/
theorem exists_rightHomotopyEquiv :
    ∃ E : ContinuousMap.HomotopyEquiv C (HomotopyPullback p.hom j'.hom),
      E.toFun = HomotopyPullback.comparison p.hom j'.hom c.hom j.hom (congrArg TopCat.Hom.hom
        wj) := by
  let e0 := DoubleCylinder.Cartesian.rightEndHomotopyEquiv (cylinderSquare f g) (cylinderSquare
    f' g')
    a b c wf wg EL hEL ER hER
  let e1 := collapseSquareEquiv sq sq' a b c p wf wg wi wj hf hf'
  let E := HomotopyPullback.pastingHomotopyEquiv c.hom (cylinderMap a b c wf wg).hom p.hom
    (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f g)).hom (collapse sq).hom
    (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f' g')).hom (collapseBase sq').hom
    (DoubleCylinder.FiniteNormalization.right_square (cylinderSquare f g) (cylinderSquare f' g')
      a b c wf wg)
    (collapse_square sq sq' a b c p wf wg wi wj) e0
    (DoubleCylinder.Cartesian.rightEndHomotopyEquiv_toFun _ _ _ _ _ _ _ _ _ _ _) e1 rfl
  have hr : (collapse sq).hom.comp (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f
    g)).hom = j.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_rightEnd (cylinderSquare f g) sq)
  have hc : (collapseBase sq').hom.comp (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd
    f' g')).hom = j'.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_rightEnd (cylinderSquare f' g') sq')
  refine ⟨E.trans (baseMapCongr p.hom _ j'.hom hc).toHomotopyEquiv, ?_⟩
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (c x, collapse sq (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f g) x),
      ContinuousMap.const unitInterval
        (collapseBase sq' (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f' g') (c x)))) =
    (c x, j x, ContinuousMap.const unitInterval (j' (c x)))
  exact Prod.ext rfl (Prod.ext (ContinuousMap.congr_fun hr x)
    (ContinuousMap.ext (fun _ ↦ ContinuousMap.congr_fun hc (c x))))

/-- A chosen actual left comparison equivalence, with its exact forward map. -/
def leftHomotopyEquiv : ContinuousMap.HomotopyEquiv B (HomotopyPullback p.hom i'.hom) :=
  (exists_leftHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).choose
@[simp] theorem leftHomotopyEquiv_toFun :
    (leftHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).toFun =
      HomotopyPullback.comparison p.hom i'.hom b.hom i.hom (congrArg TopCat.Hom.hom wi) :=
  (exists_leftHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).choose_spec

/-- A chosen actual right comparison equivalence, with its exact forward map. -/
def rightHomotopyEquiv : ContinuousMap.HomotopyEquiv C (HomotopyPullback p.hom j'.hom) :=
  (exists_rightHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).choose
@[simp] theorem rightHomotopyEquiv_toFun :
    (rightHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).toFun =
      HomotopyPullback.comparison p.hom j'.hom c.hom j.hom (congrArg TopCat.Hom.hom wj) :=
  (exists_rightHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).choose_spec

end Quillen.CartesianPushout
