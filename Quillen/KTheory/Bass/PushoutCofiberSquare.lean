/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.PushoutStrength
public import Quillen.KTheory.Bass.StrictDiagramCofiberDescent
public import Quillen.Topology.Prespectrum.PushoutCollapseNaturality

/-!
# The positive-direction cone square for Bass pushout strength

The original right-cone collapse and the actual Bass cofiber comparison give a
commuting square without choosing an inverse comparison. Every inner overlap
and outer cone-cylinder value is retained. This is an adopted independent reconstruction against
the identified baseline.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u v w
namespace Quillen.KTheory.Bass.PushoutCofiberSquare
open PushoutStrength
variable {C : Type u} [Category.{v} C]
  {F₀ F₁ F₂ : C ⥤ LoopPrespectrum.{w}} (f : F₀ ⟶ F₁) (g : F₀ ⟶ F₂)

/-- Original cone inclusions as a coefficient-natural transformation. -/
def coneInclusion : F₁ ⟶ mappingConeDiagram f where
  app X := mappingConeInclusion (f.app X)
  naturality X Y k := (mappingConeInclusionSquare
    (Arrow.homMk (f := Arrow.mk (f.app X)) (g := Arrow.mk (f.app Y))
      (F₀.map k) (F₁.map k) (f.naturality k))).w

/-- The original entire cone null track. -/
def coneNull (X : C) :
    Homotopy ((f ≫ coneInclusion f).app X)
      ((diagramZeroMap F₀ (mappingConeDiagram f)).app X) :=
  mappingConeHomotopy (f.app X)

/-- Original cone maps retain the independent null coordinate. -/
theorem coneNull_naturality {X Y : C} (k : X ⟶ Y) n r x :
    ((mappingConeDiagram f).map k).map n ((coneNull f X).level n (r, x)) =
      (coneNull f Y).level n (r, (F₀.map k).map n x) := rfl

/-- Descent of the original inclusion and original null is the identity. -/
theorem coneDesc_self :
    mappingConeDescTransformation f (coneInclusion f) (coneNull f)
      (coneNull_naturality f) = 𝟙 (mappingConeDiagram f) := by
  apply NatTrans.ext
  funext X
  apply mappingCone_hom_ext
  · apply Hom.ext; funext n; ext x; rfl
  · intro n r x
    rfl

/-- The unchanged pointwise collapse of the right pushout chart. -/
def collapse : pushout f g ⟶ mappingConeDiagram f where
  app X := HomotopyPushout.collapseRight (f.app X) (g.app X)
  naturality X Y k := by
    apply HomotopyPushout.hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · apply Hom.ext
      funext n
      ext x
      exact (((mappingConeDiagram f).map k).map_point n).symm
    · intro n r x
      rfl

/-- The left inclusion survives the original collapse. -/
theorem left_collapse : left f g ≫ collapse f g = coneInclusion f := by
  apply NatTrans.ext
  funext X
  apply Hom.ext; funext n; ext x; rfl

/-- The right inclusion becomes the literal zero transformation. -/
theorem right_collapse : right f g ≫ collapse f g =
    diagramZeroMap F₂ (mappingConeDiagram f) := by
  apply NatTrans.ext
  funext X
  apply Hom.ext; funext n; ext x; rfl

/-- The original constant null on the collapsed right chart. -/
def collapseNull (X : C) :
    Homotopy (((right f g) ≫ collapse f g).app X)
      ((diagramZeroMap F₂ (mappingConeDiagram f)).app X) :=
  HomotopyPushout.collapseRightNull (f.app X) (g.app X)

/-- The complete constant null remains coefficient-natural. -/
theorem collapseNull_naturality {X Y : C} (k : X ⟶ Y) n r x :
    ((mappingConeDiagram f).map k).map n ((collapseNull f g X).level n (r, x)) =
      (collapseNull f g Y).level n (r, (F₂.map k).map n x) :=
  ((mappingConeDiagram f).map k).map_point n

/-- Original right-inclusion cones collapse by the prescribed quotient descent. -/
def coneCollapse : mappingConeDiagram (right f g) ⟶ mappingConeDiagram f :=
  mappingConeDescTransformation (right f g) (collapse f g) (collapseNull f g)
    (collapseNull_naturality f g)

variable (Q : C ⥤ Arrow (Arrow C))

/-- The positive cofiber comparison is the original descent of the Bass cone null. -/
theorem cofiberComparison_desc (X : C) :
    (strictDiagramCofiberComparison Q f).app X =
      mappingConeDesc (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map (coneInclusion f)).app X)
        (strictDiagramNullHomotopy f (coneInclusion f) (coneNull f)
          (coneNull_naturality f) Q X) := by
  have h := strictDiagramCofiberComparison_desc Q f (coneInclusion f)
    (coneNull f) (coneNull_naturality f) X
  rw [coneDesc_self, CategoryTheory.Functor.map_id] at h
  simpa only [NatTrans.id_app, Category.comp_id] using h

/-- The cofiber comparison retains the original inclusion. -/
@[reassoc]
theorem cofiberComparison_inclusion (X : C) :
    mappingConeInclusion (((strictDiagramFunctor Q).map f).app X) ≫
      (strictDiagramCofiberComparison Q f).app X =
        (((strictDiagramFunctor Q).map (coneInclusion f)).app X) := by
  rw [cofiberComparison_desc]
  exact mappingConeInclusion_desc _ _ _

/-- The cofiber comparison's cylinder is the Bass image of the same original time slice. -/
theorem cofiberComparison_cylinder (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F₀).obj X).space n) :
    ((strictDiagramCofiberComparison Q f).app X).map n
      ((mappingConeHomotopy (((strictDiagramFunctor Q).map f).app X)).level n (r, x)) =
        (((strictDiagramFunctor Q).map
          (diagramHomotopyAt (coneNull f) (coneNull_naturality f) r)).app X).map n x := by
  rw [cofiberComparison_desc]
  change ((strictDiagramMapHomotopy (coneNull f) (coneNull_naturality f) Q X).at r).map n x = _
  rw [strictDiagramMapHomotopy_at]

/-- Collapsing the original overlap at any time yields the original cone null at that time. -/
theorem glueAt_collapse (r : unitInterval) :
    diagramHomotopyAt (glue f g) (glue_naturality f g) r ≫ collapse f g =
      diagramHomotopyAt (coneNull f) (coneNull_naturality f) r := by
  apply NatTrans.ext
  funext X
  apply Hom.ext; funext n; ext x; rfl

/-- Every slice of the prescribed constant null is the literal zero transformation. -/
theorem collapseNullAt (r : unitInterval) :
    diagramHomotopyAt (collapseNull f g) (collapseNull_naturality f g) r =
      diagramZeroMap F₂ (mappingConeDiagram f) := by
  apply NatTrans.ext
  funext X
  apply Hom.ext; funext n; ext x; rfl

/-- The right-inclusion square uses the original comparison and the identity source map. -/
def rightSquare (X : C) :
    Arrow.mk (HomotopyPushout.inr (((strictDiagramFunctor Q).map f).app X)
      (((strictDiagramFunctor Q).map g).app X)) ⟶
        Arrow.mk (((strictDiagramFunctor Q).map (right f g)).app X) :=
  Arrow.homMk (𝟙 _) (comparison f g Q X) (by
    exact (Category.id_comp _).trans (comparison_right f g Q X).symm)

/-- The original overlap descent commutes with the actual positive cofiber comparison. -/
theorem comparison_collapse (X : C) :
    comparison f g Q X ≫ (((strictDiagramFunctor Q).map (collapse f g)).app X) =
      HomotopyPushout.collapseRight (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) ≫
          (strictDiagramCofiberComparison Q f).app X := by
  apply HomotopyPushout.hom_ext
  · apply Hom.ext
    funext n
    ext x
    have hl := congrArg (fun a => (a.app X).map n x)
      (((strictDiagramFunctor Q).map_comp (left f g) (collapse f g)).symm.trans
        (congrArg (fun a => (strictDiagramFunctor Q).map a) (left_collapse f g)))
    have hc := congrArg (fun a => a.map n x) (cofiberComparison_inclusion f Q X)
    exact hl.trans hc.symm
  · apply Hom.ext
    funext n
    ext x
    have hz := congrArg (fun a => a.app X)
      (((strictDiagramFunctor Q).map_comp (right f g) (collapse f g)).symm.trans
        (congrArg (fun a => (strictDiagramFunctor Q).map a) (right_collapse f g)))
    rw [strictDiagramFunctor_map_zero_app] at hz
    exact (congrArg (fun a => a.map n x) hz).trans
      (((strictDiagramCofiberComparison Q f).app X).map_point n).symm
  · intro n r x
    change (((strictDiagramFunctor Q).map (collapse f g)).app X).map n
      (((strictDiagramMapHomotopy (glue f g) (glue_naturality f g) Q X).at r).map n x) =
        ((strictDiagramCofiberComparison Q f).app X).map n
          ((mappingConeHomotopy (((strictDiagramFunctor Q).map f).app X)).level n (r, x))
    rw [strictDiagramMapHomotopy_at, cofiberComparison_cylinder]
    exact congrArg (fun a => (a.app X).map n x)
      (((strictDiagramFunctor Q).map_comp
        (diagramHomotopyAt (glue f g) (glue_naturality f g) r) (collapse f g)).symm.trans
        (congrArg (fun a => (strictDiagramFunctor Q).map a) (glueAt_collapse f g r)))

/-- The positive cone square retains both original quotient cylinders. -/
theorem coneSquare (X : C) :
    mappingConeMap (rightSquare f g Q X) ≫
        (strictDiagramCofiberComparison Q (right f g)).app X ≫
          (((strictDiagramFunctor Q).map (coneCollapse f g)).app X) =
      HomotopyPushout.rightConeCollapse (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) ≫
          (strictDiagramCofiberComparison Q f).app X := by
  rw [show (strictDiagramCofiberComparison Q (right f g)).app X ≫
      (((strictDiagramFunctor Q).map (coneCollapse f g)).app X) = _ from
    strictDiagramCofiberComparison_desc Q (right f g) (collapse f g)
      (collapseNull f g) (collapseNull_naturality f g) X]
  apply mappingCone_hom_ext
  · change comparison f g Q X ≫ (((strictDiagramFunctor Q).map (collapse f g)).app X) = _
    exact comparison_collapse f g Q X
  · intro n r x
    change ((strictDiagramMapHomotopy (collapseNull f g)
      (collapseNull_naturality f g) Q X).at r).map n x =
        ((strictDiagramCofiberComparison Q f).app X).map n
          ((mappingCone (((strictDiagramFunctor Q).map f).app X)).point n)
    rw [strictDiagramMapHomotopy_at, collapseNullAt, strictDiagramFunctor_map_zero_app]
    exact (((strictDiagramCofiberComparison Q f).app X).map_point n).symm

end Quillen.KTheory.Bass.PushoutCofiberSquare
