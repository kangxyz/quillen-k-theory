/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StrictDoubleSquareCone
public import Quillen.Topology.Prespectrum.StrictSquarePushoutNaturality
public import Quillen.Topology.Prespectrum.StrictSquareConeInterchangeNaturality

/-!
# Naturality of the actual two-totalization interchange

Every morphism of the original four-dimensional strict diagrams gives the
original pointwise comparison square. The source isomorphism is natural by the
proved square-cone/pushout theorem; the second factor is the original
cone/square interchange. The resulting whole-map equality and its inverse need
no new compatibility hypotheses.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.StrictSquare.Double
variable {E E' : Arrow (Arrow (Arrow (Arrow LoopPrespectrum.{u})))} (h : E ⟶ E')

/-- Restrict the actual four-dimensional map to its three source squares. -/
def sourceSpanMorphism :
    Pushout.SpanMorphism E.left.hom E.hom.left E'.left.hom E'.hom.left where
  source := h.left.left
  left := h.left.right
  right := h.right.left
  left_comm := h.left.w.symm
  right_comm := (congrArg (fun a => a.left) h.w).symm

/-- The actual pointwise original comparison is natural in the entire strict diagram. -/
theorem comparisonMap_naturality :
    (sourceSpanMorphism h).squareMap ≫ comparisonMap E' = comparisonMap E ≫ h.right.right := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext
  · exact comparison_naturality ((Arrow.leftFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.map h)
  · exact comparison_naturality ((Arrow.leftFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.map h)
  · exact comparison_naturality ((Arrow.rightFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.map h)
  · exact comparison_naturality ((Arrow.rightFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.map h)

/-- The original square of comparison arrows before taking their pointwise cones. -/
def comparisonArrowMap : Arrow.mk (comparisonMap E) ⟶ Arrow.mk (comparisonMap E') :=
  Arrow.homMk (sourceSpanMorphism h).squareMap h.right.right (comparisonMap_naturality h)

/-- Naturality of the actual source-change isomorphism, with its literal identity target. -/
theorem comparisonArrowIso_naturality :
    strictSquareComparisonFunctor.map (totalFunctor.mapArrow.mapArrow.map h) ≫
        (comparisonArrowIso E').hom =
      (comparisonArrowIso E).hom ≫ totalFunctor.mapArrow.map (comparisonArrowMap h) := by
  apply Arrow.hom_ext
  · exact (sourceSpanMorphism h).totalIso_naturality
  · rfl

/-- The whole actual interchange is natural for every four-dimensional strict diagram map. -/
theorem interchangeIso_naturality :
    totalFunctor.map (totalFunctor.mapArrow.mapArrow.map h) ≫ (interchangeIso E').hom =
      (interchangeIso E).hom ≫ totalFunctor.map (coneSquareMap (comparisonArrowMap h)) := by
  have hc : mappingConeFunctor.map
      (strictSquareComparisonFunctor.map (totalFunctor.mapArrow.mapArrow.map h)) ≫
        mappingConeFunctor.map (comparisonArrowIso E').hom =
      mappingConeFunctor.map (comparisonArrowIso E).hom ≫
        mappingConeFunctor.map (totalFunctor.mapArrow.map (comparisonArrowMap h)) := by
    rw [← mappingConeFunctor.map_comp, ← mappingConeFunctor.map_comp,
      comparisonArrowIso_naturality]
  change mappingConeFunctor.map
    (strictSquareComparisonFunctor.map (totalFunctor.mapArrow.mapArrow.map h)) ≫
      mappingConeFunctor.map (comparisonArrowIso E').hom ≫
    (coneInterchangeIso (comparisonMap E')).hom =
      (mappingConeFunctor.map (comparisonArrowIso E).hom ≫
        (coneInterchangeIso (comparisonMap E)).hom) ≫ _
  rw [← Category.assoc, hc, Category.assoc]
  exact (congrArg (fun a => mappingConeFunctor.map (comparisonArrowIso E).hom ≫ a)
    (coneInterchangeIso_naturality (comparisonArrowMap h))).trans (Category.assoc _ _ _).symm

/-- Its specified inverse is natural for the same actual maps. -/
theorem interchangeIso_inv_naturality :
    totalFunctor.map (coneSquareMap (comparisonArrowMap h)) ≫ (interchangeIso E').inv =
      (interchangeIso E).inv ≫ totalFunctor.map (totalFunctor.mapArrow.mapArrow.map h) := by
  apply (cancel_mono (interchangeIso E').hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    interchangeIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Quillen.LoopPrespectrum.StrictSquare.Double
