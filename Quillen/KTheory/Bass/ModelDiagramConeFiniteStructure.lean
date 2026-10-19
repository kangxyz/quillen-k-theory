/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramFiniteStructure

/-!
# Original unlooped cone ranges at all finite Bass stages

The actual four corners of every finite stage satisfy the finite ladder. This supplies the
chosen-point range used by a row refinement comparison once its genuine row action is given.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- Every original finite-stage comparison cone has the stated linear structure range. -/
theorem modelDiagramIterate_cone_structure_bijective (i : ℕ) (F : C ⥤ Model.{w})
    (X : C) (n k : ℕ) (hk : k + 2 < 2 * n + 2) :
    Function.Bijective (homotopyGroupMap (N := Fin (k + 2))
      ((mappingCone (StrictSquare.comparison
        (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj
          (Q.obj X)))).structureMap (n + i + 3))
      ((mappingCone (StrictSquare.comparison
        (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj
          (Q.obj X)))).map_point _)) := by
  let G := (strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)
  rw [show n + i + 3 = (n + 1) + i + 2 by omega]
  exact pushoutCone_structure_bijective_of_finite_corners
    (G.map (Q.obj X).left.hom) (G.map (Q.obj X).hom.left)
    (StrictSquare.comparison (G.mapArrow.mapArrow.obj (Q.obj X))) i
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F _)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F _)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F _)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F _)
    (fun m x j hj => modelDiagramIterate_homotopyGroup_subsingleton_at Q i F _ m j hj x)
    (fun m x j hj => modelDiagramIterate_homotopyGroup_subsingleton_at Q i F _ m j hj x)
    (fun m x j hj => modelDiagramIterate_homotopyGroup_subsingleton_at Q i F _ m j hj x)
    (fun m x j hj => modelDiagramIterate_homotopyGroup_subsingleton_at Q i F _ m j hj x)
    (modelDiagramIterate_structure_bijective Q i F _)
    (modelDiagramIterate_structure_bijective Q i F _)
    (modelDiagramIterate_structure_bijective Q i F _)
    (modelDiagramIterate_structure_bijective Q i F _)
    (n + 1) (k + 2) (by omega) (by omega)

end Quillen.KTheory.Bass
