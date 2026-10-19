/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictDiagramFiniteStructure
public import Quillen.KTheory.Bass.ModelDiagramConnectivity
public import Quillen.KTheory.Bass.StrictDiagramIteration
public import Quillen.Waldhausen.SConstruction.Iterated.OmegaSpectrum

/-!
# Actual finite structure range at every model Bass stage

Only stage zero uses the model Omega-spectrum theorem. Successors use the genuine finite
span-cone-loop ladder, together with the already proved original stage topology and growth.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- Every original finite Bass stage has the actual slope-two chosen-point structure range. -/
theorem modelDiagramIterate_structure_bijective (i : ℕ) (F : C ⥤ Model.{w})
    (X : C) (n j : ℕ) (hj : 0 < j) (hr : j < 2 * n + 2) :
    Function.Bijective (homotopyGroupMap (N := Fin j)
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).structureMap
        (n + i + 2))
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).map_point _)) := by
  induction i generalizing X n j with
  | zero =>
    exact based_bijective_of_weak _ _ (prespectrum_isOmega (F.obj X) _) j
  | succ i ih =>
    rw [strictDiagramIterate_succ_right]
    exact strictDiagramFunctor_structure_bijective Q
      ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)) i
      (modelDiagramIterate_point_homotopyExtensionProperty Q i F)
      (fun Y m x k hk => modelDiagramIterate_homotopyGroup_subsingleton_at Q i F Y m k hk x)
      (fun Y m k hk hr => ih Y m k hk hr) X n j hj hr

end Quillen.KTheory.Bass
