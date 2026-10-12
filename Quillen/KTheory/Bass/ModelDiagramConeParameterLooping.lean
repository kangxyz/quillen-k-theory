/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.ConeParameterLoopingExcision
public import Quillen.KTheory.Bass.ModelDiagramConnectivity

/-!
# Loop-cofiber comparison at every actual finite model-diagram Bass stage

For any original arrow between actual finite Bass stages, the proved model-diagram point
HEP, T1 topology and all-point growth discharge looped excision and stability of the original
loop-cofiber comparison. The shared offset is the maximum of the two actual iteration indices.
No condition is imposed on low levels and no transition stabilization is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i j : ℕ) (F G : C ⥤ Model.{w}) (X Y : C)
  (f : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X) ⟶
    (((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).obj Y))

/-- The original arrow between any two finite model-diagram stages has looped stable excision. -/
theorem modelDiagramIterate_parameterLoopingMap_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)) :=
  parameterLoopingMap_coneFiber_isStableEquivalence_of_linearGrowth f (max i j)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F X)
    (modelDiagramIterate_point_homotopyExtensionProperty Q j G Y)
    (fun n x k hk ↦ modelDiagramIterate_homotopyGroup_subsingleton_of_le Q i F X
      (n + max i j + 2) (by omega) k (by omega) x)
    (fun n x k hk ↦ modelDiagramIterate_homotopyGroup_subsingleton_of_le Q j G Y
      (n + max i j + 2) (by omega) k (by omega) x)

/-- The unchanged loop-cofiber comparison is stable at every actual finite model-diagram stage. -/
theorem modelDiagramIterate_mappingConeParameterLoopingComparison_isStableEquivalence :
    IsStableEquivalence (mappingConeParameterLoopingComparison f) :=
  mappingConeParameterLoopingComparison_isStableEquivalence_of_linearGrowth f (max i j)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F X)
    (modelDiagramIterate_point_homotopyExtensionProperty Q j G Y)
    (fun n x k hk ↦ modelDiagramIterate_homotopyGroup_subsingleton_of_le Q i F X
      (n + max i j + 2) (by omega) k (by omega) x)
    (fun n x k hk ↦ modelDiagramIterate_homotopyGroup_subsingleton_of_le Q j G Y
      (n + max i j + 2) (by omega) k (by omega) x)

end Quillen.KTheory.Bass
