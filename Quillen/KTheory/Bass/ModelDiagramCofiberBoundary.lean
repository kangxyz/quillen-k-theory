/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.ModelDiagramCofiberPreservation
public import Quillen.Topology.Prespectrum.ConeDescStableEquivalence

/-!
# The original signed boundary after Bass cofiber preservation

Actual finite Model growth discharges cone-fiber excision for the unchanged Bass image map.
Consequently its original signed cone boundary is carried to the original fiber boundary by
the actual Bass null descent and its specified fiber lift. This is a single-boundary naturality
identity; no sign law for swapping two successive cone boundaries is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (i j : ℕ) (F G : C ⥤ Model.{w})
    (a : (strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor) ⟶
      (strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor))

/-- Actual finite Model growth proves excision for the unchanged Bass image of the original map. -/
theorem modelDiagramBassMap_coneFiber_isStableEquivalence (X : C) :
    IsStableEquivalence (mappingConeFiberComparison (((strictDiagramFunctor Q).map a).app X)) := by
  let S := (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj
    (Q.obj X))
  let T := (((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj
    (Q.obj X))
  let : ∀ m, T1Space ((mappingCone (StrictSquare.comparison S)).space m) :=
    modelDiagramSquareConeSpaceT1Space Q i F (Q.obj X)
  let : ∀ m, T1Space ((mappingCone (StrictSquare.comparison T)).space m) :=
    modelDiagramSquareConeSpaceT1Space Q j G (Q.obj X)
  change IsStableEquivalence (mappingConeFiberComparison
    (parameterLoopingMap (mappingConeMap
      (strictSquareComparisonFunctor.map (diagramSquareMap a (Q.obj X))))))
  exact parameterLoopingMap_coneFiber_isStableEquivalence_of_linearGrowth
    (E := mappingCone (StrictSquare.comparison S)) (F := mappingCone (StrictSquare.comparison T))
    (mappingConeMap (strictSquareComparisonFunctor.map (diagramSquareMap a (Q.obj X))))
    (max i j) (modelDiagramSquareCone_point_homotopyExtensionProperty Q i F (Q.obj X))
    (modelDiagramSquareCone_point_homotopyExtensionProperty Q j G (Q.obj X))
    (fun n x k hk ↦ modelDiagramSquareCone_homotopyGroup_subsingleton Q i F (Q.obj X)
      (n + max i j + 2) n (by omega) x k hk)
    (fun n x k hk ↦ modelDiagramSquareCone_homotopyGroup_subsingleton Q j G (Q.obj X)
      (n + max i j + 2) n (by omega) x k hk)

/-- The actual Bass null descent carries the original signed cone boundary to its fiber boundary. -/
theorem modelDiagramCofiberDesc_bass_connecting
    {K : C ⥤ LoopPrespectrum.{w}}
    (b : (strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor) ⟶ K)
    (N : ∀ X, Homotopy (a.app X ≫ b.app X)
      (zeroHom (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X) (K.obj X)))
    (hN : ∀ {X Y} (f : X ⟶ Y) n r x,
      (K.map f).map n ((N X).level n (r, x)) =
        (N Y).level n (r, (((strictDiagramIterate Q i).obj
          (F ⋙ prespectrumFunctor)).map f).map n x)) (X : C) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        (mappingConeDesc (((strictDiagramFunctor Q).map a).app X)
          (((strictDiagramFunctor Q).map b).app X) (strictDiagramNullHomotopy a b N hN Q X)) ≫
      stableFiberConnecting (((strictDiagramFunctor Q).map b).app X) d =
    stableMappingConeConnecting (((strictDiagramFunctor Q).map a).app X)
      (modelDiagramBassMap_coneFiber_isStableEquivalence Q i j F G a X) d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          (((strictDiagramFunctor Q).map b).app X) (((strictDiagramFunctor Q).map a).app X)
          (strictDiagramNullHomotopy a b N hN Q X)) :=
  mappingConeDesc_connecting _ _ _
    (modelDiagramBassMap_coneFiber_isStableEquivalence Q i j F G a X) d

end Quillen.KTheory.Bass
