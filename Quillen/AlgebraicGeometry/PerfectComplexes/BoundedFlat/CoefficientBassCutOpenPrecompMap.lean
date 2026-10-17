/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompAttachments
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenMap

/-! Source-domain precomposition maps both displayed cylinders, retaining each original clock. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenPrecomp
open CutOpenCarrier
variable {U V W T : Model.{u}} (A : U ⟶ V) (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε₀ ε₁ : G.functor ≅ (F ≫ J).functor)

/-- The whole reference nerve changes its source domain by the actual model morphism. -/
def parameterMap {W : Model.{u}} (H : V ⟶ W) :
    |parameterSSet H| ⟶ |parameterSSet (A ≫ H)| :=
  SSet.toTop.map (nerveMap (Codiscrete.functorOfFun (precompNode A)))

/-- The ordinary or shifted full attachment equality survives realization. -/
theorem attachment_square (ε : G.functor ≅ (F ≫ J).functor) :
    SSet.toTop.map (attaching F J G ε) ≫ parameterMap A G =
      parameterMap A F ≫ SSet.toTop.map (attaching (A ≫ F) J (A ≫ G) (anchor A F J G ε)) := by
  exact (Functor.map_comp SSet.toTop _ _).symm.trans
    ((congrArg (fun f ↦ SSet.toTop.map f) (attachment_simplicial A F J G ε)).trans
      (Functor.map_comp SSet.toTop _ _))

theorem erase_square :
    SSet.toTop.map (erase F) ≫ 𝟙 _ = parameterMap A F ≫ SSet.toTop.map (erase (A ≫ F)) := by
  dsimp only [parameterMap]
  rw [Category.comp_id, ← Functor.map_comp]
  exact congrArg (fun f ↦ SSet.toTop.map f) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- The ordinary sheet map is the existing strict map of its actual displayed double cylinders. -/
def firstMap : |firstSimplicial F J G ε₀| ⟶
    |firstSimplicial (A ≫ F) J (A ≫ G) (anchor A F J G ε₀)| :=
  CutOpenMap.firstMap F J G (A ≫ F) J (A ≫ G) ε₀ (anchor A F J G ε₀)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀)

@[reassoc] theorem firstMap_left :
    SSet.toTop.map (left₀ F J G ε₀) ≫ firstMap A F J G ε₀ =
      parameterMap A G ≫ SSet.toTop.map (left₀ (A ≫ F) J (A ≫ G) (anchor A F J G ε₀)) :=
  CutOpenMap.firstMap_left F J G (A ≫ F) J (A ≫ G) ε₀ (anchor A F J G ε₀)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀)

@[reassoc] theorem firstMap_right :
    SSet.toTop.map (right₀ F J G ε₀) ≫ firstMap A F J G ε₀ =
      SSet.toTop.map (right₀ (A ≫ F) J (A ≫ G) (anchor A F J G ε₀)) :=
  CutOpenMap.firstMap_right F J G (A ≫ F) J (A ≫ G) ε₀ (anchor A F J G ε₀)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀)

/-- The shifted sheet uses its own full anchor, followed by the already checked ordinary map. -/
theorem second_square :
    SSet.toTop.map (secondAttaching F J G ε₀ ε₁) ≫ firstMap A F J G ε₀ =
      parameterMap A F ≫ SSet.toTop.map
        (secondAttaching (A ≫ F) J (A ≫ G) (anchor A F J G ε₀) (anchor A F J G ε₁)) :=
  CutOpenMap.second_square F J G (A ≫ F) J (A ≫ G) ε₀ ε₁ (anchor A F J G ε₀) (anchor A F J G ε₁)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀) (attachment_square A F J G ε₁)

/-- Two applications of the existing double-cylinder map retain the complete original carrier. -/
def map : space F J G ε₀ ε₁ ⟶
    space (A ≫ F) J (A ≫ G) (anchor A F J G ε₀) (anchor A F J G ε₁) :=
  CutOpenMap.map F J G (A ≫ F) J (A ≫ G) ε₀ ε₁ (anchor A F J G ε₀) (anchor A F J G ε₁)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀) (attachment_square A F J G ε₁)

@[reassoc] theorem map_first :
    SSet.toTop.map (left₁ F J G ε₀ ε₁) ≫ map A F J G ε₀ ε₁ =
      firstMap A F J G ε₀ ≫ SSet.toTop.map
        (left₁ (A ≫ F) J (A ≫ G) (anchor A F J G ε₀) (anchor A F J G ε₁)) :=
  CutOpenMap.map_first F J G (A ≫ F) J (A ≫ G) ε₀ ε₁ (anchor A F J G ε₀) (anchor A F J G ε₁)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀) (attachment_square A F J G ε₁)

@[simp] theorem map_tipPlus :
    map A F J G ε₀ ε₁ (tipPlus F J G ε₀ ε₁) =
      tipPlus (A ≫ F) J (A ≫ G) (anchor A F J G ε₀) (anchor A F J G ε₁) :=
  CutOpenMap.map_tipPlus F J G (A ≫ F) J (A ≫ G) ε₀ ε₁ (anchor A F J G ε₀) (anchor A F J G ε₁)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀) (attachment_square A F J G ε₁)

@[simp] theorem map_tipMinus :
    map A F J G ε₀ ε₁ (tipMinus F J G ε₀ ε₁) =
      tipMinus (A ≫ F) J (A ≫ G) (anchor A F J G ε₀) (anchor A F J G ε₁) :=
  CutOpenMap.map_tipMinus F J G (A ≫ F) J (A ≫ G) ε₀ ε₁ (anchor A F J G ε₀) (anchor A F J G ε₁)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀) (attachment_square A F J G ε₁)

@[simp] theorem map_laurent (x : |parameterSSet G|) :
    map A F J G ε₀ ε₁ (laurentInclusion F J G ε₀ ε₁ x) =
      laurentInclusion (A ≫ F) J (A ≫ G) (anchor A F J G ε₀) (anchor A F J G ε₁)
        (parameterMap A G x) :=
  CutOpenMap.map_laurent F J G (A ≫ F) J (A ≫ G) ε₀ ε₁ (anchor A F J G ε₀) (anchor A F J G ε₁)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀) (attachment_square A F J G ε₁) x

@[simp] theorem map_cylinderMinus (x : |parameterSSet F|) (t : I) :
    map A F J G ε₀ ε₁ (cylinderMinus F J G ε₀ ε₁ (x, t)) =
      cylinderMinus (A ≫ F) J (A ≫ G) (anchor A F J G ε₀) (anchor A F J G ε₁)
        (parameterMap A F x, t) :=
  CutOpenMap.map_cylinderMinus F J G (A ≫ F) J (A ≫ G) ε₀ ε₁ (anchor A F J G ε₀) (anchor A F J G ε₁)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀) (attachment_square A F J G ε₁) x t

@[simp] theorem map_cylinderPlus (x : |parameterSSet F|) (t : I) :
    map A F J G ε₀ ε₁ (cylinderPlus F J G ε₀ ε₁ (x, t)) =
      cylinderPlus (A ≫ F) J (A ≫ G) (anchor A F J G ε₀) (anchor A F J G ε₁)
        (parameterMap A F x, t) :=
  CutOpenMap.map_cylinderPlus F J G (A ≫ F) J (A ≫ G) ε₀ ε₁ (anchor A F J G ε₀) (anchor A F J G ε₁)
    (parameterMap A F) (parameterMap A G)
    (attachment_square A F J G ε₀) (attachment_square A F J G ε₁) x t

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenPrecomp
