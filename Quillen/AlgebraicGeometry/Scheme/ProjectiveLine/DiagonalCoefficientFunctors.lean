/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact
public import Aglib.AlgebraicGeometry.Modules.Tensor.Symmetry
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalAllCoefficientTensor
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalAllCoefficientPushforward
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatPullback
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ClosedPushforwardExactness
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.TensorDerivedPushforward

/-! # Exact original diagonal coefficient functors

These use the original first pullback and tensor with each original diagonal
sequence vertex. Exactness is proved for all module sheaves; no coefficient
flatness or perfect representative is assumed.
-/

@[expose] public section
open Quillen
open Quillen.SchemeSheaf


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (moduleTensorRightLeftIso moduleTensorRight_preservesHomology)
end Quillen.SchemeSheaf

end


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
  AlgebraicGeometry SheafOfModulesOfCommRing
namespace AlgebraicGeometry.Scheme.Modules
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

/-- The original first projection is flat, being base change of the original flat projection. -/
instance diagonalCoefficientFirst_flat : Flat (relativeFirst R) := by
  dsimp [relativeFirst]
  infer_instance

/-- The original coefficient functor at a fixed vertex of the diagonal sequence. -/
def diagonalCoefficientFunctor (A : (relativeSquare R).Modules) :
    (twoChartLine R).Modules ⥤ (relativeSquare R).Modules :=
  Scheme.Modules.pullback (relativeFirst R) ⋙ moduleTensorRightFunctor (relativeSquare R) A

/-- An original sequence arrow induces its original coefficient natural transformation. -/
def diagonalCoefficientMap {A B : (relativeSquare R).Modules} (g : A ⟶ B) :
    diagonalCoefficientFunctor R A ⟶ diagonalCoefficientFunctor R B where
  app E := (moduleTensorLeftFunctor (relativeSquare R)
    ((Scheme.Modules.pullback (relativeFirst R)).obj E)).map g
  naturality {_ _} f := (moduleTensorCoefficientMap (relativeSquare R)
    ((Scheme.Modules.pullback (relativeFirst R)).map f)).naturality g |>.symm

/-- Tensoring the original coefficient map with a fixed original vertex is additive. -/
instance diagonalCoefficientFunctor_additive (A : (relativeSquare R).Modules) :
    (diagonalCoefficientFunctor R A).Additive := by
  dsimp [diagonalCoefficientFunctor]
  infer_instance

/-- The literal original projection-formula and section comparison, natural in all coefficients. -/
def diagonalCoefficientThirdIso :
    diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₃ ≅
      moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R) ⋙
        Scheme.Modules.pushforward (relativeDiagonal R) := by
  let P := Scheme.Modules.pullback (relativeFirst R)
  let D := Scheme.Modules.pullback (relativeDiagonal R)
  let J := Scheme.Modules.pushforward (relativeDiagonal R)
  let T := moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)
  let e := sectionPullbackIso (relativeDiagonal R) (relativeFirst R)
    (relativeDiagonal_first R)
  exact NatIso.ofComponents
    (fun E => diagonalTensorPushforwardIso_all R E (tautologicalQuotientLine R))
    (fun {E E'} f => by
      have hp : (moduleTensorRightFunctor (relativeSquare R)
          (J.obj (tautologicalQuotientLine R))).map (P.map f) ≫
            projectionFormulaMap (relativeDiagonal R) (P.obj E') (tautologicalQuotientLine R) =
          projectionFormulaMap (relativeDiagonal R) (P.obj E) (tautologicalQuotientLine R) ≫
            J.map (T.map (D.map (P.map f))) :=
        (projectionFormulaNatTrans (relativeDiagonal R)
          (tautologicalQuotientLine R)).naturality (P.map f)
      have hs : D.map (P.map f) ≫ e.hom.app E' = e.hom.app E ≫ f := e.hom.naturality f
      change (moduleTensorRightFunctor (relativeSquare R)
        (J.obj (tautologicalQuotientLine R))).map (P.map f) ≫
        (projectionFormulaMap (relativeDiagonal R) (P.obj E') _ ≫
        J.map (T.map (e.hom.app E'))) =
        (projectionFormulaMap (relativeDiagonal R) (P.obj E) _ ≫
          J.map (T.map (e.hom.app E))) ≫ J.map (T.map f)
      rw [← Category.assoc, hp, Category.assoc, ← J.map_comp, ← T.map_comp, hs,
        T.map_comp, J.map_comp, Category.assoc])

/-- The first original coefficient vertex is exact on all module coefficients. -/
instance diagonalCoefficientFirst_preservesHomology :
    (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₁).PreservesHomology := by
  let A := (diagonalIncidenceSequence R).X₁
  let P := Scheme.Modules.pullback (relativeFirst R)
  let T := moduleTensorRightFunctor (relativeSquare R) A
  let : IsFiniteLocallyFree (relativeSquare R) A := by
    dsimp [A, diagonalIncidenceSequence]
    infer_instance
  let : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesHomology T
  let : PreservesFiniteColimits T := Functor.preservesFiniteColimits_of_preservesHomology T
  let : PreservesFiniteLimits (P ⋙ T) := by infer_instance
  let : PreservesFiniteColimits (P ⋙ T) := by infer_instance
  exact (inferInstance : (P ⋙ T).PreservesHomology)

/-- The second original coefficient vertex is exact on all module coefficients. -/
instance diagonalCoefficientSecond_preservesHomology :
    (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₂).PreservesHomology := by
  let A := (diagonalIncidenceSequence R).X₂
  let P := Scheme.Modules.pullback (relativeFirst R)
  let T := moduleTensorRightFunctor (relativeSquare R) A
  let : IsFiniteLocallyFree (relativeSquare R) A := by
    dsimp [A, diagonalIncidenceSequence]
    infer_instance
  let : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesHomology T
  let : PreservesFiniteColimits T := Functor.preservesFiniteColimits_of_preservesHomology T
  let : PreservesFiniteLimits (P ⋙ T) := by infer_instance
  let : PreservesFiniteColimits (P ⋙ T) := by infer_instance
  exact (inferInstance : (P ⋙ T).PreservesHomology)

/-- Exactness of the third original functor follows from its actual closed projection formula. -/
instance diagonalCoefficientThird_preservesHomology :
    (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₃).PreservesHomology := by
  let : IsClosedImmersion (relativeDiagonal R) := isClosedImmersion_relativeDiagonal R
  let G := moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R) ⋙
    Scheme.Modules.pushforward (relativeDiagonal R)
  let : PreservesFiniteLimits G := by
    let : PreservesFiniteLimits (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)) := Functor.preservesFiniteLimits_of_preservesHomology _
    dsimp [G]
    infer_instance
  let : PreservesFiniteColimits G := by
    let : PreservesFiniteColimits (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)) := Functor.preservesFiniteColimits_of_preservesHomology _
    dsimp [G]
    infer_instance
  let : PreservesFiniteLimits (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₃) :=
    preservesFiniteLimits_of_natIso (diagonalCoefficientThirdIso R).symm
  let : PreservesFiniteColimits (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₃) :=
    preservesFiniteColimits_of_natIso (diagonalCoefficientThirdIso R).symm
  infer_instance
end AlgebraicGeometry.Scheme.ProjectiveLine
