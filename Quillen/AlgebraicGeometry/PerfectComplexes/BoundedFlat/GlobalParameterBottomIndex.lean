/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientDoubleNegativeRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientTelescope
public import Quillen.KTheory.Bass.StrictDiagramIndexDoubleShift

/-!
# The original first two bottom representatives under the integral Spec row

Both finite index-plus-row isomorphisms preserve the original Laurent target
inclusion and inverse signed shift. Their right corners retain the actual
integral Laurent Spec isomorphism and the original global row isomorphism.
No geometric variable permutation or negative-class redefinition is used.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

universe u

namespace Quillen.PerfectComplexes.GlobalParameterCoefficient

open GlobalSectionChangeIndex CoefficientNegativeRepresentatives
open StrictDiagramIndexRow

private theorem laurentUnderSquare_right_right {R : CommRingCat.{u}} (a : Under R) :
    (laurentUnderSquare R a).right.right = (laurentUnderFunctor R).obj a := rfl

variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- The first actual finite comparison retains the original Laurent Spec corner and signed shift. -/
@[reassoc]
theorem finiteIso_one_targetShift (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    targetShift ((parameterDiagram P).mapArrow.mapArrow.obj (square (specUnder.obj a))) d ≫
        (stableHomotopyFunctor d).map ((finiteIso P 1).hom.app a) =
      (stableHomotopyFunctor (d + 1)).map
          ((parameterDiagram P).map (specSquare.hom.app a).right.right) ≫
        (stableHomotopyFunctor (d + 1)).map
          ((rowSpectrumIso P).hom.app ((laurentUnderFunctor _).obj a)) ≫
        targetShift ((globalRow P ⋙ prespectrumFunctor).mapArrow.mapArrow.obj
          (laurentUnderSquare _ a)) d := by
  have h := StrictDiagramIndexRow.finiteIso_one_targetShift specUnder
    (laurentUnderSquareFunctor _) squareFunctor specSquare (rowSpectrumIso P) a d
  simpa only [finiteIso, globalDiagram, squareFunctor, laurentUnderSquareFunctor,
    laurentUnderSquare_right_right,
    CategoryTheory.Functor.map_comp, Category.assoc] using h

/-- The original second comparison is the first comparison on the original first rows. -/
theorem finiteIso_two_hom :
    (finiteIso P 2).hom =
      (StrictDiagramIndexRow.finiteIso specUnder (laurentUnderSquareFunctor _)
        squareFunctor specSquare (finiteIso P 1) 1).hom :=
  StrictDiagramIndexRow.finiteIso_two_hom specUnder (laurentUnderSquareFunctor _)
    squareFunctor specSquare (rowSpectrumIso P)

/-- The complete double Laurent corner keeps both actual Spec arrows and the original row map. -/
def doubleLaurentRowCorner (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  StrictDiagramIndexRow.doubleTargetCorner specUnder (laurentUnderSquareFunctor _)
    squareFunctor specSquare (rowSpectrumIso P) a

/-- Both genuine representatives commute with the actual second finite Spec-row comparison. -/
@[reassoc]
theorem finiteIso_doubleTargetShift (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    doubleTargetShift squareFunctor (parameterDiagram P) (specUnder.obj a) d ≫
        (stableHomotopyFunctor d).map ((finiteIso P 2).hom.app a) =
      (stableHomotopyFunctor ((d + 1) + 1)).map (doubleLaurentRowCorner P a) ≫
        doubleTargetShift (laurentUnderSquareFunctor _) (globalRow P ⋙ prespectrumFunctor) a d :=
  StrictDiagramIndexRow.finiteIso_doubleTargetShift specUnder (laurentUnderSquareFunctor _)
    squareFunctor specSquare (rowSpectrumIso P) a d

/-- The complete original double Laurent corner has its actual componentwise inverse. -/
instance doubleLaurentRowCorner_isIso (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsIso (doubleLaurentRowCorner P a) := by
  dsimp only [doubleLaurentRowCorner, StrictDiagramIndexRow.doubleTargetCorner]
  infer_instance

private theorem inverse_square {E : Type*} [Category E] {A B C D : E}
    (f : A ⟶ B) (fi : B ⟶ A) (g : C ⟶ D) (gi : D ⟶ C)
    (a : A ⟶ C) (b : B ⟶ D) (h : a ≫ g = f ≫ b)
    (hf : fi ≫ f = 𝟙 B) (hg : g ≫ gi = 𝟙 C) : b ≫ gi = fi ≫ a := by
  calc
    b ≫ gi = (fi ≫ f) ≫ b ≫ gi := by rw [hf, Category.id_comp]
    _ = fi ≫ (a ≫ g) ≫ gi := by
      simpa only [Category.assoc] using congrArg (fun k => fi ≫ k ≫ gi) h.symm
    _ = fi ≫ a := by simp only [Category.assoc, hg, Category.comp_id]

/-- Inverting the actual finite Spec-row comparison preserves the same double representative. -/
@[reassoc]
theorem doubleTargetShift_inverseFiniteIso
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    doubleTargetShift (laurentUnderSquareFunctor _) (globalRow P ⋙ prespectrumFunctor) a d ≫
        (stableHomotopyFunctor d).map ((finiteIso P 2).inv.app a) =
      (stableHomotopyFunctor ((d + 1) + 1)).map (inv (doubleLaurentRowCorner P a)) ≫
        doubleTargetShift squareFunctor (parameterDiagram P) (specUnder.obj a) d := by
  exact inverse_square _ _ _ _ _ _ (finiteIso_doubleTargetShift P a d)
    (by
      rw [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id]
      exact (stableHomotopyFunctor ((d + 1) + 1)).map_id _)
    (by
      rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
      exact (stableHomotopyFunctor d).map_id _)

end Quillen.PerfectComplexes.GlobalParameterCoefficient
