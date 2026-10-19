/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterBottomIndex
public import Quillen.KTheory.Bass.SchemeDoubleTargetShift

/-!
# The actual double Spec representative through second normalization

The original inverse Spec-row comparison and the actual second normalization
send both target representatives to the negative double Laurent inclusion.
The inverse double Laurent Spec corner and both genuine shifts remain explicit.
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
open GlobalSectionChangeIndex StrictDiagramIndexRow GeometricConeInterchange
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))

private theorem transport_negative {A B C D E G : AddCommGrpCat}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ D) (d : D ⟶ C)
    (e : C ⟶ E) (f : E ⟶ G) (j : D ⟶ G)
    (h : a ≫ b = c ≫ d) (k : d ≫ e ≫ f = -j) :
    a ≫ b ≫ e ≫ f = -(c ≫ j) := by
  rw [← Category.assoc a, h]
  simp only [Category.assoc]
  rw [k, Preadditive.comp_neg]

/-- The same inverse finite comparison and second normalization retain their exact minus sign. -/
theorem doubleTargetShift_inverseFiniteIso_stageMap
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    doubleTargetShift (laurentUnderSquareFunctor _) (globalRow P ⋙ prespectrumFunctor) a d ≫
        (stableHomotopyFunctor d).map ((finiteIso P 2).inv.app a) ≫
        (stableHomotopyFunctor d).map
          ((NormalizedStageMap.stageMap squareFunctor 2 (parameterDiagram P)).app
            (specUnder.obj a)) ≫
        (doubleNormalizedShift (parameterDiagram P) (specUnder.obj a) d).hom =
      -((stableHomotopyFunctor ((d + 1) + 1)).map (inv (doubleLaurentRowCorner P a)) ≫
        (stableHomotopyFunctor ((d + 1) + 1)).map
          (doubleLaurentInclusion (parameterDiagram P) (specUnder.obj a))) :=
  transport_negative _ _ _ _ _ _ _ (doubleTargetShift_inverseFiniteIso P a d)
    (doubleTargetShift_stageMap (parameterDiagram P) (specUnder.obj a) d)

end Quillen.PerfectComplexes.GlobalParameterCoefficient
