/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentNegativeCorrection
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFiniteNegativeComparison

/-!
# The original negative-class correction in the specified normalized stage

The independently defined correction on the original negative group is carried
by its fixed normalized class comparison to the actual conjugating word. This
is only a conjugation square: no finite word or quotient permutation is assigned
a sign or identified with an identity.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open SchemeNaturalSeed NormalizedStageMap GlobalSectionChangeIndex
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
  [CompactSpace P.left]

/-- The fixed normalized comparison is the original finite comparison and actual stage map. -/
theorem normalizedNegativeKComparison_finite (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (normalizedNegativeKComparison P i a).hom =
      (finiteNegativeKComparison P i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((stageMap squareFunctor i (parameterDiagram P)).app (specUnder.obj a)) := by
  rw [normalizedNegativeKComparison_hom, finiteNegativeKComparison_hom_app]
  simp only [Category.assoc]

/-- Original finite correction retains the same actual conjugating word after normalization. -/
@[reassoc]
theorem negativeClassCorrection_normalized (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection P i a).hom ≫ (normalizedNegativeKComparison P i a).hom =
      (normalizedNegativeKComparison P i a).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((conjugatingIso i (parameterDiagram P)).hom.app (specUnder.obj a)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let e := (stageMap squareFunctor i (parameterDiagram P)).app (specUnder.obj a)
  let : IsIso (H.map e) := model_stageMap_stable squareFunctor i
    (ParameterModels.ambient P.left) (specUnder.obj a) (-(i : ℤ))
  simp only [normalizedNegativeKComparison_finite]
  change ((finiteNegativeKComparison P i).hom.app a ≫
      (H.map e ≫ H.map ((conjugatingIso i (parameterDiagram P)).hom.app (specUnder.obj a)) ≫
        inv (H.map e)) ≫ (finiteNegativeKComparison P i).inv.app a) ≫
      ((finiteNegativeKComparison P i).hom.app a ≫ H.map e) = _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, IsIso.inv_hom_id, Category.comp_id]
  rfl

end Quillen.PerfectComplexes.GlobalParameterCoefficient
