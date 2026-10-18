/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientNull
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFullCurrentNull

/-! # The named original full-open null retains every time under integral Spec-row transport -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open GlobalSectionChangeIndex GlobalParameterCoefficient
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))

example (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((ParameterModels.supported f.left).obj (specUnder.obj a))).space n) :
    (prespectrumMap ((parameterRowModelIso P).hom.app a)).map n
      (((ParameterFullCurrentNull.fullNull f.left).homotopy (specUnder.obj a)).level n (s, x)) =
      (prespectrumMap ((globalOpenRestriction f).app a)).map n
        (((globalSupportedOpenNull f).homotopy a).level n
          (s, (prespectrumMap ((parameterSupportedRowIso f).hom.app a)).map n x)) :=
  fullNull_row_square f a n s x

example (s : unitInterval)
    (x : (prespectrum ((ParameterModels.supported f.left).obj (specUnder.obj a))).space 0) :
    (prespectrumMap ((parameterCoefficientRestriction P).app a)).map 0
      (((ParameterFullCurrentNull.fullNull f.left).homotopy (specUnder.obj a)).level 0 (s, x)) =
      (prespectrumMap (boundedFlatCoefficientOpenRestrictionModelMap f a)).map 0
        (((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a).level 0
          (s, (prespectrumMap (((parameterSupportedRowIso f).hom.app a) ≫
            (supportedRowRestriction f).app a)).map 0 x)) :=
  fullNull_coefficient_square f a 0 s x

#print axioms supportedFullRestriction_model_square
#print axioms fullNull_row_square
#print axioms fullNull_coefficient_square
