/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationCutSimplex

/-!
# Actual evaluation-cut simplex regression

The entire trailing simplicial face agrees with the original postcomposed binary
comparison. Independent triangle and level-zero loop coordinates remain independent.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.PerfectComplexes.CoefficientSectionEvaluationCutSimplex
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.CoefficientSectionEvaluationCutSimplex
variable {R : CommRingCat.{u}} {i j k l : Index R}
  (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)

/-- The original binary route used in the actual trailing face. -/
def oldTriangle : ModelSimplex (boundedFlatCoefficientSectionModel i)
    (modelOf (boundedFlatPerfectWaldhausen (space k))) 2 :=
  ModelSimplex.triangle
    (F := boundedFlatCoefficientSectionModelMap (f ≫ g) ≫
      boundedFlatCoefficientSectionEvaluationModelMap k)
    (G := (boundedFlatCoefficientSectionModelMap f ≫
      boundedFlatCoefficientSectionEvaluationModelMap j) ≫
        boundedFlatCoefficientOriginalModelMap g)
    (H := (boundedFlatCoefficientSectionEvaluationModelMap i ≫
      boundedFlatCoefficientOriginalModelMap f) ≫ boundedFlatCoefficientOriginalModelMap g)
    (boundedFlatCoefficientSectionModelFirstRouteIso f g).hom
    (boundedFlatCoefficientSectionModelSecondRouteIso f g).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)

/-- The restriction is an equality of full simplicial transformations. -/
theorem whole_simplicial_face (n : ℕ) :
    stageTransformationSimplex n ((simplex f g h).face (SimplexCategory.δ 0)) =
      stageTransformationSimplex n (oldTriangle f g) ≫
        (stages n).map (boundedFlatCoefficientOriginalModelMap h) := by
  rw [last_face_postcomp, stageTransformationSimplex_postcomp]
  rfl

/-- The restriction retains every barycentric parameter, not only the composition clock. -/
theorem whole_barycentric_face (n : ℕ) (z : StdSimplex ℝ (Fin 3))
    (x : (prespectrum (boundedFlatCoefficientSectionModel i)).space n) :
    family f g h n (StdSimplex.map (SimplexCategory.δ 0).toOrderHom z, x) =
      (prespectrumMap (boundedFlatCoefficientOriginalModelMap h)).map n
        (prespectrumSimplexFamily (oldTriangle f g) n (z, x)) := by
  change prespectrumSimplexFamily _ _ _ = _
  rw [prespectrumSimplexFamily_face, last_face_postcomp, prespectrumSimplexFamily_postcomp]
  rfl

/-- The two original triangle clocks remain independent of the level-zero loop clock. -/
theorem independent_loop_time (r s t : unitInterval)
    (x : Path (stagePoint 0 (boundedFlatCoefficientSectionModel i))
      (stagePoint 0 (boundedFlatCoefficientSectionModel i))) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space l))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space l)))) from
        family f g h 0
          (StdSimplex.map (SimplexCategory.δ 0).toOrderHom
            (Quillen.TheoremB.compositionTriangleHomotopy (r, s)), x)) t =
      stageSimplexBarycentric (simplex f g h) 0
        (StdSimplex.map (SimplexCategory.δ 0).toOrderHom
          (Quillen.TheoremB.compositionTriangleHomotopy (r, s)), x t) :=
  prespectrumSimplexFamily_zero_apply _ _ _ _

end QuillenTest.CoefficientSectionEvaluationCutSimplex
