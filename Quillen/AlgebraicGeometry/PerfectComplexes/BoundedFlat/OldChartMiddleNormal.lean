/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionMiddleRightNormal

/-! Exact normalized middle node in the unchanged coefficient-composition chart. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassReferenceMerge
section Schemes
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

abbrev mergedMiddleGeom := (DoubleSquareTrack.middle_eq p q q' b c hq).symm

include hq in
theorem mergedMiddleSourceEq : (NormalizedTripleSimplex.sourceMap c q p).functor =
    (BinaryNormalizationSimplex.sourceMap q' (b ≫ p)).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (mergedMiddleGeom p q q' b c hq))

/-- The full actual middle node retains its original source-square equality and normalization. -/
theorem merged_middle_normal : DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 5 =
    (⟨BinaryNormalizationSimplex.targetMap q' (b ≫ p),
      eqToIso (mergedMiddleSourceEq p q q' b c hq) ≪≫
        BinaryNormalizationSimplex.total q' (b ≫ p)⟩ :
      DoubleSquareCommonSimplex.Node p q c) := by
  have hf : (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 5).1.functor =
      (BinaryNormalizationSimplex.targetMap q' (b ≫ p)).functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
    (DoubleSquareTrack.middle_eq p q q' b c hq).symm)) ≪≫
      smallIso (boundedFlatNormalizedPullbackCompIso q' (b ≫ p)) = _
  rw [smallIso_eqToIso]
  rfl
end Schemes

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

abbrev oldChartMiddleGeom := mergedMiddleGeom
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((laurentUnderFunctor R).map v))
  (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
  (coefficientTransformation_naturality P α v).symm

abbrev oldChartMiddleSourceEq := mergedMiddleSourceEq
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((laurentUnderFunctor R).map v))
  (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
  (coefficientTransformation_naturality P α v).symm

/-- The original chart's whole dependent middle node has this exact normalized representation. -/
theorem old_chart_middle_normal : BassOverlap.chartNodes P u v α 5 =
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u)),
      eqToIso (oldChartMiddleSourceEq P u v α) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))⟩ :
      DoubleSquareCommonSimplex.Node
        (coefficientMap P ((polynomialUnderFunctor R).map u))
        (coefficientMap P ((polynomialUnderFunctor R).map v)) (coefficientMap P (α.app c))) :=
  merged_middle_normal
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientTransformation_naturality P α u).symm
    (coefficientTransformation_naturality P α v).symm

end Quillen.PerfectComplexes.BassH1Join
