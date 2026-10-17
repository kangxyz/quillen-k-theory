/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedOriginalAnchorNodes
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenMap

/-! The original chosen two-sheet carrier maps through its exact anchor normalization. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedOriginalAnchorMap
open BassH0Merge CommonReferenceNerve CommonReferenceProduct
open CoefficientBassSeedOriginalAnchorNormalization
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R}
  (p : a ⟶ b) (q : b ⟶ c)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
local notation "j" => coefficientMap P (α.app c)
local notation "g" => coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) q) ≫
  coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) p)
local notation "h" => polynomialProjection P a
local notation "D" => BassOverlap.projectionMap P (a := a) ≫ BassMOuterJoin.sideBinarySource P p q
local notation "G" => BassOverlap.commonReference P p q

open CutOpenCarrier
local notation "ε" => BassMOuterJoin.oldSideIso P p q α hc
local notation "η" => normalizedAnchor P p q α hc
local notation "τ" => LaurentUnitReferenceSpecialization.commonUnit P p q

/-- The actual normalization map of the original polynomial reference nerve. -/
def polynomialMap : |parameterSSet D| ⟶ |parameterSSet (normalizedMap (g ≫ h))| :=
  SSet.toTop.map (nerveMap (Codiscrete.functorOfFun
    (reanchor (BinaryNormalizationSimplex.total g h))))

/-- The ordinary full attaching square is the already proved whole-parameter equality. -/
theorem ordinary_square :
    SSet.toTop.map (attaching D (normalizedMap j) G ε) ≫ 𝟙 _ =
      polynomialMap P p q ≫
        SSet.toTop.map (attaching (normalizedMap (g ≫ h)) (normalizedMap j) G η) := by
  ext x
  exact CoefficientBassSeedOriginalAnchorNodes.ordinary_parameter P p q α hc x

/-- The second attaching square retains the actual common-unit shifted anchor. -/
theorem shifted_square :
    SSet.toTop.map (attaching D (normalizedMap j) G (τ ≪≫ ε)) ≫ 𝟙 _ =
      polynomialMap P p q ≫
        SSet.toTop.map (attaching (normalizedMap (g ≫ h)) (normalizedMap j) G (τ ≪≫ η)) := by
  ext x
  exact CoefficientBassSeedOriginalAnchorNodes.shifted_parameter P p q α hc x

/-- Map each original chosen carrier point using its two full attaching squares. -/
def map : space D (normalizedMap j) G ε (τ ≪≫ ε) ⟶
    space (normalizedMap (g ≫ h)) (normalizedMap j) G η (τ ≪≫ η) :=
  CutOpenMap.map D (normalizedMap j) G (normalizedMap (g ≫ h)) (normalizedMap j) G
    ε (τ ≪≫ ε) η (τ ≪≫ η) (polynomialMap P p q) (𝟙 _)
    (ordinary_square P p q α hc) (shifted_square P p q α hc)

/-- The original tipMinus cell keeps its exact coordinate. -/
@[simp] theorem map_tipMinus :
    map P p q α hc (tipMinus D (normalizedMap j) G ε (τ ≪≫ ε)) =
      tipMinus (normalizedMap (g ≫ h)) (normalizedMap j) G η (τ ≪≫ η) :=
  CutOpenMap.map_tipMinus D (normalizedMap j) G (normalizedMap (g ≫ h)) (normalizedMap j) G
    ε (τ ≪≫ ε) η (τ ≪≫ η) (polynomialMap P p q) (𝟙 _)
    (ordinary_square P p q α hc) (shifted_square P p q α hc)

/-- The original tipPlus cell keeps its exact coordinate. -/
@[simp] theorem map_tipPlus :
    map P p q α hc (tipPlus D (normalizedMap j) G ε (τ ≪≫ ε)) =
      tipPlus (normalizedMap (g ≫ h)) (normalizedMap j) G η (τ ≪≫ η) :=
  CutOpenMap.map_tipPlus D (normalizedMap j) G (normalizedMap (g ≫ h)) (normalizedMap j) G
    ε (τ ≪≫ ε) η (τ ≪≫ η) (polynomialMap P p q) (𝟙 _)
    (ordinary_square P p q α hc) (shifted_square P p q α hc)

/-- The original laurent cell keeps its exact coordinate. -/
@[simp] theorem map_laurent (x : |parameterSSet G|) :
    map P p q α hc (laurentInclusion D (normalizedMap j) G ε (τ ≪≫ ε) x) =
      laurentInclusion (normalizedMap (g ≫ h)) (normalizedMap j) G η (τ ≪≫ η) x :=
  CutOpenMap.map_laurent D (normalizedMap j) G (normalizedMap (g ≫ h)) (normalizedMap j) G
    ε (τ ≪≫ ε) η (τ ≪≫ η) (polynomialMap P p q) (𝟙 _)
    (ordinary_square P p q α hc) (shifted_square P p q α hc) x

/-- The original cylinderMinus cell keeps its exact coordinate. -/
@[simp] theorem map_cylinderMinus (x : |parameterSSet D|) (t : I) :
    map P p q α hc (cylinderMinus D (normalizedMap j) G ε (τ ≪≫ ε) (x, t)) =
      cylinderMinus (normalizedMap (g ≫ h)) (normalizedMap j) G η (τ ≪≫ η)
        (polynomialMap P p q x, t) :=
  CutOpenMap.map_cylinderMinus D (normalizedMap j) G (normalizedMap (g ≫ h)) (normalizedMap j) G
    ε (τ ≪≫ ε) η (τ ≪≫ η) (polynomialMap P p q) (𝟙 _)
    (ordinary_square P p q α hc) (shifted_square P p q α hc) x t

/-- The original cylinderPlus cell keeps its exact coordinate. -/
@[simp] theorem map_cylinderPlus (x : |parameterSSet D|) (t : I) :
    map P p q α hc (cylinderPlus D (normalizedMap j) G ε (τ ≪≫ ε) (x, t)) =
      cylinderPlus (normalizedMap (g ≫ h)) (normalizedMap j) G η (τ ≪≫ η)
        (polynomialMap P p q x, t) :=
  CutOpenMap.map_cylinderPlus D (normalizedMap j) G (normalizedMap (g ≫ h)) (normalizedMap j) G
    ε (τ ≪≫ ε) η (τ ≪≫ η) (polynomialMap P p q) (𝟙 _)
    (ordinary_square P p q α hc) (shifted_square P p q α hc) x t

end Quillen.PerfectComplexes.CoefficientBassSeedOriginalAnchorMap
