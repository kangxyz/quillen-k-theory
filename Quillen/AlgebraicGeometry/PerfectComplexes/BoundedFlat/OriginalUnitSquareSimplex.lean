/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OriginalUnitSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeBinaryComparison
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexLiftPasting
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleWhiskering
public import Quillen.Topology.Prespectrum.RelativeOperationEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleSourceTransport

/-! A common finite simplex for the original geometric unit square. All vertices retain the
chosen-zero normalization; the two unit routes retain their actual intermediate functors. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.OriginalUnitSquareSimplex

/-- The genuine normalization intermediate of the original identity track. -/
def unitIntermediate (X : Scheme.{u}) : BoundedFlatPerfect X ⥤ BoundedFlatPerfect X :=
  Quillen.rebaseFunctor (𝟭 (BoundedFlatPerfect X))
    (boundedFlatPerfectWaldhausen X).zero (boundedFlatPerfectWaldhausen X).zero
    (((Waldhausen.IsExact.id (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq).zero (boundedFlatPerfectWaldhausen X).isZero).iso
      (boundedFlatPerfectWaldhausen X).isZero)

/-- The geometric comparison from identity pullback to its rebased intermediate. -/
def unitGeometric (X : Scheme.{u}) :
    boundedFlatNormalizedPullback (𝟙 X) ≅ unitIntermediate X :=
  (boundedFlatPullbackNormalizationIso (𝟙 X)).symm ≪≫
    boundedFlatPerfectPullbackIdIso X ≪≫ Quillen.rebaseFunctorIso _ _ _ _

/-- The normalization from the rebased identity functor to the identity functor. -/
def unitNormalization (X : Scheme.{u}) : unitIntermediate X ≅ 𝟭 (BoundedFlatPerfect X) :=
  (Quillen.rebaseFunctorIso _ _ _ _).symm

theorem unit_composite (X : Scheme.{u}) :
    (unitGeometric X).hom ≫ (unitNormalization X).hom =
      (boundedFlatNormalizedPullbackIdIso X).hom := by
  simp [unitGeometric, unitNormalization, boundedFlatNormalizedPullbackIdIso, Category.assoc]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The model map induced by normalized pullback along the original scheme map. -/
def sourceMap : modelOf (boundedFlatPerfectWaldhausen Y) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact f)
    (boundedFlatNormalizedPullback_obj_zero f)

/-- The target model map of the original right-unit binary normalization. -/
abbrev rightMap := BinaryNormalizationSimplex.targetMap (𝟙 X) f
/-- The target model map of the original left-unit binary normalization. -/
abbrev leftMap := BinaryNormalizationSimplex.targetMap f (𝟙 Y)
/-- The intermediate model map of the first right-unit comparison. -/
abbrev rightFirstMap := BinaryNormalizationSimplex.intermediateMap (𝟙 X) f
/-- The intermediate model map of the first left-unit comparison. -/
abbrev leftFirstMap := BinaryNormalizationSimplex.intermediateMap f (𝟙 Y)

/-- The model map with the rebased identity after the original pullback. -/
def rightSecondMap : modelOf (boundedFlatPerfectWaldhausen Y) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ ((boundedFlatNormalizedPullback_exact f).comp
    (Waldhausen.IsExact.id (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq).rebase)
    (by simp only [comp_obj, boundedFlatNormalizedPullback_obj_zero,
      Quillen.rebaseFunctor_obj_base])

/-- The model map with the rebased identity before the original pullback. -/
def leftSecondMap : modelOf (boundedFlatPerfectWaldhausen Y) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ ((Waldhausen.IsExact.id (boundedFlatPerfectWaldhausen Y).cof
    (boundedFlatPerfectWaldhausen Y).weq).rebase.comp (boundedFlatNormalizedPullback_exact f))
    (by simp only [comp_obj, Quillen.rebaseFunctor_obj_base,
      boundedFlatNormalizedPullback_obj_zero])

/-- The first unsplit right-unit comparison from the original source map. -/
def rightFirst : (sourceMap f).functor ≅ (rightMap f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (boundedFlatNormalizedRightUnitFirst f) AsSmall.up)

/-- The second unsplit right-unit comparison back to the original source map. -/
def rightSecond : (rightMap f).functor ≅ (sourceMap f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (boundedFlatNormalizedRightUnitSecond f) AsSmall.up)

/-- The geometric component of the first right-unit comparison. -/
def rightFirstGeometric : (sourceMap f).functor ≅ (rightFirstMap f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (Category.id_comp f).symm) ≪≫
      BinaryNormalizationSimplex.geometricIso (𝟙 X) f) AsSmall.up)

/-- The normalization component of the first right-unit comparison. -/
abbrev rightFirstNormalization := BinaryNormalizationSimplex.second (𝟙 X) f

/-- The geometric component of the second right-unit comparison. -/
def rightSecondGeometric : (rightMap f).functor ≅ (rightSecondMap f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerLeft (boundedFlatNormalizedPullback f) (unitGeometric X)) AsSmall.up)

/-- The normalization component of the second right-unit comparison. -/
def rightSecondNormalization : (rightSecondMap f).functor ≅ (sourceMap f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerLeft (boundedFlatNormalizedPullback f) (unitNormalization X)) AsSmall.up)

theorem right_first_composite :
    (rightFirstGeometric f).hom ≫ (rightFirstNormalization f).hom =
      (rightFirst f).hom := by
  have hh := congrArg (fun η ↦ whiskerLeft AsSmall.down
    (whiskerRight (eqToHom
      (congrArg boundedFlatNormalizedPullback (Category.id_comp f).symm) ≫ η) AsSmall.up))
    (BinaryNormalizationSimplex.composite_hom (𝟙 X) f)
  simpa only [rightFirstGeometric, rightFirstNormalization, BinaryNormalizationSimplex.second,
    rightFirst, boundedFlatNormalizedRightUnitFirst, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, eqToIso.hom, whiskerLeft_comp, whiskerRight_comp, Category.assoc] using hh

theorem right_second_composite :
    (rightSecondGeometric f).hom ≫ (rightSecondNormalization f).hom =
      (rightSecond f).hom := by
  apply NatTrans.ext
  funext A
  simp only [rightSecondGeometric, rightSecondNormalization, rightSecond,
    boundedFlatNormalizedRightUnitSecond, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    rightUnitor_hom_app]
  rw [← Functor.map_comp, ← NatTrans.comp_app, unit_composite]
  exact congrArg (fun k ↦ AsSmall.up.map k) (Category.comp_id _).symm

/-- The first unsplit left-unit comparison from the original source map. -/
def leftFirst : (sourceMap f).functor ≅ (leftMap f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (boundedFlatNormalizedLeftUnitFirst f) AsSmall.up)

/-- The second unsplit left-unit comparison back to the original source map. -/
def leftSecond : (leftMap f).functor ≅ (sourceMap f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (boundedFlatNormalizedLeftUnitSecond f) AsSmall.up)

/-- The geometric component of the first left-unit comparison. -/
def leftFirstGeometric : (sourceMap f).functor ≅ (leftFirstMap f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (Category.comp_id f).symm) ≪≫
      BinaryNormalizationSimplex.geometricIso f (𝟙 Y)) AsSmall.up)

/-- The normalization component of the first left-unit comparison. -/
abbrev leftFirstNormalization := BinaryNormalizationSimplex.second f (𝟙 Y)

/-- The geometric component of the second left-unit comparison. -/
def leftSecondGeometric : (leftMap f).functor ≅ (leftSecondMap f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerRight (unitGeometric Y) (boundedFlatNormalizedPullback f)) AsSmall.up)

/-- The normalization component of the second left-unit comparison. -/
def leftSecondNormalization : (leftSecondMap f).functor ≅ (sourceMap f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerRight (unitNormalization Y) (boundedFlatNormalizedPullback f)) AsSmall.up)

theorem left_first_composite :
    (leftFirstGeometric f).hom ≫ (leftFirstNormalization f).hom =
      (leftFirst f).hom := by
  have hh := congrArg (fun η ↦ whiskerLeft AsSmall.down
    (whiskerRight (eqToHom
      (congrArg boundedFlatNormalizedPullback (Category.comp_id f).symm) ≫ η) AsSmall.up))
    (BinaryNormalizationSimplex.composite_hom f (𝟙 Y))
  simpa only [leftFirstGeometric, leftFirstNormalization, BinaryNormalizationSimplex.second,
    leftFirst, boundedFlatNormalizedLeftUnitFirst, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, eqToIso.hom, whiskerLeft_comp, whiskerRight_comp, Category.assoc] using hh

theorem left_second_composite :
    (leftSecondGeometric f).hom ≫ (leftSecondNormalization f).hom =
      (leftSecond f).hom := by
  apply NatTrans.ext
  funext A
  simp only [leftSecondGeometric, leftSecondNormalization, leftSecond,
    boundedFlatNormalizedLeftUnitSecond, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    leftUnitor_hom_app]
  rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, unit_composite]
  exact congrArg (fun k ↦ AsSmall.up.map k) (Category.comp_id _).symm

theorem two_routes :
    (rightFirst f).hom ≫ (rightSecond f).hom =
      (leftFirst f).hom ≫ (leftSecond f).hom := by
  have hh := congrArg
    (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (boundedFlatNormalizedUnitRoutes_equation f)
  simpa only [rightFirst, rightSecond, leftFirst, leftSecond, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_comp, whiskerRight_comp] using hh

/-- Eight actual functors, including both split identity normalization intermediates. -/
def vertices : Fin 8 → (modelOf (boundedFlatPerfectWaldhausen Y) ⟶
    modelOf (boundedFlatPerfectWaldhausen X)) :=
  ![sourceMap f, rightFirstMap f, rightMap f, rightSecondMap f,
    leftFirstMap f, leftMap f, leftSecondMap f, sourceMap f]

/-- The original source-reference isomorphisms for all eight unit-square vertices. -/
def references : ∀ i, (sourceMap f).functor ≅ (vertices f i).functor :=
  Fin.cases (Iso.refl _) (Fin.cases (rightFirstGeometric f)
    (Fin.cases (rightFirst f) (Fin.cases (rightFirst f ≪≫ rightSecondGeometric f)
      (Fin.cases (leftFirstGeometric f) (Fin.cases (leftFirst f)
        (Fin.cases (leftFirst f ≪≫ leftSecondGeometric f)
          (Fin.cases (rightFirst f ≪≫ rightSecond f) (fun i ↦ Fin.elim0 i))))))))

/-- The common simplex is constructed from the original functors, not supplied as coherence. -/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen Y))
    (modelOf (boundedFlatPerfectWaldhausen X)) 7 :=
  ModelSimplex.ofIsos (sourceMap f) (vertices f) (references f)

/-- The monotone three-vertex face selected by the two given order comparisons. -/
def triangleFace (i j k : Fin 8) (hij : i ≤ j) (hjk : j ≤ k) : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![i, j, k], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [le_trans hij hjk]⟩

theorem right_first_face :
    (simplex f).face (triangleFace 0 1 2 (by decide) (by decide)) =
      ModelSimplex.triangle (rightFirstGeometric f).hom (rightFirstNormalization f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact right_first_composite f

theorem right_second_face :
    (simplex f).face (triangleFace 2 3 7 (by decide) (by decide)) =
      ModelSimplex.triangle (rightSecondGeometric f).hom (rightSecondNormalization f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · change (_ ≫ (rightSecondGeometric f).hom) ≫ (rightSecondNormalization f).hom = _
    rw [Category.assoc, right_second_composite]
    rfl

theorem right_normalized_face :
    (simplex f).face (triangleFace 0 2 7 (by decide) (by decide)) =
      ModelSimplex.triangle (rightFirst f).hom (rightSecond f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · rfl

theorem left_first_face :
    (simplex f).face (triangleFace 0 4 5 (by decide) (by decide)) =
      ModelSimplex.triangle (leftFirstGeometric f).hom (leftFirstNormalization f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact left_first_composite f

theorem left_second_face :
    (simplex f).face (triangleFace 5 6 7 (by decide) (by decide)) =
      ModelSimplex.triangle (leftSecondGeometric f).hom (leftSecondNormalization f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · change (_ ≫ (leftSecondGeometric f).hom) ≫ (leftSecondNormalization f).hom = _
    rw [Category.assoc, left_second_composite]
    exact (two_routes f).symm

theorem left_normalized_face :
    (simplex f).face (triangleFace 0 5 7 (by decide) (by decide)) =
      ModelSimplex.triangle (leftFirst f).hom (leftSecond f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact (two_routes f).symm

/-- The six scalar triangles use the unchanged dyadic composition parameter. -/
def rightFirstParameter :=
  Quillen.SimplexParameters.triangle (triangleFace 0 1 2 (by decide) (by decide))
/-- The scalar triangle for the split second right-unit comparison. -/
def rightSecondParameter :=
  Quillen.SimplexParameters.triangle (triangleFace 2 3 7 (by decide) (by decide))
/-- The scalar triangle for the two unsplit right-unit comparisons. -/
def normalizedRightParameter :=
  Quillen.SimplexParameters.triangle (triangleFace 0 2 7 (by decide) (by decide))
/-- The scalar triangle for the split first left-unit comparison. -/
def leftFirstParameter :=
  Quillen.SimplexParameters.triangle (triangleFace 0 4 5 (by decide) (by decide))
/-- The scalar triangle for the split second left-unit comparison. -/
def leftSecondParameter :=
  Quillen.SimplexParameters.triangle (triangleFace 5 6 7 (by decide) (by decide))
/-- The scalar triangle for the two unsplit left-unit comparisons. -/
def normalizedLeftParameter :=
  Quillen.SimplexParameters.triangle (triangleFace 0 5 7 (by decide) (by decide))

/-- The two-edge parameter path for the first right-unit comparison. -/
def rightCompositionPath : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 8))
    (StdSimplex.single 2) := (edge 0 1).trans (edge 1 2)
/-- The two-edge parameter path for the second right-unit comparison. -/
def rightUnitPath : Path (StdSimplex.single 2 : StdSimplex ℝ (Fin 8))
    (StdSimplex.single 7) := (edge 2 3).trans (edge 3 7)
/-- The two-edge parameter path for the first left-unit comparison. -/
def leftCompositionPath : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 8))
    (StdSimplex.single 5) := (edge 0 4).trans (edge 4 5)
/-- The two-edge parameter path for the second left-unit comparison. -/
def leftUnitPath : Path (StdSimplex.single 5 : StdSimplex ℝ (Fin 8))
    (StdSimplex.single 7) := (edge 5 6).trans (edge 6 7)

/-- Original right-to-left unit-route comparison, with its unchanged association and speeds. -/
def routesParameter : (rightCompositionPath.trans rightUnitPath).Homotopy
    (leftCompositionPath.trans leftUnitPath) :=
  (rightFirstParameter.hcomp rightSecondParameter).symm.trans
    ((normalizedRightParameter.symm.trans normalizedLeftParameter).trans
      (leftFirstParameter.hcomp leftSecondParameter))

/-- Rotation and constant-half contraction are the actual native operations, before collapse. -/
def rotatedParameter :=
  (rotate routesParameter).trans
    ((Path.Homotopy.transRefl rightUnitPath).symm.hcomp
      (Path.Homotopy.refl leftUnitPath.symm))

/-- The square parameter uses the same three-side quotient as the original unit square. -/
def squareParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 8)) :=
  collapsed rotatedParameter

theorem rightFirstParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightFirstParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy
        (rightFirstGeometric f).hom (rightFirstNormalization f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (right_first_face f) n r t x

theorem rightSecondParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightSecondParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy
        (rightSecondGeometric f).hom (rightSecondNormalization f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (right_second_face f) n r t x

theorem normalizedRightParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (normalizedRightParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy (rightFirst f).hom (rightSecond f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (right_normalized_face f) n r t x

theorem leftFirstParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftFirstParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy
        (leftFirstGeometric f).hom (leftFirstNormalization f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (left_first_face f) n r t x

theorem leftSecondParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftSecondParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy
        (leftSecondGeometric f).hom (leftSecondNormalization f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (left_second_face f) n r t x

theorem normalizedLeftParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (normalizedLeftParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy (leftFirst f).hom (leftSecond f).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (left_normalized_face f) n r t x

/-- Every common-simplex parameter fixes the actual original chosen point, including level zero. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 8)) :
    prespectrumSimplexFamily (simplex f) n
      (z, (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).point n) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen X)).point n :=
  prespectrumSimplexFamily_point (simplex f) n z

/-- The entire common family retains a structure coordinate independent of its scalar parameters. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 8))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) (t : unitInterval) :
    prespectrumSimplexFamily (simplex f) (n + 1)
      (z, (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).structureMap n x t) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen X)).structureMap n
        (prespectrumSimplexFamily (simplex f) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex f) n z x t

private theorem whiskering_transport {C D E T : Type*}
    [Category C] [Category D] [Category E] [Category T]
    (L : C ⥤ D) (R : E ⥤ T) {F G : D ⥤ E} (e : F = G) :
    whiskerLeft L (whiskerRight (eqToHom e) R) =
      eqToHom (congrArg (fun H ↦ L ⋙ H ⋙ R) e) := by
  subst G
  ext A
  simp

private theorem composition_congr_first {V W : Model.{u}} {F G H : V ⟶ W}
    (η η' : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hη' : ∀ A, W.waldhausen.weq (η'.app A))
    (hθ : ∀ A, W.waldhausen.weq (θ.app A)) (e : η = η')
    (n : ℕ) (r t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (t, x)) =
      (prespectrumTransformationCompositionHomotopy η' θ hη' hθ).level n (r, (t, x)) := by
  subst η'
  rfl

private theorem right_source_eq :
    (sourceMap f).functor = (BinaryNormalizationSimplex.sourceMap (𝟙 X) f).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (Category.id_comp f).symm)

private theorem right_first_hom :
    (rightFirstGeometric f).hom = eqToHom (right_source_eq f) ≫
      (BinaryNormalizationSimplex.first (𝟙 X) f).hom := by
  unfold rightFirstGeometric BinaryNormalizationSimplex.first
  simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.trans_hom, eqToIso.hom,
    whiskerRight_comp, whiskerLeft_comp, whiskering_transport]

theorem rightFirst_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightFirstParameter (r, t), x) =
      (boundedFlatNormalizedCompTrackComparison (𝟙 X) f).level n (r, (t, x)) := by
  refine (rightFirstParameter_lift f n r t x).trans ?_
  trans (prespectrumTransformationCompositionHomotopy
    (eqToHom (right_source_eq f) ≫ (BinaryNormalizationSimplex.first (𝟙 X) f).hom)
    (BinaryNormalizationSimplex.second (𝟙 X) f).hom
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
      inferInstance)).level n (r, (t, x))
  · exact composition_congr_first _ _ _ _ _ _ (right_first_hom f) n r t x
  refine (transformationComposition_source_transport
    (F := sourceMap f) (F' := BinaryNormalizationSimplex.sourceMap (𝟙 X) f)
    (G := BinaryNormalizationSimplex.intermediateMap (𝟙 X) f)
    (H := BinaryNormalizationSimplex.targetMap (𝟙 X) f) (right_source_eq f)
    (BinaryNormalizationSimplex.first (𝟙 X) f).hom
    (BinaryNormalizationSimplex.second (𝟙 X) f).hom
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    n r t x).trans ?_
  exact (BinaryNormalizationSimplex.native_apply (𝟙 X) f n r t x).symm

private theorem left_source_eq :
    (sourceMap f).functor = (BinaryNormalizationSimplex.sourceMap f (𝟙 Y)).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (Category.comp_id f).symm)

private theorem left_first_hom :
    (leftFirstGeometric f).hom = eqToHom (left_source_eq f) ≫
      (BinaryNormalizationSimplex.first f (𝟙 Y)).hom := by
  unfold leftFirstGeometric BinaryNormalizationSimplex.first
  simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.trans_hom, eqToIso.hom,
    whiskerRight_comp, whiskerLeft_comp, whiskering_transport]

theorem leftFirst_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftFirstParameter (r, t), x) =
      (boundedFlatNormalizedCompTrackComparison f (𝟙 Y)).level n (r, (t, x)) := by
  refine (leftFirstParameter_lift f n r t x).trans ?_
  trans (prespectrumTransformationCompositionHomotopy
    (eqToHom (left_source_eq f) ≫ (BinaryNormalizationSimplex.first f (𝟙 Y)).hom)
    (BinaryNormalizationSimplex.second f (𝟙 Y)).hom
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
      inferInstance)).level n (r, (t, x))
  · exact composition_congr_first _ _ _ _ _ _ (left_first_hom f) n r t x
  refine (transformationComposition_source_transport
    (F := sourceMap f) (F' := BinaryNormalizationSimplex.sourceMap f (𝟙 Y))
    (G := BinaryNormalizationSimplex.intermediateMap f (𝟙 Y))
    (H := BinaryNormalizationSimplex.targetMap f (𝟙 Y)) (left_source_eq f)
    (BinaryNormalizationSimplex.first f (𝟙 Y)).hom
    (BinaryNormalizationSimplex.second f (𝟙 Y)).hom
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    n r t x).trans ?_
  exact (BinaryNormalizationSimplex.native_apply f (𝟙 Y) n r t x).symm

/-- The model map of normalized pullback along the identity scheme map. -/
def unitSourceMap (T : Scheme.{u}) : modelOf (boundedFlatPerfectWaldhausen T) ⟶
    modelOf (boundedFlatPerfectWaldhausen T) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact (𝟙 T))
    (boundedFlatNormalizedPullback_obj_zero _)

/-- The model map of the rebased identity functor. -/
def unitIntermediateMap (T : Scheme.{u}) : modelOf (boundedFlatPerfectWaldhausen T) ⟶
    modelOf (boundedFlatPerfectWaldhausen T) :=
  modelMap _ _ (Waldhausen.IsExact.id (boundedFlatPerfectWaldhausen T).cof
    (boundedFlatPerfectWaldhausen T).weq).rebase (Quillen.rebaseFunctor_obj_base _ _ _ _)

/-- The literal identity model map at the original scheme. -/
def unitTargetMap (T : Scheme.{u}) : modelOf (boundedFlatPerfectWaldhausen T) ⟶
    modelOf (boundedFlatPerfectWaldhausen T) :=
  modelMap _ _ (Waldhausen.IsExact.id _ _) rfl

/-- The geometric comparison from the identity source map to its rebased intermediate. -/
def unitFirst (T : Scheme.{u}) : (unitSourceMap T).functor ≅ (unitIntermediateMap T).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (unitGeometric T) AsSmall.up)

/-- The normalization comparison from the rebased intermediate to the identity map. -/
def unitSecond (T : Scheme.{u}) : (unitIntermediateMap T).functor ≅ (unitTargetMap T).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (unitNormalization T) AsSmall.up)

private theorem relative_transport {E F : LoopPrespectrum.{u}} {a b : E ⟶ F}
    {H H' K : Homotopy a b} (e : H = H')
    (p : H.RelHomotopy K = H'.RelHomotopy K) (J : H.RelHomotopy K) (n : ℕ) :
    ((p.mp J).level n).toContinuousMap = (J.level n).toContinuousMap := by
  subst H'
  rfl

private theorem ofLevels_projection {E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} {H K : Homotopy f g} (J : H.RelHomotopy K)
    (H' K' : Homotopy f' g') (hH : ∀ n, H'.level n = H.level n)
    (hK : ∀ n, K'.level n = K.level n) (n : ℕ) :
    ((J.ofLevels H' K' hH hK).level n).toContinuousMap =
      (J.level n).toContinuousMap := rfl

/-- The unit comparison is its original split-normalization triangle at every native level. -/
theorem unit_native_level (T : Scheme.{u}) (n : ℕ) :
    ((boundedFlatNormalizedIdTrackComparison T).level n).toContinuousMap =
      ((prespectrumTransformationCompositionHomotopy (unitFirst T).hom (unitSecond T).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen T)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen T)).waldhausen.weq_iso _
          inferInstance)).level n).toContinuousMap := by
  unfold boundedFlatNormalizedIdTrackComparison
  dsimp only
  rw [ofLevels_projection]
  apply relative_transport
  congr 1
  exact (boundedFlatNormalizedPullbackIdIso_hom T).symm

private theorem postcomp_level_eq {E F G : LoopPrespectrum.{u}}
    {a b a' b' : E ⟶ F} {H K : Homotopy a b} {H' K' : Homotopy a' b'}
    (J : H.RelHomotopy K) (J' : H'.RelHomotopy K') (c : F ⟶ G) (n : ℕ)
    (h : (J.level n).toContinuousMap = (J'.level n).toContinuousMap)
    (r t : unitInterval) (x : E.space n) :
    (J.postcomp c).level n (r, (t, x)) = (J'.postcomp c).level n (r, (t, x)) :=
  congrArg (c.map n) (Homotopy.RelHomotopy.level_eq_apply J J' n h r t x)

private theorem lift_cast {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k)
    {a b : StdSimplex ℝ (Fin (k + 1))} {p q : Path a b} {A : p.Homotopy q}
    {f g f' g' : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    {J : H.RelHomotopy K} (ef : f = f') (eg : g = g')
    (h : HomotopyLift S A J) : HomotopyLift S A (J.cast ef eg) := by
  intro n r t x
  exact h n r t x

theorem rightSecond_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightSecondParameter (r, t), x) =
      (Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap f)
        (boundedFlatNormalizedIdTrackComparison X)).level n (r, (t, x)) := by
  refine (rightSecondParameter_lift f n r t x).trans ?_
  trans (Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap f)
    (prespectrumTransformationCompositionHomotopy
      (unitFirst X).hom (unitSecond X).hom
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
        inferInstance))).level n (r, (t, x))
  · exact transformationComposition_precomp
      (F := unitSourceMap X) (G := unitIntermediateMap X) (H := unitTargetMap X)
      (unitFirst X).hom (unitSecond X).hom
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
      (sourceMap f) n r t x
  · exact (Homotopy.RelHomotopy.level_eq_precomp_apply _ _
      (boundedFlatPerfectPrespectrumMap f) n (unit_native_level X n) r t x).symm

theorem leftSecond_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftSecondParameter (r, t), x) =
      ((boundedFlatNormalizedIdTrackComparison Y).postcomp
        (boundedFlatPerfectPrespectrumMap f)).level n (r, (t, x)) := by
  refine (leftSecondParameter_lift f n r t x).trans ?_
  trans ((prespectrumTransformationCompositionHomotopy
      (unitFirst Y).hom (unitSecond Y).hom
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen Y)).waldhausen.weq_iso _ inferInstance)
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen Y)).waldhausen.weq_iso _
        inferInstance)).postcomp (boundedFlatPerfectPrespectrumMap f)).level n (r, (t, x))
  · exact transformationComposition_postcomp
      (F := unitSourceMap Y) (G := unitIntermediateMap Y) (H := unitTargetMap Y)
      (unitFirst Y).hom (unitSecond Y).hom
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen Y)).waldhausen.weq_iso _ inferInstance)
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen Y)).waldhausen.weq_iso _ inferInstance)
      (sourceMap f) n r t x
  · exact (postcomp_level_eq _ _ (boundedFlatPerfectPrespectrumMap f) n
      (unit_native_level Y n) r t x).symm

/-- The normalized middle uses the precise original two-triangle pasting. -/
theorem normalized_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n
      ((normalizedRightParameter.symm.trans normalizedLeftParameter) (r, t), x) =
      (boundedFlatNormalizedUnitRoutesComparison f).level n (r, (t, x)) := by
  unfold boundedFlatNormalizedUnitRoutesComparison
  dsimp only
  rw [Homotopy.RelHomotopy.ofLevels_apply,
    originalPrespectrumPastingHomotopy_whole_level, Path.Homotopy.trans_apply]
  split
  · exact normalizedRightParameter_lift f n _ t x
  · exact normalizedLeftParameter_lift f n _ t x

private theorem relative_cast_apply {E F : LoopPrespectrum.{u}}
    {a b a' b' : E ⟶ F} {H K : Homotopy a b} (J : H.RelHomotopy K)
    (ea : a = a') (eb : b = b') (n : ℕ) (r t : unitInterval) (x : E.space n) :
    (J.cast ea eb).level n (r, (t, x)) = J.level n (r, (t, x)) := rfl

private theorem relative_hcomp_apply {E F : LoopPrespectrum.{u}} {a b c : E ⟶ F}
    {H H' : Homotopy a b} {K K' : Homotopy b c}
    (J : H.RelHomotopy H') (L : K.RelHomotopy K')
    (n : ℕ) (r t : unitInterval) (x : E.space n) :
    (J.hcomp L).level n (r, (t, x)) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        J.level n (r, (⟨2 * t,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x))
      else L.level n (r, (⟨2 * t - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, x)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

private theorem hcomp_evaluate {A B : Type*} [TopologicalSpace A] {a b c : A}
    {p p' : Path a b} {q q' : Path b c} (J : p.Homotopy p') (K : q.Homotopy q')
    (v : A → B) (F G : unitInterval → unitInterval → B)
    (hJ : ∀ r t, v (J (r, t)) = F r t) (hK : ∀ r t, v (K (r, t)) = G r t)
    (r t : unitInterval) :
    v ((J.hcomp K) (r, t)) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        F r ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      else G r ⟨2 * t - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := by
  rw [Path.Homotopy.hcomp_apply]
  split
  · exact hJ _ _
  · exact hK _ _

private theorem right_route_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (boundedFlatNormalizedRightUnitRouteComparison f).level n (r, (t, x)) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        (boundedFlatNormalizedCompTrackComparison (𝟙 X) f).level n
          (r, (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x))
      else (Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap f)
        (boundedFlatNormalizedIdTrackComparison X)).level n
          (r, (⟨2 * t - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, x)) :=
  relative_hcomp_apply
    ((boundedFlatNormalizedCompTrackComparison (𝟙 X) f).cast
      (congrArg boundedFlatPerfectPrespectrumMap (Category.id_comp f)) rfl)
    ((Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap f)
      (boundedFlatNormalizedIdTrackComparison X)).cast rfl (Category.comp_id _)) n r t x

private theorem right_route_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n
      ((rightFirstParameter.hcomp rightSecondParameter) (r, t), x) =
      (boundedFlatNormalizedRightUnitRouteComparison f).level n (r, (t, x)) := by
  refine Eq.trans ?_ (right_route_value f n r t x).symm
  exact hcomp_evaluate rightFirstParameter rightSecondParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ (boundedFlatNormalizedCompTrackComparison (𝟙 X) f).level n (r, (t, x)))
    (fun r t ↦ (Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap f)
      (boundedFlatNormalizedIdTrackComparison X)).level n (r, (t, x)))
    (fun r t ↦ rightFirst_native f n r t x) (fun r t ↦ rightSecond_native f n r t x) r t

private theorem left_route_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (boundedFlatNormalizedLeftUnitRouteComparison f).level n (r, (t, x)) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        (boundedFlatNormalizedCompTrackComparison f (𝟙 Y)).level n
          (r, (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x))
      else ((boundedFlatNormalizedIdTrackComparison Y).postcomp
        (boundedFlatPerfectPrespectrumMap f)).level n
          (r, (⟨2 * t - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, x)) :=
  relative_hcomp_apply
    ((boundedFlatNormalizedCompTrackComparison f (𝟙 Y)).cast
      (congrArg boundedFlatPerfectPrespectrumMap (Category.comp_id f)) rfl)
    (((boundedFlatNormalizedIdTrackComparison Y).postcomp
      (boundedFlatPerfectPrespectrumMap f)).cast rfl (Category.id_comp _)) n r t x

private theorem left_route_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n
      ((leftFirstParameter.hcomp leftSecondParameter) (r, t), x) =
      (boundedFlatNormalizedLeftUnitRouteComparison f).level n (r, (t, x)) := by
  refine Eq.trans ?_ (left_route_value f n r t x).symm
  exact hcomp_evaluate leftFirstParameter leftSecondParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ (boundedFlatNormalizedCompTrackComparison f (𝟙 Y)).level n (r, (t, x)))
    (fun r t ↦ ((boundedFlatNormalizedIdTrackComparison Y).postcomp
      (boundedFlatPerfectPrespectrumMap f)).level n (r, (t, x)))
    (fun r t ↦ leftFirst_native f n r t x) (fun r t ↦ leftSecond_native f n r t x) r t

/-- The scalar unit-route comparison evaluates to the entire original comparison. -/
theorem routes_native : HomotopyLift (simplex f) routesParameter
    (boundedFlatOriginalUnitRoutesComparison f) :=
  HomotopyLift.trans (simplex f) (HomotopyLift.symm (simplex f) (right_route_native f))
    (HomotopyLift.trans (simplex f) (normalized_native f) (left_route_native f))

private theorem squareBoundary_apply {E F : LoopPrespectrum.{u}}
    {f₀ g₀ f₁ g₁ f₀' g₀' f₁' g₁' : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}
    (S : H₀.Square H₁ L M)
    (H₀' : Homotopy f₀' g₀') (H₁' : Homotopy f₁' g₁')
    (L' : Homotopy f₀' f₁') (M' : Homotopy g₀' g₁')
    (h₀ : ∀ n, H₀'.level n = H₀.level n) (h₁ : ∀ n, H₁'.level n = H₁.level n)
    (hL : ∀ n, L'.level n = L.level n) (hM : ∀ n, M'.level n = M.level n)
    (n : ℕ) (r t : unitInterval) (x : E.space n) :
    (S.ofBoundaryLevels H₀' H₁' L' M' h₀ h₁ hL hM).level n (r, (t, x)) =
      S.level n (r, (t, x)) := rfl

private theorem target_evaluate {A B : Type*} [TopologicalSpace A] {a b : A}
    {p q : Path a b} (J : p.Homotopy q) (v : A → B)
    (F : unitInterval → unitInterval → B)
    (hJ : ∀ r t, v (J (r, t)) = F r t) (t : unitInterval) :
    v (q t) = F 1 t :=
  (congrArg v (J.apply_one t)).symm.trans (hJ 1 t)

private theorem right_composition_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightCompositionPath t, x) =
      (boundedFlatPerfectPrespectrumCompHomotopy (𝟙 X) f).level n (t, x) := by
  exact (target_evaluate rightFirstParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ (boundedFlatNormalizedCompTrackComparison (𝟙 X) f).level n (r, (t, x)))
    (fun r t ↦ rightFirst_native f n r t x) t).trans
      (((boundedFlatNormalizedCompTrackComparison (𝟙 X) f).level n).apply_one (t, x))

private theorem left_composition_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftCompositionPath t, x) =
      (boundedFlatPerfectPrespectrumCompHomotopy f (𝟙 Y)).level n (t, x) := by
  exact (target_evaluate leftFirstParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ (boundedFlatNormalizedCompTrackComparison f (𝟙 Y)).level n (r, (t, x)))
    (fun r t ↦ leftFirst_native f n r t x) t).trans
      (((boundedFlatNormalizedCompTrackComparison f (𝟙 Y)).level n).apply_one (t, x))

private theorem right_unit_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightUnitPath t, x) =
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap f)
        (boundedFlatPerfectPrespectrumIdHomotopy X)).level n (t, x) := by
  exact (target_evaluate rightSecondParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ (Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap f)
        (boundedFlatNormalizedIdTrackComparison X)).level n (r, (t, x)))
    (fun r t ↦ rightSecond_native f n r t x) t).trans
      (((Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap f)
        (boundedFlatNormalizedIdTrackComparison X)).level n).apply_one (t, x))

private theorem left_unit_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftUnitPath t, x) =
      ((boundedFlatPerfectPrespectrumIdHomotopy Y).postcomp
        (boundedFlatPerfectPrespectrumMap f)).level n (t, x) := by
  exact (target_evaluate leftSecondParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ ((boundedFlatNormalizedIdTrackComparison Y).postcomp
        (boundedFlatPerfectPrespectrumMap f)).level n (r, (t, x)))
    (fun r t ↦ leftSecond_native f n r t x) t).trans
      ((((boundedFlatNormalizedIdTrackComparison Y).postcomp
        (boundedFlatPerfectPrespectrumMap f)).level n).apply_one (t, x))

private theorem rotation_native : HomotopyLift (simplex f) (rotate routesParameter)
    (Homotopy.RelHomotopy.rotate (boundedFlatOriginalUnitRoutesComparison f)) :=
  HomotopyLift.rotate (simplex f) (right_composition_native f) (right_unit_native f)
    (left_composition_native f) (left_unit_native f) (routes_native f)

private theorem contraction_native :
  let L := (Homotopy.precomp (boundedFlatPerfectPrespectrumMap f)
    (boundedFlatPerfectPrespectrumIdHomotopy X)).cast rfl (Category.comp_id _)
  let M := ((boundedFlatPerfectPrespectrumIdHomotopy Y).postcomp
    (boundedFlatPerfectPrespectrumMap f)).cast rfl (Category.id_comp _)
  HomotopyLift (simplex f)
    ((Path.Homotopy.transRefl rightUnitPath).symm.hcomp
      (Path.Homotopy.refl leftUnitPath.symm))
    ((Homotopy.RelHomotopy.transRefl L).symm.hcomp (Homotopy.RelHomotopy.refl M.symm)) :=
  HomotopyLift.hcomp (simplex f)
    (HomotopyLift.symm (simplex f) (PathLift.transRefl (simplex f) (right_unit_native f)))
    (PathLift.refl (simplex f) (PathLift.symm (simplex f) (left_unit_native f)))

/-- Every value of the original geometric unit square lies in this actual common simplex. -/
theorem square_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (squareParameter (r, t), x) =
      (boundedFlatPerfectPrespectrumUnitSquare f).level n (r, (t, x)) := by
  unfold boundedFlatPerfectPrespectrumUnitSquare
  dsimp only
  rw [squareBoundary_apply]
  exact HomotopyLift.toSquare (simplex f)
    (HomotopyLift.trans (simplex f) (rotation_native f) (contraction_native f)) n r t x

/-- The original rotate/constant-contraction surface is retained before the actual quotient. -/
theorem square_collapse (z : unitInterval × unitInterval) :
    squareParameter (Quillen.ThreeSideSquare.collapse z) = rotatedParameter z :=
  collapsed_collapse rotatedParameter z

/-- Exact original lower scalar path. -/
theorem square_zero (t : unitInterval) :
    squareParameter (0, t) = (rightCompositionPath.symm.trans leftCompositionPath) t := by
  have h := square_collapse (0, t)
  rw [Quillen.ThreeSideSquare.collapse_zero] at h
  exact h.trans (rotatedParameter.apply_zero t)

/-- Exact scalar left boundary, with the original first-quarter time. -/
theorem square_left (r : unitInterval) :
    squareParameter (r, 0) =
      ((rightUnitPath.trans (Path.refl (StdSimplex.single 7))).trans leftUnitPath.symm)
        (Quillen.ThreeSideSquare.leftTime r) := by
  have h := square_collapse (1, Quillen.ThreeSideSquare.leftTime r)
  rw [Quillen.ThreeSideSquare.collapse_leftTime] at h
  exact h.trans (rotatedParameter.apply_one _)

/-- Exact scalar top boundary, retaining the original constant half before quotienting. -/
theorem square_top (t : unitInterval) :
    squareParameter (1, t) =
      ((rightUnitPath.trans (Path.refl (StdSimplex.single 7))).trans leftUnitPath.symm)
        (Quillen.ThreeSideSquare.topTime t) := by
  have h := square_collapse (1, Quillen.ThreeSideSquare.topTime t)
  rw [Quillen.ThreeSideSquare.collapse_topTime] at h
  exact h.trans (rotatedParameter.apply_one _)

/-- Exact scalar right boundary, with the original reversed final-half time. -/
theorem square_right (r : unitInterval) :
    squareParameter (r, 1) =
      ((rightUnitPath.trans (Path.refl (StdSimplex.single 7))).trans leftUnitPath.symm)
        (Quillen.ThreeSideSquare.rightTime r) := by
  have h := square_collapse (1, Quillen.ThreeSideSquare.rightTime r)
  rw [Quillen.ThreeSideSquare.collapse_rightTime] at h
  exact h.trans (rotatedParameter.apply_one _)

end Quillen.PerfectComplexes.OriginalUnitSquareSimplex
