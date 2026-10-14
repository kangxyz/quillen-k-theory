/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BinaryNormalizationSimplex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackSimplex

/-! One common geometric simplex containing all six old triangles of a split triple comparison. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.SplitTripleSimplex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The first old binary intermediate on the left route. -/
abbrev leftFirstMap := BinaryNormalizationSimplex.intermediateMap f (g ≫ h)

/-- The second old binary intermediate on the left route, postwhiskered by the actual map. -/
def leftSecondMap : modelOf (boundedFlatPerfectWaldhausen T) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ (((boundedFlatPerfectPullback_exact h).comp
    (boundedFlatPerfectPullback_exact g)).rebase.comp (boundedFlatNormalizedPullback_exact f))
    (by simp only [comp_obj, Quillen.rebaseFunctor_obj_base,
      boundedFlatNormalizedPullback_obj_zero])

/-- The first old binary intermediate on the right route. -/
abbrev rightFirstMap := BinaryNormalizationSimplex.intermediateMap (f ≫ g) h

/-- The second old binary intermediate on the right route, prewhiskered by the actual map. -/
def rightSecondMap : modelOf (boundedFlatPerfectWaldhausen T) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ ((boundedFlatNormalizedPullback_exact h).comp
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f)).rebase)
    (by simp only [comp_obj, boundedFlatNormalizedPullback_obj_zero,
      Quillen.rebaseFunctor_obj_base])

abbrev leftFirstGeometric := BinaryNormalizationSimplex.first f (g ≫ h)
abbrev leftFirstNormalization := BinaryNormalizationSimplex.second f (g ≫ h)

def leftSecondGeometric : (NormalizedTripleSimplex.leftMap f g h).functor ≅
    (leftSecondMap f g h).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerRight (BinaryNormalizationSimplex.geometricIso g h)
      (boundedFlatNormalizedPullback f)) AsSmall.up)

def leftSecondNormalization : (leftSecondMap f g h).functor ≅
    (NormalizedTripleSimplex.targetMap f g h).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerRight (BinaryNormalizationSimplex.normalizationIso g h)
      (boundedFlatNormalizedPullback f)) AsSmall.up)

def rightFirstGeometric : (NormalizedTripleSimplex.sourceMap f g h).functor ≅
    (rightFirstMap f g h).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm) ≪≫
      BinaryNormalizationSimplex.geometricIso (f ≫ g) h) AsSmall.up)

abbrev rightFirstNormalization := BinaryNormalizationSimplex.second (f ≫ g) h

def rightSecondGeometric : (NormalizedTripleSimplex.rightMap f g h).functor ≅
    (rightSecondMap f g h).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerLeft (boundedFlatNormalizedPullback h)
      (BinaryNormalizationSimplex.geometricIso f g)) AsSmall.up)

def rightSecondNormalization : (rightSecondMap f g h).functor ≅
    (NormalizedTripleSimplex.targetMap f g h).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerLeft (boundedFlatNormalizedPullback h)
      (BinaryNormalizationSimplex.normalizationIso f g)) AsSmall.up)

theorem left_first_composite :
    (leftFirstGeometric f g h).hom ≫ (leftFirstNormalization f g h).hom =
      (NormalizedTripleSimplex.leftFirst f g h).hom :=
  BinaryNormalizationSimplex.small_composite_hom f (g ≫ h)

theorem left_second_composite :
    (leftSecondGeometric f g h).hom ≫ (leftSecondNormalization f g h).hom =
      (NormalizedTripleSimplex.leftSecond f g h).hom := by
  apply NatTrans.ext
  funext A
  simp only [leftSecondGeometric, leftSecondNormalization, NormalizedTripleSimplex.leftSecond,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.trans_hom, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app,
    BinaryNormalizationSimplex.composite_hom]

theorem right_first_composite :
    (rightFirstGeometric f g h).hom ≫ (rightFirstNormalization f g h).hom =
      (NormalizedTripleSimplex.rightFirst f g h).hom := by
  have hh := congrArg (fun η ↦ whiskerLeft AsSmall.down
    (whiskerRight (eqToHom
      (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm) ≫ η) AsSmall.up))
    (BinaryNormalizationSimplex.composite_hom (f ≫ g) h)
  simpa only [rightFirstGeometric, rightFirstNormalization, BinaryNormalizationSimplex.second,
    NormalizedTripleSimplex.rightFirst, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, eqToIso.hom, whiskerLeft_comp, whiskerRight_comp, Category.assoc] using hh

theorem right_second_composite :
    (rightSecondGeometric f g h).hom ≫ (rightSecondNormalization f g h).hom =
      (NormalizedTripleSimplex.rightSecond f g h).hom := by
  have hh := congrArg (fun η ↦ whiskerLeft AsSmall.down
    (whiskerRight (whiskerLeft (boundedFlatNormalizedPullback h) η) AsSmall.up))
    (BinaryNormalizationSimplex.composite_hom f g)
  simpa only [rightSecondGeometric, rightSecondNormalization, NormalizedTripleSimplex.rightSecond,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_comp, whiskerRight_comp] using hh

/-- The eight actual normalized and intermediate geometric functors. -/
def vertices : Fin 8 → (modelOf (boundedFlatPerfectWaldhausen T) ⟶
    modelOf (boundedFlatPerfectWaldhausen X)) :=
  ![NormalizedTripleSimplex.sourceMap f g h, leftFirstMap f g h,
    NormalizedTripleSimplex.leftMap f g h, leftSecondMap f g h,
    rightFirstMap f g h, NormalizedTripleSimplex.rightMap f g h, rightSecondMap f g h,
    NormalizedTripleSimplex.targetMap f g h]

/-- Canonical comparisons from the same native total pullback to all eight vertices. -/
def references : ∀ i, (NormalizedTripleSimplex.sourceMap f g h).functor ≅
    (vertices f g h i).functor :=
  Fin.cases (Iso.refl _) (Fin.cases (leftFirstGeometric f g h)
    (Fin.cases (NormalizedTripleSimplex.leftFirst f g h)
      (Fin.cases (NormalizedTripleSimplex.leftFirst f g h ≪≫ leftSecondGeometric f g h)
        (Fin.cases (rightFirstGeometric f g h)
          (Fin.cases (NormalizedTripleSimplex.rightFirst f g h)
            (Fin.cases (NormalizedTripleSimplex.rightFirst f g h ≪≫ rightSecondGeometric f g h)
              (Fin.cases (NormalizedTripleSimplex.leftFirst f g h ≪≫
                NormalizedTripleSimplex.leftSecond f g h) (fun i ↦ Fin.elim0 i))))))))

/-- The common simplex contains every old binary and normalized triangle of the triple. -/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen T))
    (modelOf (boundedFlatPerfectWaldhausen X)) 7 :=
  ModelSimplex.ofIsos (NormalizedTripleSimplex.sourceMap f g h)
    (vertices f g h) (references f g h)

/-- An explicitly chosen ordered triple of vertices. -/
def triangleFace (i j k : Fin 8) (hij : i ≤ j) (hjk : j ≤ k) : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![i, j, k], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [le_trans hij hjk]⟩

theorem left_first_face :
    (simplex f g h).face (triangleFace 0 1 2 (by decide) (by decide)) =
      ModelSimplex.triangle (leftFirstGeometric f g h).hom (leftFirstNormalization f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact left_first_composite f g h

theorem left_second_face :
    (simplex f g h).face (triangleFace 2 3 7 (by decide) (by decide)) =
      ModelSimplex.triangle (leftSecondGeometric f g h).hom (leftSecondNormalization f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · change (_ ≫ (leftSecondGeometric f g h).hom) ≫ (leftSecondNormalization f g h).hom = _
    rw [Category.assoc, left_second_composite]
    rfl

theorem normalized_left_face :
    (simplex f g h).face (triangleFace 0 2 7 (by decide) (by decide)) =
      ModelSimplex.triangle (NormalizedTripleSimplex.leftFirst f g h).hom
        (NormalizedTripleSimplex.leftSecond f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · rfl

theorem right_first_face :
    (simplex f g h).face (triangleFace 0 4 5 (by decide) (by decide)) =
      ModelSimplex.triangle (rightFirstGeometric f g h).hom (rightFirstNormalization f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact right_first_composite f g h

theorem right_second_face :
    (simplex f g h).face (triangleFace 5 6 7 (by decide) (by decide)) =
      ModelSimplex.triangle (rightSecondGeometric f g h).hom (rightSecondNormalization f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · change (_ ≫ (rightSecondGeometric f g h).hom) ≫ (rightSecondNormalization f g h).hom = _
    rw [Category.assoc, right_second_composite]
    exact (NormalizedTripleSimplex.two_routes f g h).symm

theorem normalized_right_face :
    (simplex f g h).face (triangleFace 0 5 7 (by decide) (by decide)) =
      ModelSimplex.triangle (NormalizedTripleSimplex.rightFirst f g h).hom
        (NormalizedTripleSimplex.rightSecond f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact (NormalizedTripleSimplex.two_routes f g h).symm

end Quillen.PerfectComplexes.SplitTripleSimplex
