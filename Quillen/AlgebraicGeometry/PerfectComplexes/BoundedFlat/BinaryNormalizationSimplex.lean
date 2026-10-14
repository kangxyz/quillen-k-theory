/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleLift
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CompositionTrack

/-! The genuine normalization intermediate and whole old binary comparison triangle. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BinaryNormalizationSimplex
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual intermediate normalization of the unnormalized composite functor. -/
def intermediate : BoundedFlatPerfect Z ⥤ BoundedFlatPerfect X :=
  Quillen.rebaseFunctor (boundedFlatPerfectPullback g ⋙ boundedFlatPerfectPullback f)
    (boundedFlatPerfectWaldhausen Z).zero (boundedFlatPerfectWaldhausen X).zero
    ((((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f)).zero
      (boundedFlatPerfectWaldhausen Z).isZero).iso (boundedFlatPerfectWaldhausen X).isZero)

/-- The old first transformation is the conjugated geometric isomorphism. -/
def geometricIso : boundedFlatNormalizedPullback (f ≫ g) ≅ intermediate f g :=
  (boundedFlatPullbackNormalizationIso (f ≫ g)).symm ≪≫
    boundedFlatPerfectPullbackCompIso f g ≪≫
    Quillen.rebaseFunctorIso _ _ _ _

/-- This is exactly the first component used by the old binary comparison. -/
theorem geometricIso_hom : (geometricIso f g).hom =
    Waldhausen.normalizedWeakTransformation (boundedFlatPerfectPullback_exact (f ≫ g))
      ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
      (boundedFlatPerfectPullbackCompIso f g).hom := rfl

/-- The old second component is the unchanged binary normalization isomorphism. -/
def normalizationIso : intermediate f g ≅
    boundedFlatNormalizedPullback g ⋙ boundedFlatNormalizedPullback f :=
  exactNormalizationCompIso (boundedFlatPerfectPullback_exact g)
    (boundedFlatPerfectPullback_exact f)

/-- The actual split composite is the native total normalized comparison. -/
theorem composite_hom : (geometricIso f g).hom ≫ (normalizationIso f g).hom =
    (boundedFlatNormalizedPullbackCompIso f g).hom :=
  (boundedFlatNormalizedPullbackCompIso_hom f g).symm

def sourceMap : modelOf (boundedFlatPerfectWaldhausen Z) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact (f ≫ g))
    (boundedFlatNormalizedPullback_obj_zero _)

def intermediateMap : modelOf (boundedFlatPerfectWaldhausen Z) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ ((boundedFlatPerfectPullback_exact g).comp
    (boundedFlatPerfectPullback_exact f)).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _)

def targetMap : modelOf (boundedFlatPerfectWaldhausen Z) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ ((boundedFlatNormalizedPullback_exact g).comp
    (boundedFlatNormalizedPullback_exact f))
    (by simp only [comp_obj, boundedFlatNormalizedPullback_obj_zero])

def first : (sourceMap f g).functor ≅ (intermediateMap f g).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (geometricIso f g) AsSmall.up)

def second : (intermediateMap f g).functor ≅ (targetMap f g).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (normalizationIso f g) AsSmall.up)

def total : (sourceMap f g).functor ≅ (targetMap f g).functor :=
  isoWhiskerLeft AsSmall.down
    (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso f g) AsSmall.up)

theorem small_composite_hom : (first f g).hom ≫ (second f g).hom = (total f g).hom := by
  have hh := congrArg
    (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up)) (composite_hom f g)
  simpa only [first, second, total, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_comp, whiskerRight_comp] using hh

/-- All three actual binary vertices use the original total functor as common reference. -/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen Z))
    (modelOf (boundedFlatPerfectWaldhausen X)) 2 :=
  ModelSimplex.ofIsos (sourceMap f g) ![sourceMap f g, intermediateMap f g, targetMap f g]
    (Fin.cases (Iso.refl _) (Fin.cases (first f g)
      (Fin.cases (total f g) (fun i ↦ Fin.elim0 i))))

/-- The complete old triangle, including both original normalization components. -/
theorem simplex_eq_triangle : simplex f g =
    ModelSimplex.triangle (first f g).hom (second f g).hom
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance) := by
  have he : simplex f g = (simplex f g).face (𝟙 ⦋2⦌) :=
    ModelSimplex.ext_diagram (by rfl)
  rw [he]
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact small_composite_hom f g

/-- Every point of the old composition triangle has an explicit common-simplex lift. -/
theorem whole_triangle (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    prespectrumSimplexFamily (simplex f g) n
      (Quillen.TheoremB.compositionTriangleHomotopy (r, s), x) =
      (prespectrumTransformationCompositionHomotopy (first f g).hom (second f g).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (s, x)) := by
  rw [simplex_eq_triangle]
  exact prespectrumSimplexFamily_triangle _ _ _ _ n r s x

end Quillen.PerfectComplexes.BinaryNormalizationSimplex
