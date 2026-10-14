/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexIsomorphism
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackCoherence

/-!
# Normalized Pullback Simplex

One actual geometric common simplex for the original normalized pullback-associativity diamond.
Both native composition triangles are faces of the same tetrahedron. The entire Bass rectangle
and its original split normalization pieces still need a joint parameter lift.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.NormalizedTripleSimplex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The exact original source of the native normalized triple comparison. -/
def sourceMap : modelOf (boundedFlatPerfectWaldhausen T) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact (f ≫ g ≫ h))
    (boundedFlatNormalizedPullback_obj_zero _)

/-- Its actual first intermediate normalized pullback functor. -/
def leftMap : modelOf (boundedFlatPerfectWaldhausen T) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ ((boundedFlatNormalizedPullback_exact (g ≫ h)).comp
    (boundedFlatNormalizedPullback_exact f))
    (by simp only [comp_obj, boundedFlatNormalizedPullback_obj_zero])

/-- Its actual second intermediate normalized pullback functor. -/
def rightMap : modelOf (boundedFlatPerfectWaldhausen T) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ ((boundedFlatNormalizedPullback_exact h).comp
    (boundedFlatNormalizedPullback_exact (f ≫ g)))
    (by simp only [comp_obj, boundedFlatNormalizedPullback_obj_zero])

/-- The unchanged fully decomposed target of the native triple comparison. -/
def targetMap : modelOf (boundedFlatPerfectWaldhausen T) ⟶
    modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ ((boundedFlatNormalizedPullback_exact h).comp
    ((boundedFlatNormalizedPullback_exact g).comp (boundedFlatNormalizedPullback_exact f)))
    (by simp only [comp_obj, boundedFlatNormalizedPullback_obj_zero])

/-- The original first left edge, transported only through the accepted small-model equivalence. -/
def leftFirst : (sourceMap f g h).functor ≅ (leftMap f g h).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso f (g ≫ h))
    AsSmall.up)

/-- The original second left edge, including its genuine functor associator. -/
def leftSecond : (leftMap f g h).functor ≅ (targetMap f g h).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso g h) (boundedFlatNormalizedPullback f)
      ≪≫ Functor.associator (boundedFlatNormalizedPullback h) (boundedFlatNormalizedPullback g)
        (boundedFlatNormalizedPullback f)) AsSmall.up)

/-- The original first right edge retains the scheme associativity transport. -/
def rightFirst : (sourceMap f g h).functor ≅ (rightMap f g h).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (f ≫ g) h) AsSmall.up)

/-- The original second right edge keeps its actual prewhiskered comparison. -/
def rightSecond : (rightMap f g h).functor ≅ (targetMap f g h).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerLeft (boundedFlatNormalizedPullback h) (boundedFlatNormalizedPullbackCompIso f g))
    AsSmall.up)

/-- Geometric associativity identifies the two original common-diagram routes. -/
theorem two_routes :
    (leftFirst f g h).hom ≫ (leftSecond f g h).hom =
      (rightFirst f g h).hom ≫ (rightSecond f g h).hom := by
  have he := boundedFlatNormalizedPullbackCompIso_two_routes f g h
  have hh := congrArg
    (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up)) he
  simpa only [leftFirst, leftSecond, rightFirst, rightSecond, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, Iso.trans_hom, eqToIso.hom, whiskerLeft_comp, whiskerRight_comp,
    Category.assoc] using hh

/-- A genuine common tetrahedron for the original native normalized triple-pullback diamond. -/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen T))
    (modelOf (boundedFlatPerfectWaldhausen X)) 3 :=
  ModelSimplex.diamond (F₀ := sourceMap f g h) (F₁ := leftMap f g h)
    (F₂ := rightMap f g h) (F₃ := targetMap f g h)
    (leftFirst f g h) (leftSecond f g h) (rightFirst f g h)

/-- Every point of the first native composition triangle is a face of this common simplex. -/
theorem first_face :
    (simplex f g h).face (SimplexCategory.δ 2) =
      ModelSimplex.triangle (leftFirst f g h).hom (leftSecond f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance) :=
  ModelSimplex.diamond_first _ _ _

/-- The second native triangle uses the proved geometric equation, with no higher premise. -/
theorem second_face :
    (simplex f g h).face (SimplexCategory.δ 1) =
      ModelSimplex.triangle (rightFirst f g h).hom (rightSecond f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance) :=
  ModelSimplex.diamond_second _ _ _ _ (two_routes f g h)

/-- The first complete realized native triangle sits in the common geometric tetrahedron. -/
theorem first_face_realization (r : ℕ)
    (x : stageSpace r (modelOf (boundedFlatPerfectWaldhausen T)))
    (z : |(Δ[2] : SSet.{u + 1})|) :
    stageSimplexRealization r (simplex f g h)
      (x, SSet.toTop.map (SSet.stdSimplex.δ 2) z) =
      stageTriangleRealization (leftFirst f g h).hom (leftSecond f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
            inferInstance) r (x, z) := by
  exact (stageSimplexRealization_face r (simplex f g h) (SimplexCategory.δ 2) x z).trans
    (by rw [first_face, stageSimplexRealization_triangle])

/-- The second complete realized native triangle retains its original whole two-parameter image. -/
theorem second_face_realization (r : ℕ)
    (x : stageSpace r (modelOf (boundedFlatPerfectWaldhausen T)))
    (z : |(Δ[2] : SSet.{u + 1})|) :
    stageSimplexRealization r (simplex f g h)
      (x, SSet.toTop.map (SSet.stdSimplex.δ 1) z) =
      stageTriangleRealization (rightFirst f g h).hom (rightSecond f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
            inferInstance) r (x, z) := by
  exact (stageSimplexRealization_face r (simplex f g h) (SimplexCategory.δ 1) x z).trans
    (by rw [second_face, stageSimplexRealization_triangle])

end Quillen.PerfectComplexes.NormalizedTripleSimplex
