/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveWhiskering
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveSharedStart

/-!
# The two original whiskered Bass cubes in the same actual reference nerve

Both remaining fixed cubes retain all 140 original nodes and the unchanged scalarCube.{u}.
Their anchors are the displayed actual geometric total equalities followed by original
normalized pullback composition isomorphisms. Every native finite family is precisely the
original pre- or postcomposed interiorCube, including level zero. This does not identify
additional shared faces or distinct canonically isomorphic nodes.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The exact model morphism inducing the original native coefficient prespectrum map. -/
def coefficientModel {a b : Under R} (u : a ⟶ b) :
    modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      modelOf (boundedFlatPerfectWaldhausen (space (op P, b))) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact (coefficientMap P u))
    (boundedFlatNormalizedPullback_obj_zero _)

/-- This model morphism induces exactly the original coefficient map. -/
theorem coefficientModel_prespectrum {a b : Under R} (u : a ⟶ b) :
    prespectrumMap (coefficientModel P u) = boundedFlatPerfectPrespectrumMap (coefficientMap P u) :=
  rfl

variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The original total map for the source-whiskered cube, with its actual association. -/
theorem precomp_total :
    coefficientMap P ((laurentUnderFunctor R).map ((u ≫ v) ≫ w)) ≫ laurentProjection P a =
      (laurentProjection P d ≫ coefficientMap P w ≫ coefficientMap P v) ≫ coefficientMap P u := by
  rw [BassH0Merge.total, coefficientMap_comp]
  simp only [Category.assoc]

/-- The original total map for the Laurent-target-whiskered cube. -/
theorem postcomp_total :
    coefficientMap P ((laurentUnderFunctor R).map ((u ≫ v) ≫ w)) ≫ laurentProjection P a =
      coefficientMap P ((laurentUnderFunctor R).map w) ≫
        (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u) := by
  rw [Functor.map_comp, coefficientMap_comp, Category.assoc, BassH0Merge.total]

/-- Canonical anchor of the original source-whiskered reference in the common total nerve. -/
def precompAnchor :
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)).functor ≅
      (coefficientModel P u ≫ BassOverlap.commonReference P v w).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (precomp_total P u v w)) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (laurentProjection P d ≫ coefficientMap P w ≫ coefficientMap P v)
        (coefficientMap P u)) AsSmall.up)

/-- Canonical anchor of the original Laurent-postcomposed reference in that same total nerve. -/
def postcompAnchor :
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)).functor ≅
      (BassOverlap.commonReference P u v ≫
        coefficientModel P ((laurentUnderFunctor R).map w)).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (postcomp_total P u v w)) ≪≫
      boundedFlatNormalizedPullbackCompIso (coefficientMap P ((laurentUnderFunctor R).map w))
        (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)) AsSmall.up)

/-- All 140 full source-whiskered nodes, in precisely the original insertion order. -/
def precompNodes : Fin 140 → CommonReferenceNerve.Node (BassH0Diagram.reference P ((u ≫ v) ≫ w)) :=
  ModelSimplex.reanchorNodes (precompAnchor P u v w)
    (fun i ↦ CommonReferenceNerve.precompNode (coefficientModel P u) (BassMWhole.nodes P v w i))

/-- All 140 full target-whiskered nodes, in precisely the original insertion order. -/
def postcompNodes : Fin 140 → CommonReferenceNerve.Node (BassH0Diagram.reference P ((u ≫ v) ≫ w)) :=
  ModelSimplex.reanchorNodes (postcompAnchor P u v w)
    (fun i ↦ CommonReferenceNerve.postcompNode
      (coefficientModel P ((laurentUnderFunctor R).map w)) (BassMWhole.nodes P u v i))

/-- The original source-whiskered cube uses the unchanged chosen scalar parameter. -/
def precompLift : C(Quillen.SimplexCubeExtension.Cube,
    |nerve (Codiscrete (CommonReferenceNerve.Node (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  (CommonReferenceNerve.parameter _ (precompNodes P u v w)).comp BassMWhole.scalarCube.{u}

/-- The original target-whiskered cube uses the unchanged chosen scalar parameter. -/
def postcompLift : C(Quillen.SimplexCubeExtension.Cube,
    |nerve (Codiscrete (CommonReferenceNerve.Node (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  (CommonReferenceNerve.parameter _ (postcompNodes P u v w)).comp BassMWhole.scalarCube.{u}

/-- Every source-whiskered finite family evaluates to the exact unchanged original native cube. -/
theorem precomp_native_cube (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily _ (precompNodes P u v w) n
        (BassMWhole.scalarCube.{u} ![r, s, t], x) =
      (BassMWhole.interiorCube P v w).level n
        (r, (s, (t, (boundedFlatPerfectPrespectrumMap (coefficientMap P u)).map n x))) := by
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  change prespectrumSimplexFamily (ModelSimplex.reanchorSimplex (precompAnchor P u v w)
    (fun i ↦ CommonReferenceNerve.precompNode (coefficientModel P u) (BassMWhole.nodes P v w i)))
    n (BassMWhole.scalarCube.{u} ![r, s, t], x) = _
  rw [ModelSimplex.reanchorSimplex_eq, ← CommonReferenceNerve.prespectrumFamily_eq,
    CommonReferenceNerve.prespectrumFamily_precomp, CommonReferenceNerve.prespectrumFamily_eq]
  exact (BassMWhole.interiorCube_level P v w n r s t
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P u)).map n x)).symm

/-- Every target-whiskered finite family evaluates to the exact unchanged original native cube. -/
theorem postcomp_native_cube (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily _ (postcompNodes P u v w) n
        (BassMWhole.scalarCube.{u} ![r, s, t], x) =
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map w))).map n
        ((BassMWhole.interiorCube P u v).level n (r, (s, (t, x)))) := by
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  change prespectrumSimplexFamily (ModelSimplex.reanchorSimplex (postcompAnchor P u v w)
    (fun i ↦ CommonReferenceNerve.postcompNode
      (coefficientModel P ((laurentUnderFunctor R).map w)) (BassMWhole.nodes P u v i)))
    n (BassMWhole.scalarCube.{u} ![r, s, t], x) = _
  rw [ModelSimplex.reanchorSimplex_eq, ← CommonReferenceNerve.prespectrumFamily_eq,
    CommonReferenceNerve.prespectrumFamily_postcomp, CommonReferenceNerve.prespectrumFamily_eq]
  exact congrArg
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map w))).map n)
    (BassMWhole.interiorCube_level P u v n r s t x).symm

end Quillen.PerfectComplexes.BassMWholeNerve
