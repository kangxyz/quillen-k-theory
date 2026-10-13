/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.CanonicalFiberObjectSquare

/-! # Original transformation and reversed canonical-fiber square consumers -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Convexity
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u v
namespace QuillenTest.CanonicalFiberObjectSquare

open Quillen
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Two independent simplex operators retain the original weak-arrow grid. -/
theorem original_component_cylinder {A B : C} (f : A ⟶ B) (hf : W.weq f)
    {n : SimplexCategory} (α τ : n ⟶ ⦋1⦌) :
    nerveCylinderDiagram
        (whiskerLeft (Structure.intervalProjection n ⋙ indexMap α)
          ((oneEmbedding W).map f).hom) τ =
      gridMap₂ α τ ⋙ (W.weakObjectSimplex f hf).val :=
  W.weakObjectSimplex_cylinder f hf α τ

variable {D : Type u} [Category.{v} D] (V : Structure D) {F G : D ⥤ C}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))
  (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)

/-- The transformation and object-loop times remain independent on the whole original square. -/
theorem original_transformation_square (A : D) (s t : unitInterval) :
    objectTransformationTrack V W hF hG η hη hF0 hG0 A (s, t) =
      bisimplexRealization W (W.weakObjectSimplex (η.app A) (hη A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (η.app A) (hη A)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) :=
  objectTransformationRealization_square V W hF hG η hη hF0 hG0 A s t

variable {W} (N : NestedWeakEquivalences W)

/-- The unchanged projection is the original fine object loop. -/
theorem original_fiber_projection (X : AcyclicCategory N) (t : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.1 = W.kZeroObjectLoop X.obj t :=
  canonicalFiberObjectLoop_projection N X t

/-- The actual fiber coordinate reverses only the nerve coordinate of the original square. -/
theorem original_reversed_fiber_square (X : AcyclicCategory N) (t s : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 s =
      bisimplexRealization N.coarse
        (N.coarse.weakObjectSimplex ((zeroToAcyclicInclusion N).app X)
          (zeroToAcyclicInclusion_weak N X)).val
        ((isSimplex₂_diagonal_iff N.coarse.cof N.coarse.weq _).mpr
          (N.coarse.weakObjectSimplex ((zeroToAcyclicInclusion N).app X)
            (zeroToAcyclicInclusion_weak N X)).property)
        (StdSimplex.homeomorphI.symm t,
          StdSimplex.homeomorphI.symm (unitInterval.symm s)) :=
  canonicalFiberObjectLoop_path_square N X t s

/-- The initial fiber face is the actual coarse image of the original fine object loop. -/
theorem original_fiber_path_source (X : AcyclicCategory N) (t : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 0 =
      changeWeakMap N ((canonicalFiberObjectLoop N X t).val.1) :=
  (canonicalFiberObjectLoop N X t).property.1

/-- The terminal fiber face is the actual coarse basepoint. -/
theorem original_fiber_path_target (X : AcyclicCategory N) (t : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 1 = N.coarse.kBasepoint :=
  (canonicalFiberObjectLoop N X t).property.2

end QuillenTest.CanonicalFiberObjectSquare
