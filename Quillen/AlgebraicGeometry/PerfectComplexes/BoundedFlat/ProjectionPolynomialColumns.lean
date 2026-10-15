/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PostReferenceFamily

/-! The actual two polynomial columns in a projection rectangle with full reference transports. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassH0Merge

/-- The native triple's left column works with its actual arbitrary reference iso. -/
theorem triple_left_column_iso {X Y Z T : Scheme.{u}}
    (F : modelOf (boundedFlatPerfectWaldhausen T) ⟶ modelOf (boundedFlatPerfectWaldhausen X))
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (ρ : F.functor ≅ (NormalizedTripleSimplex.sourceMap f g h).functor) (i : Fin 3) :
    (⟨SplitTripleSimplex.vertices f g h (leftIndex i),
      ρ ≪≫ SplitTripleSimplex.references f g h (leftIndex i)⟩ :
      Σ G : modelOf (boundedFlatPerfectWaldhausen T) ⟶ modelOf (boundedFlatPerfectWaldhausen X),
        F.functor ≅ G.functor) =
      postReferenceNode F (normalizedMap f) (H := BinaryNormalizationSimplex.sourceMap g h)
        (ρ ≪≫ BinaryNormalizationSimplex.total f (g ≫ h)) (binaryNodes g h i) := by
  have hn := congrArg (anchorNode ρ)
    (triple_left_column (NormalizedTripleSimplex.sourceMap f g h) f g h rfl i)
  simpa only [tripleLeftNode, binaryColumnNode, anchorNode, eqToIso_refl,
    Iso.refl_trans, postReferenceNode, Iso.trans_assoc] using hn

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)

/--
The reference from the projection source to the middle triple `q', b, p`, combining the
projection and middle-square transports.
-/
def nativeMiddleReference : (ProjectionReference.reference c r).functor ≅
    (NormalizedTripleSimplex.sourceMap q' b p).functor :=
  eqToIso (ProjectionReference.anchor p q c r hr) ≪≫
    DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq

/-- Every original middle-triple node retains the actual projection/source transports. -/
theorem native_middle_nodes (i : Fin 8) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (DoubleSquareMergedSimplex.middleFace.toOrderHom i) =
    (⟨SplitTripleSimplex.vertices q' b p i,
      nativeMiddleReference p q q' b c hq r hr ≪≫ SplitTripleSimplex.references q' b p i⟩ :
      ProjectionReference.Node c r) := by
  have hn := projection_middle_nodes p q p' q' a b c hp hq r hr
    (ProjectionReference.reference c r) rfl i
  have he : projectionNativeNode p q p' q' a b c hp hq r hr
      (ProjectionReference.reference c r) rfl
      (DoubleSquareMergedSimplex.middleFace.toOrderHom i) =
      ProjectionReference.nodes p q p' q' a b c hp hq r hr
        (DoubleSquareMergedSimplex.middleFace.toOrderHom i) := anchorNode_refl _
  exact he.symm.trans (by
    simpa only [projectionMiddleReference, projectionFirstReference, eqToIso_refl,
      Iso.refl_trans, nativeMiddleReference] using hn)

/-- The first whole polynomial binary column is the original middle triple's left column. -/
theorem native_middle_column (i : Fin 3) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (H := BinaryNormalizationSimplex.sourceMap b p)
        (nativeMiddleReference p q q' b c hq r hr ≪≫ BinaryNormalizationSimplex.total q' (b ≫ p))
        (binaryNodes b p i) :=
  (native_middle_nodes p q p' q' a b c hp hq r hr (leftIndex i)).trans
    (triple_left_column_iso (ProjectionReference.reference c r) q' b p
      (nativeMiddleReference p q q' b c hq r hr) i)

/-- The second polynomial binary column keeps the original total-square reference transport. -/
theorem native_last_column (i : Fin 3) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (H := BinaryNormalizationSimplex.sourceMap p' a)
        (nativeLastReference p q p' q' a b c hp hq r hr ≪≫
          BinaryNormalizationSimplex.total q' (p' ≫ a)) (binaryNodes p' a i) :=
  (native_last_nodes p q p' q' a b c hp hq r hr (leftIndex i)).trans
    (triple_left_column_iso (ProjectionReference.reference c r) q' p' a
      (nativeLastReference p q p' q' a b c hp hq r hr) i)

end Quillen.PerfectComplexes.BassH1Join
