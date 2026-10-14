/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OldChartMiddleNormal

/-! Full middle and last binary columns in the original merged square-composition diagram. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassH0Merge
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- Every middle-triple node retains the original whole-square source reference. -/
theorem merged_middle_nodes (i : Fin 8) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.middleFace.toOrderHom i) =
    (⟨SplitTripleSimplex.vertices q' b p i,
      DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq ≪≫
        SplitTripleSimplex.references q' b p i⟩ : DoubleSquareCommonSimplex.Node p q c) :=
  (DoubleSquareMergedSimplex.middle_nodes p q p' q' a b c hp hq i).trans
    (DoubleSquareCommonSimplex.middle_nodes p q p' q' a b c hp hq i)

/-- Every last-triple node retains the actual total-square source equality. -/
theorem merged_last_nodes (i : Fin 8) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.lastFace.toOrderHom i) =
    (⟨SplitTripleSimplex.vertices q' p' a i,
      DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
        SplitTripleSimplex.references q' p' a i⟩ : DoubleSquareCommonSimplex.Node p q c) :=
  (DoubleSquareMergedSimplex.last_nodes p q p' q' a b c hp hq i).trans
    (DoubleSquareCommonSimplex.last_nodes p q p' q' a b c hp hq i)

/-- The entire original middle binary column is its native binary family postcomposed by q'. -/
theorem merged_middle_column (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
    postReferenceNode (NormalizedTripleSimplex.sourceMap c q p) (normalizedMap q')
      (H := BinaryNormalizationSimplex.sourceMap b p)
      (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq ≪≫
        BinaryNormalizationSimplex.total q' (b ≫ p)) (binaryNodes b p i) :=
  (merged_middle_nodes p q p' q' a b c hp hq (leftIndex i)).trans
    (triple_left_column_iso (NormalizedTripleSimplex.sourceMap c q p) q' b p
      (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq) i)

/-- The entire last column retains the original total equality before both binary pieces. -/
theorem merged_last_column (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
    postReferenceNode (NormalizedTripleSimplex.sourceMap c q p) (normalizedMap q')
      (H := BinaryNormalizationSimplex.sourceMap p' a)
      (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
        BinaryNormalizationSimplex.total q' (p' ≫ a)) (binaryNodes p' a i) :=
  (merged_last_nodes p q p' q' a b c hp hq (leftIndex i)).trans
    (triple_left_column_iso (NormalizedTripleSimplex.sourceMap c q p) q' p' a
      (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq) i)

end Quillen.PerfectComplexes.BassH1Join
