/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionChartRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleParameters
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ProductSupport
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveParameter

/-!
# Complete original square rows in the projection rectangle

The chart row and polynomial column retain their actual five dependent reference nodes.
Their scalar words are the original reversed-first, forward-second paths L and Ppath.
Only the four used primitive edges are required to be ordered.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.ProjectionRectangleSquareRows
open BassH0Merge BassH1Join BassReferenceMerge

/-- The actual chart row carries L in its original order. -/
def chartRow : Fin 5 → Fin 18 := ![9, 10, 11, 12, 13]

/-- The actual polynomial column carries Ppath, with its original nonmonotone labels. -/
def polynomialRow : Fin 5 → Fin 18 := ![5, 6, 13, 7, 17]

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)

/-- The chart row keeps the exact projection-source transport before precomposition. -/
def chartAnchor : (ProjectionReference.reference c r).functor ≅
    (normalizedMap p ≫ NativeSquareFiveSimplex.source c q).functor :=
  rightRowReference (ProjectionReference.reference c r) c q p
    (nativeFirstReference p q c r hr)

/-- The polynomial column keeps the actual middle-square transport before postcomposition. -/
def polynomialAnchor : (ProjectionReference.reference c r).functor ≅
    (NativeSquareFiveSimplex.source b p ≫ normalizedMap q').functor :=
  nativeMiddleReference p q q' b c hq r hr ≪≫ BinaryNormalizationSimplex.total q' (b ≫ p)

private theorem chart_first_nodes (i : Fin 3) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (chartRow (NativeSquareFiveSimplex.firstFace.toOrderHom i)) =
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (binaryNodes c q i) := by
  have hi : chartRow (NativeSquareFiveSimplex.firstFace.toOrderHom i) =
      DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i) := by
    fin_cases i <;> rfl
  rw [hi]
  exact native_first_right_row p q p' q' a b c hp hq r hr i

private theorem chart_second_nodes (i : Fin 3) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (chartRow (NativeSquareFiveSimplex.secondFace.toOrderHom i)) =
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (rightRowReference (ProjectionReference.reference c r) q' b p
          (nativeMiddleReference p q q' b c hq r hr)) (binaryNodes q' b i) := by
  have hi : chartRow (NativeSquareFiveSimplex.secondFace.toOrderHom i) =
      DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i) := by
    fin_cases i <;> rfl
  rw [hi]
  exact native_middle_right_row p q p' q' a b c hp hq r hr i

private theorem polynomial_first_nodes (i : Fin 3) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (polynomialRow (NativeSquareFiveSimplex.firstFace.toOrderHom i)) =
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (binaryNodes b p i) := by
  have hi : polynomialRow (NativeSquareFiveSimplex.firstFace.toOrderHom i) =
      DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  rw [hi]
  exact native_middle_column p q p' q' a b c hp hq r hr i

private theorem polynomial_second_nodes (i : Fin 3) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (polynomialRow (NativeSquareFiveSimplex.secondFace.toOrderHom i)) =
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (H := BinaryNormalizationSimplex.sourceMap p' a)
        (nativeLastReference p q p' q' a b c hp hq r hr ≪≫
          BinaryNormalizationSimplex.total q' (p' ≫ a)) (binaryNodes p' a i) := by
  have hi : polynomialRow (NativeSquareFiveSimplex.secondFace.toOrderHom i) =
      DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  rw [hi]
  exact native_last_column p q p' q' a b c hp hq r hr i

/-- All five chart nodes retain their complete precomposed original square references. -/
theorem chart_row_nodes (i : Fin 5) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr (chartRow i) =
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i) := by
  have hs (j : Fin 3) :
      ProjectionReference.nodes p q p' q' a b c hp hq r hr
        (chartRow (NativeSquareFiveSimplex.secondFace.toOrderHom j)) =
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq
          (NativeSquareFiveSimplex.secondFace.toOrderHom j)) :=
    pre_families_match (ProjectionReference.reference c r) (normalizedMap p)
      (BinaryNormalizationSimplex.sourceMap q' b) (binaryNodes q' b)
      (chart_second_nodes p q p' q' a b c hp hq r hr)
      (pre_square_second_nodes c q q' b hq (ProjectionReference.reference c r)
        (normalizedMap p) (chartAnchor p q c r hr)) 0
      (chart_first_nodes p q p' q' a b c hp hq r hr 0) j
  fin_cases i
  · exact chart_first_nodes p q p' q' a b c hp hq r hr 0
  · exact chart_first_nodes p q p' q' a b c hp hq r hr 1
  · exact chart_first_nodes p q p' q' a b c hp hq r hr 2
  · exact hs 1
  · exact hs 2

/-- All five polynomial nodes keep the original square equality and full postcomposition anchor. -/
theorem polynomial_row_nodes (i : Fin 5) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr (polynomialRow i) =
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr)
        (NativeSquareFiveSimplex.nodes b p p' a hp i) := by
  have hs (j : Fin 3) :
      ProjectionReference.nodes p q p' q' a b c hp hq r hr
        (polynomialRow (NativeSquareFiveSimplex.secondFace.toOrderHom j)) =
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp
          (NativeSquareFiveSimplex.secondFace.toOrderHom j)) :=
    post_families_match (ProjectionReference.reference c r) (normalizedMap q')
      (BinaryNormalizationSimplex.sourceMap p' a) (binaryNodes p' a)
      (polynomial_second_nodes p q p' q' a b c hp hq r hr)
      (post_square_second_nodes b p p' a hp (ProjectionReference.reference c r)
        (normalizedMap q') (polynomialAnchor p q q' b c hq r hr)) 0
      (polynomial_first_nodes p q p' q' a b c hp hq r hr 0) j
  fin_cases i
  · exact polynomial_first_nodes p q p' q' a b c hp hq r hr 0
  · exact polynomial_first_nodes p q p' q' a b c hp hq r hr 1
  · exact polynomial_first_nodes p q p' q' a b c hp hq r hr 2
  · exact hs 1
  · exact hs 2

/-- Only the actual primitive edges need to preserve the vertex order. -/
theorem primitive_rows_monotone (j : Fin 2) (i : Fin 4) :
    Monotone ((![chartRow, polynomialRow] j) ∘ (BassH1Support.edgeFace i).toOrderHom) :=
  (by decide : ∀ (j : Fin 2) (i : Fin 4),
    Monotone ((![chartRow, polynomialRow] j) ∘ (BassH1Support.edgeFace i).toOrderHom)) j i

/-- The polynomial row cannot be used as a globally ordered face. -/
theorem polynomialRow_not_monotone : ¬ Monotone polynomialRow := by decide

/-- The entire original L path is recovered in any actual rectangle face. -/
theorem chart_parameter {k : ℕ} (α : ⦋17⦌ ⟶ ⦋k⦌) (s : unitInterval) :
    StdSimplex.map (α.toOrderHom ∘ chartRow) (NativeSquareFiveSimplex.parameter s) =
      ProjectionRectangleParameters.L α s :=
  BassSupportOrder.map_two_binary (α.toOrderHom ∘ chartRow) 0 1 2 3 4 s

/-- The entire original Ppath keeps its reversed-first, forward-second subdivision. -/
theorem polynomial_parameter {k : ℕ} (α : ⦋17⦌ ⟶ ⦋k⦌) (s : unitInterval) :
    StdSimplex.map (α.toOrderHom ∘ polynomialRow) (NativeSquareFiveSimplex.parameter s) =
      ProjectionRectangleParameters.Ppath α s :=
  BassSupportOrder.map_two_binary (α.toOrderHom ∘ polynomialRow) 0 1 2 3 4 s



/-- Newly reconstructed client: whole original row parameter, using only primitive edges. -/
theorem chart_nerve_parameter (t : unitInterval) :
    CommonReferenceNerve.parameter (ProjectionReference.reference c r) (ProjectionReference.nodes
      p q p' q' a b c hp hq r hr)
      (StdSimplex.map chartRow (NativeSquareFiveSimplex.parameter t)) =
    CommonReferenceNerve.parameter (ProjectionReference.reference c r) (fun i ↦ preReferenceNode
      (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i))
      (NativeSquareFiveSimplex.parameter t) := by
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in t
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported _ _ _ chartRow
    (chart_row_nodes p q p' q' a b c hp hq r hr) (BassH1Support.edgeFace i)
    (primitive_rows_monotone 0 i) z

/-- Every native level of the five full original row nodes, with its specified reference. -/
theorem chart_row_family (n : ℕ) (z : StdSimplex ℝ (Fin 5))
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).space n) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r)
      (fun i ↦ ProjectionReference.nodes p q p' q' a b c hp hq r hr (chartRow i)) n (z, x) =
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i)) n (z, x) := by
  have hn := funext (chart_row_nodes p q p' q' a b c hp hq r hr)
  rw [hn]

/-- The original base point is fixed at every row parameter and every native level. -/
theorem chart_row_point (n : ℕ) (t : unitInterval) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i)) n
      (NativeSquareFiveSimplex.parameter t,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).point n) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen C'))).point n :=
  CommonReferenceNerve.prespectrumFamily_point _ _ n _

/-- The structure coordinate stays independent of the complete original row time. -/
theorem chart_row_structure (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).space n) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i)) (n + 1)
      (NativeSquareFiveSimplex.parameter s,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).structureMap n x t) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen C'))).structureMap n
      (CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
        preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i)) n
        (NativeSquareFiveSimplex.parameter s, x)) t :=
  CommonReferenceNerve.prespectrumFamily_structure _ _ n _ x t

/-- Newly reconstructed client: whole original row parameter, using only primitive edges. -/
theorem polynomial_nerve_parameter (t : unitInterval) :
    CommonReferenceNerve.parameter (ProjectionReference.reference c r) (ProjectionReference.nodes
      p q p' q' a b c hp hq r hr)
      (StdSimplex.map polynomialRow (NativeSquareFiveSimplex.parameter t)) =
    CommonReferenceNerve.parameter (ProjectionReference.reference c r) (fun i ↦ postReferenceNode
      (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp i))
      (NativeSquareFiveSimplex.parameter t) := by
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in t
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported _ _ _ polynomialRow
    (polynomial_row_nodes p q p' q' a b c hp hq r hr) (BassH1Support.edgeFace i)
    (primitive_rows_monotone 1 i) z

/-- Every native level of the five full original row nodes, with its specified reference. -/
theorem polynomial_row_family (n : ℕ) (z : StdSimplex ℝ (Fin 5))
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).space n) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r)
      (fun i ↦ ProjectionReference.nodes p q p' q' a b c hp hq r hr (polynomialRow i)) n (z, x) =
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp i)) n (z,
          x) := by
  have hn := funext (polynomial_row_nodes p q p' q' a b c hp hq r hr)
  rw [hn]

/-- The original base point is fixed at every row parameter and every native level. -/
theorem polynomial_row_point (n : ℕ) (t : unitInterval) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp i)) n
      (NativeSquareFiveSimplex.parameter t,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).point n) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen C'))).point n :=
  CommonReferenceNerve.prespectrumFamily_point _ _ n _

/-- The structure coordinate stays independent of the complete original row time. -/
theorem polynomial_row_structure (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).space n) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp i)) (n + 1)
      (NativeSquareFiveSimplex.parameter s,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).structureMap n x t) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen C'))).structureMap n
      (CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
        postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp i)) n
        (NativeSquareFiveSimplex.parameter s, x)) t :=
  CommonReferenceNerve.prespectrumFamily_structure _ _ n _ x t

end Quillen.PerfectComplexes.ProjectionRectangleSquareRows
