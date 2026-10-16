/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnitNodes
public import Quillen.Topology.Realization.SimplexGridBoundary
public import Quillen.Topology.Realization.SimplexGridColumn
public import Quillen.Topology.Path.SimplexCollapsedEdges

/-! A common finite diagram for the exact moving pieces of the original polynomial-span unit.
All six shared reference nodes are identified before the scalar squares are pasted. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientPolynomialSpanUnitTop
open CoefficientPolynomialSpanUnitNodes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- Five free nodes on each chart, followed by the full original fifteen-node middle grid. -/
def nodes (i : Fin 25) : Node P a :=
  if h : i.val < 5 then plusNodes P a ⟨i.val, by omega⟩ else
    if h' : i.val < 10 then minusNodes P a ⟨i.val - 5, by omega⟩ else
      middleNodes P a ⟨i.val - 10, by omega⟩

def plusIndex (i : Fin 8) : Fin 25 :=
  ⟨if i.val < 5 then i.val else 5 * (i.val - 5) + 12, by split_ifs <;> omega⟩
def minusIndex (i : Fin 8) : Fin 25 :=
  ⟨if i.val < 5 then i.val + 5 else 5 * (i.val - 5) + 14, by split_ifs <;> omega⟩
def middleIndex (i : Fin 15) : Fin 25 := ⟨10 + i.val, by omega⟩

def plusFace : ⦋7⦌ ⟶ ⦋24⦌ := SimplexCategory.Hom.mk ⟨plusIndex, by
  intro i j h
  change (plusIndex i).val ≤ (plusIndex j).val
  dsimp [plusIndex]
  split_ifs <;> omega⟩
def minusFace : ⦋7⦌ ⟶ ⦋24⦌ := SimplexCategory.Hom.mk ⟨minusIndex, by
  intro i j h
  change (minusIndex i).val ≤ (minusIndex j).val
  dsimp [minusIndex]
  split_ifs <;> omega⟩
def middleFace : ⦋14⦌ ⟶ ⦋24⦌ := SimplexCategory.Hom.mk ⟨middleIndex, by
  intro i j h
  change 10 + i.val ≤ 10 + j.val
  omega⟩

theorem plus_nodes (i : Fin 8) : nodes P a (plusFace.toOrderHom i) = plusNodes P a i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (plus_shared P a 0).symm
  · exact (plus_shared P a 1).symm
  · exact (plus_shared P a 2).symm

theorem minus_nodes (i : Fin 8) : nodes P a (minusFace.toOrderHom i) = minusNodes P a i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (minus_shared P a 0).symm
  · exact (minus_shared P a 1).symm
  · exact (minus_shared P a 2).symm

theorem middle_nodes (i : Fin 15) :
    nodes P a (middleFace.toOrderHom i) = middleNodes P a i := by
  fin_cases i <;> rfl

/-- One actual simplex contains all three unchanged moving pieces, with the six joins shared. -/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))) 24 :=
  ModelSimplex.ofIsos (source P a) (fun i ↦ (nodes P a i).1) (fun i ↦ (nodes P a i).2)

theorem plus_face : (simplex P a).face plusFace =
    CoefficientPolynomialSpanUnitSimplex.plusSimplex P a := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (plus_nodes P a)).trans (plus_family P a)

theorem minus_face : (simplex P a).face minusFace =
    CoefficientPolynomialSpanUnitSimplex.minusSimplex P a := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (minus_nodes P a)).trans (minus_family P a)

theorem middle_face : (simplex P a).face middleFace =
    CoefficientPolynomialSpanUnitSimplex.middleSimplex P a := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (middle_nodes P a)).trans (middle_family P a)

/-- The two unchanged independent coordinates of the positive square in the merged simplex. -/
def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  (embed plusFace).comp OriginalUnitSquareSimplex.squareParameter

def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  (embed minusFace).comp OriginalUnitSquareSimplex.squareParameter

def middleParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  (embed middleFace).comp CoefficientPolynomialSpanUnitSimplex.middleParameter.{u}

private theorem family_simplex_congr {V W : Model.{u}} {k : ℕ}
    (S T : ModelSimplex V W k) (h : S = T) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (z, x) = prespectrumSimplexFamily T n (z, x) :=
  congrArg (fun U ↦ prespectrumSimplexFamily U n (z, x)) h

private theorem family_parameter_congr {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (n : ℕ)
    (z w : StdSimplex ℝ (Fin (k + 1))) (h : z = w) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (z, x) = prespectrumSimplexFamily S n (w, x) :=
  congrArg (fun v ↦ prespectrumSimplexFamily S n (v, x)) h

theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (plusParameter (r, s), x) =
      ((boundedFlatCoefficientPolynomialIdentitySquare P a).postcompose
        (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).level n (r, (s, x)) := by
  refine (prespectrumSimplexFamily_face (simplex P a) plusFace n
    (OriginalUnitSquareSimplex.squareParameter (r, s)) x).trans ?_
  refine (family_simplex_congr _ _ (plus_face P a) n _ x).trans ?_
  exact CoefficientPolynomialSpanUnitSimplex.plus_native P a n r s x

theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (minusParameter (r, s), x) =
      ((boundedFlatCoefficientPolynomialIdentitySquare P a).postcompose
        (boundedFlatPerfectPrespectrumMap (laurentMinus P a))).level n (r, (s, x)) := by
  refine (prespectrumSimplexFamily_face (simplex P a) minusFace n
    (OriginalUnitSquareSimplex.squareParameter (r, s)) x).trans ?_
  refine (family_simplex_congr _ _ (minus_face P a) n _ x).trans ?_
  exact CoefficientPolynomialSpanUnitSimplex.minus_native P a n r s x

theorem middle_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (middleParameter.{u} (r, s), x) =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n
          (s, (boundedFlatCoefficientIdentityHomotopy P a).level n (r, x))) := by
  refine (prespectrumSimplexFamily_face (simplex P a) middleFace n
    (CoefficientPolynomialSpanUnitSimplex.middleParameter.{u} (r, s)) x).trans ?_
  refine (family_simplex_congr _ _ (middle_face P a) n _ x).trans ?_
  exact CoefficientPolynomialSpanUnitSimplex.middle_native P a n r s x

private theorem map_projection {d : ℕ} (α : ⦋4⦌ ⟶ ⦋d⦌) (t : unitInterval) :
    embed α (BassProjectionPath.parameter t) =
      ((binaryPath (α.toOrderHom 0) (α.toOrderHom 1) (α.toOrderHom 2)).symm.trans
        (binaryPath (α.toOrderHom 0) (α.toOrderHom 3) (α.toOrderHom 4))) t :=
  map_trans_values _ _ _ _ _ (fun t ↦ map_binaryPath α 0 1 2 (unitInterval.symm t))
    (map_binaryPath α 0 3 4) t

/-- Reindex the actual unit square and retain its four literal scalar path boundaries. -/
def unitFaceSquare {d : ℕ} (α : ⦋7⦌ ⟶ ⦋d⦌) :
    ParameterSquare
      ((binaryPath (α.toOrderHom 0) (α.toOrderHom 1) (α.toOrderHom 2)).symm.trans
        (binaryPath (α.toOrderHom 0) (α.toOrderHom 4) (α.toOrderHom 5)))
      (Path.refl (StdSimplex.single (α.toOrderHom 7)))
      (binaryPath (α.toOrderHom 2) (α.toOrderHom 3) (α.toOrderHom 7))
      (binaryPath (α.toOrderHom 5) (α.toOrderHom 6) (α.toOrderHom 7)) :=
  ParameterSquare.ofBoundaryPaths
    ((ParameterSquare.ofBoundary OriginalUnitSquareSimplex.rotatedParameter).reindex α) _ _ _ _
      (fun t ↦ (map_trans_values _ _ _ _ _
        (fun t ↦ map_binaryPath α 0 1 2 (unitInterval.symm t))
        (map_binaryPath α 0 4 5) t).symm)
      (fun _ ↦ (StdSimplex.map_single _ _).symm)
      (fun t ↦ (map_binaryPath α 2 3 7 t).symm)
      (fun t ↦ (map_binaryPath α 5 6 7 t).symm)

abbrev plusSquare := unitFaceSquare plusFace
abbrev minusSquare := (unitFaceSquare minusFace).reversePaths

def middleStart : Path (StdSimplex.single 12 : StdSimplex ℝ (Fin 25))
    (StdSimplex.single 14) := (binaryPath 10 11 12).symm.trans (binaryPath 10 13 14)
def middleEnd : Path (StdSimplex.single 22 : StdSimplex ℝ (Fin 25))
    (StdSimplex.single 24) := (binaryPath 20 21 22).symm.trans (binaryPath 20 23 24)

/-- The whole product square, with its two scalar row paths and two exact common-node columns. -/
def middleSquare : ParameterSquare middleStart middleEnd
    (binaryPath 12 17 22) (binaryPath 14 19 24) where
  parameter := middleParameter.{u}
  at_zero t := by
    change StdSimplex.map middleFace.toOrderHom
      (SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 0,
        BassProjectionPath.parameter t)) = _
    rw [Path.source, SimplexGrid.parameter_row, ← StdSimplex.map_comp]
    exact map_projection (SimplexGrid.rowFace 2 4 0 ≫ middleFace) t
  at_one t := by
    change StdSimplex.map middleFace.toOrderHom
      (SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 1,
        BassProjectionPath.parameter t)) = _
    rw [Path.target, SimplexGrid.parameter_row, ← StdSimplex.map_comp]
    exact map_projection (SimplexGrid.rowFace 2 4 2 ≫ middleFace) t
  left r := by
    change StdSimplex.map middleFace.toOrderHom
      (SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 r,
        BassProjectionPath.parameter 0)) = _
    rw [Path.source, SimplexGrid.parameter_column, ← StdSimplex.map_comp]
    exact map_binaryPath (SimplexGrid.columnFace 2 4 2 ≫ middleFace) 0 1 2 r
  right r := by
    change StdSimplex.map middleFace.toOrderHom
      (SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 r,
        BassProjectionPath.parameter 1)) = _
    rw [Path.target, SimplexGrid.parameter_column, ← StdSimplex.map_comp]
    exact map_binaryPath (SimplexGrid.columnFace 2 4 4 ≫ middleFace) 0 1 2 r

/-- These are entire scalar join equalities, proved before any native-family evaluation. -/
theorem plus_middle_join (r : unitInterval) :
    plusSquare.parameter (r, 1) = middleSquare.{u}.parameter (r, 0) :=
  (plusSquare.right r).trans (middleSquare.left r).symm

theorem middle_minus_join (r : unitInterval) :
    middleSquare.{u}.parameter (r, 1) = minusSquare.parameter (r, 0) :=
  (middleSquare.right r).trans (minusSquare.left r).symm

/-- The original positive, moving-middle and reversed negative pieces keep their association. -/
def movingSquare := plusSquare.pastePaths (middleSquare.{u}.pastePaths minusSquare)

/-- Retain the original two constant-cylinder contractions, without changing their speeds. -/
def targetContraction :
    ((Path.refl (StdSimplex.single 22)).trans
      (middleEnd.trans (Path.refl (StdSimplex.single 24)))).Homotopy middleEnd :=
  (Path.Homotopy.reflTrans (middleEnd.trans (Path.refl (StdSimplex.single 24)))).trans
    (Path.Homotopy.transRefl middleEnd)

/-- The original identity-span parameter: boundary extraction, both contractions, then descent. -/
def topBoundary := movingSquare.{u}.toBoundary.trans
  (((Path.Homotopy.refl (binaryPath (k := 24) 2 3 22)).hcomp targetContraction).hcomp
    (Path.Homotopy.refl (binaryPath (k := 24) 7 8 24).symm))

def topParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  collapsed topBoundary.{u}

/-- The complete lower edge keeps the original positive, overlap, inverse word and association. -/
theorem top_zero (t : unitInterval) :
    topParameter.{u} (0, t) =
      (((binaryPath (k := 24) 0 1 2).symm.trans (binaryPath 0 4 12)).trans
        (middleStart.trans
          ((binaryPath 5 6 7).symm.trans (binaryPath 5 9 14)).symm)) t :=
  collapsed_zero_path topBoundary.{u} t

/-- Both target pauses have been contracted at the exact original speed. -/
theorem top_one (t : unitInterval) : topParameter.{u} (1, t) = middleEnd t :=
  collapsed_top_path topBoundary.{u} t

/-- The whole positive endpoint is the original two-step polynomial identity track. -/
theorem top_left (r : unitInterval) :
    topParameter.{u} (r, 0) = binaryPath (k := 24) 2 3 22 r :=
  collapsed_left_path topBoundary.{u} r

/-- The inverse endpoint keeps its separate original two-step polynomial identity track. -/
theorem top_right (r : unitInterval) :
    topParameter.{u} (r, 1) = binaryPath (k := 24) 7 8 24 r :=
  collapsed_right_path topBoundary.{u} r

abbrev polynomialMap := boundedFlatPerfectPrespectrumMap (polynomialProjection P a)
abbrev comparisonMap := boundedFlatCoefficientBassSquareComparison P a

/-- The unchanged native moving square, before its identity-cylinder contractions. -/
def movingNative := HomotopyPushout.identicalLegMovingSquare
  (polynomialMap P a) (polynomialMap P a)
  (boundedFlatCoefficientPolynomialSquareHomotopy P (𝟙 a))
  (coneSquareIdentityTrack (polynomialMap P a))
  (boundedFlatCoefficientIdentityHomotopy P a)
  (boundedFlatCoefficientPolynomialIdentityHomotopy P a)
  (boundedFlatCoefficientPolynomialIdentitySquare P a)

private theorem native_paste_value {E F : LoopPrespectrum.{u}}
    {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
    (J : H₀.Square H₁ L M) (K : K₀.Square K₁ M N)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.pastePaths K).level n (r, (s, x)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        J.level n (r, (⟨2 * s,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x))
      else K.level n (r, (⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

private theorem mapped_paste_evaluate {d : ℕ} {U : Type*}
    {a₀ b₀ c₀ a₁ b₁ c₁ : StdSimplex ℝ (Fin (d + 1))}
    {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁} {q₀ : Path b₀ c₀} {q₁ : Path b₁ c₁}
    {l : Path a₀ a₁} {m : Path b₀ b₁} {j : Path c₀ c₁}
    {E F : LoopPrespectrum.{u}} {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
    (Q : ParameterSquare p₀ p₁ l m) (R : ParameterSquare q₀ q₁ m j)
    (J : H₀.Square H₁ L M) (K : K₀.Square K₁ M N) (n : ℕ) (x : E.space n)
    (e : StdSimplex ℝ (Fin (d + 1)) → U) (v : F.space n → U)
    (hQ : ∀ r s, e (Q.parameter (r, s)) = v (J.level n (r, (s, x))))
    (hR : ∀ r s, e (R.parameter (r, s)) = v (K.level n (r, (s, x))))
    (r s : unitInterval) :
    e ((Q.pastePaths R).parameter (r, s)) = v ((J.pastePaths K).level n (r, (s, x))) := by
  rw [ParameterSquare.pastePaths_apply, native_paste_value]
  split
  · exact hQ _ _
  · exact hR _ _

/-- All three pieces paste to the actual native moving square, before the original postmap. -/
theorem moving_native : SquareLift (simplex P a) movingSquare.{u}
    ((movingNative P a).postcompose (comparisonMap P a)) := by
  intro n r s x
  change prespectrumSimplexFamily (simplex P a) n (movingSquare.parameter (r, s), x) =
    (comparisonMap P a).map n ((movingNative P a).level n (r, (s, x)))
  unfold movingSquare movingNative HomotopyPushout.identicalLegMovingSquare
  refine mapped_paste_evaluate _ _ _ _ n x
    (fun z ↦ prespectrumSimplexFamily (simplex P a) n (z, x))
    ((comparisonMap P a).map n) ?_ ?_ r s
  · intro r s
    exact plus_native P a n r s x
  · intro r s
    refine mapped_paste_evaluate _ _ _ _ n x
      (fun z ↦ prespectrumSimplexFamily (simplex P a) n (z, x))
      ((comparisonMap P a).map n) ?_ ?_ r s
    · intro r s
      exact middle_native P a n r s x
    · intro r s
      exact minus_native P a n r (unitInterval.symm s) x

/-- The unpaused original cylinder is the terminal row of the actual product grid. -/
theorem cylinder_native : PathLift (simplex P a) middleEnd
    ((HomotopyPushout.glue (polynomialMap P a) (polynomialMap P a)).postcomp
      (comparisonMap P a)) := by
  intro n s x
  refine (family_parameter_congr (simplex P a) n _ _ (middleSquare.at_one s).symm x).trans ?_
  refine (middle_native P a n 1 s x).trans ?_
  exact congrArg (fun y ↦ (comparisonMap P a).map n
    (HomotopyPushout.cylinder (polynomialMap P a) (polynomialMap P a) n (s, y)))
    ((boundedFlatCoefficientIdentityHomotopy P a).at_one n x)

/-- The scalar terminal vertex is the exact target of the unchanged original cylinder. -/
theorem cylinder_target_native : PathLift (simplex P a) (Path.refl (StdSimplex.single 24))
    ((Quillen.LoopPrespectrum.Homotopy.refl ((polynomialMap P a) ≫
      HomotopyPushout.inr (polynomialMap P a) (polynomialMap P a))).postcomp
      (comparisonMap P a)) := by
  intro n t x
  refine (family_parameter_congr (simplex P a) n _ _ middleEnd.target.symm x).trans ?_
  exact (cylinder_native P a n 1 x).trans (congrArg ((comparisonMap P a).map n)
    ((HomotopyPushout.glue (polynomialMap P a) (polynomialMap P a)).at_one n x))

/-- Both original constant pieces of the target cylinder contract with their exact native speeds. -/
theorem target_contraction_native : HomotopyLift (simplex P a) targetContraction
    ((HomotopyPushout.identicalLegIdentityTargetComparison (polynomialMap P a)).postcomp
      (comparisonMap P a)) := by
  have h := cylinder_native P a
  have hc := cylinder_target_native P a
  have hp := PathLift.postcompTrans (simplex P a) (comparisonMap P a) h hc
  exact HomotopyLift.postcompTrans (simplex P a) (comparisonMap P a)
    (PathLift.postcompReflTrans (simplex P a) (comparisonMap P a) hp)
    (PathLift.postcompTransRefl (simplex P a) (comparisonMap P a) h)

/-- The whole left endpoint track of the moving square is the original polynomial unit. -/
theorem left_native : PathLift (simplex P a) (binaryPath (k := 24) 2 3 22)
    ((Homotopy.precomp (polynomialMap P a)
      ((boundedFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
        (HomotopyPushout.inl (polynomialMap P a) (polynomialMap P a)))).postcomp
      (comparisonMap P a)) := by
  intro n r x
  refine (family_parameter_congr (simplex P a) n _ _ (plusSquare.left r).symm x).trans ?_
  refine (plus_native P a n r 0 x).trans ?_
  exact congrArg ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n)
    ((boundedFlatCoefficientPolynomialIdentitySquare P a).left n r x)

/-- The whole right endpoint track retains the separate inverse Laurent chart. -/
theorem right_native : PathLift (simplex P a) (binaryPath (k := 24) 7 8 24)
    ((Homotopy.precomp (polynomialMap P a)
      ((boundedFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
        (HomotopyPushout.inr (polynomialMap P a) (polynomialMap P a)))).postcomp
      (comparisonMap P a)) := by
  intro n r x
  refine (family_parameter_congr (simplex P a) n _ _
    ((unitFaceSquare minusFace).left r).symm x).trans ?_
  refine (minus_native P a n r 0 x).trans ?_
  exact congrArg ((boundedFlatPerfectPrespectrumMap (laurentMinus P a)).map n)
    ((boundedFlatCoefficientPolynomialIdentitySquare P a).left n r x)

/-- Every point of the original polynomial-span identity cylinder after the unchanged Bass map
has this explicit common-simplex parameter. No span identity or comparison track is replaced. -/
theorem top_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (topParameter.{u} (r, t), x) =
      ((boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).postcomp
        (boundedFlatCoefficientBassSquareComparison P a)).level n
        (r, HomotopyPushout.cylinder (polynomialMap P a) (polynomialMap P a) n (t, x)) := by
  have hm : HomotopyLift (simplex P a) movingSquare.{u}.toBoundary
      ((movingNative P a).toBoundary.postcomp (comparisonMap P a)) :=
    SquareLift.toBoundary (simplex P a) (moving_native P a)
  let L := Homotopy.precomp (polynomialMap P a)
    ((boundedFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
      (HomotopyPushout.inl (polynomialMap P a) (polynomialMap P a)))
  let M := Homotopy.precomp (polynomialMap P a)
    ((boundedFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
      (HomotopyPushout.inr (polynomialMap P a) (polynomialMap P a)))
  have hl : HomotopyLift (simplex P a)
      (Path.Homotopy.refl (binaryPath (k := 24) 2 3 22))
      ((Homotopy.RelHomotopy.refl L).postcomp (comparisonMap P a)) := by
    intro n r s x
    exact left_native P a n s x
  have hr : HomotopyLift (simplex P a)
      (Path.Homotopy.refl (binaryPath (k := 24) 7 8 24).symm)
      ((Homotopy.RelHomotopy.refl M.symm).postcomp (comparisonMap P a)) := by
    intro n r s x
    exact right_native P a n (unitInterval.symm s) x
  have hc := HomotopyLift.postcompHcomp (simplex P a) (comparisonMap P a)
    (HomotopyLift.postcompHcomp (simplex P a) (comparisonMap P a)
      hl (target_contraction_native P a)) hr
  have h := HomotopyLift.postcompTrans (simplex P a) (comparisonMap P a) hm hc
  exact HomotopyLift.postcompOfBoundary (simplex P a) (comparisonMap P a) h n r t x

end Quillen.PerfectComplexes.CoefficientPolynomialSpanUnitTop
