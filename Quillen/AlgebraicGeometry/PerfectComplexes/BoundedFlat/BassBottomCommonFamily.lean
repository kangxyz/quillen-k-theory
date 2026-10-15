/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomSharedScalarPaths

/-! Three complete original Bass cylinder faces in one actual geometric reference family.
Repeated boundary slots are retained; their dependent-node identifications remain an obligation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassBottomCommonFamily
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Laurent naturality and the actual positive projection equation identify the bottom total. -/
theorem bottom_total :
    (BassLaurentBottomFace.firstMap P v ≫ BassLaurentBottomFace.secondMap P u) ≫
      (laurentPlus P a ≫ polynomialProjection P a) =
        laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  have hu := coefficientTransformation_naturality P (laurentUnderCoefficient R) u
  have hv := coefficientTransformation_naturality P (laurentUnderCoefficient R) v
  change BassLaurentBottomFace.secondMap P u ≫ laurentProjection P a =
    laurentProjection P b ≫ coefficientMap P u at hu
  change BassLaurentBottomFace.firstMap P v ≫ laurentProjection P b =
    laurentProjection P c ≫ coefficientMap P v at hv
  rw [laurentPlus_projection]
  simp only [Category.assoc]
  rw [hu, ← Category.assoc _ _ (coefficientMap P u), hv]
  simp only [Category.assoc]

/-- The bottom grid's reference uses the same actual total as both chart families. -/
def referenceIso : (BassOverlap.commonReference P u v).functor ≅
    (BassProjectionPath.source P a ≫ BassLaurentBottomFace.source P u v).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (bottom_total P u v).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (BassLaurentBottomFace.firstMap P v ≫ BassLaurentBottomFace.secondMap P u)
        (laurentPlus P a ≫ polynomialProjection P a)) AsSmall.up)

/-- The whole bottom diagram retains all product references after changing the common anchor. -/
def bottomNodes (i : Fin 15) : BassOverlap.Node P u v :=
  ⟨CommonReferenceProduct.vertices (fun j ↦ (BassProjectionPath.nodes P a j).1)
      (BassLaurentBottomFace.vertices P u v) i,
    referenceIso P u v ≪≫ CommonReferenceProduct.references
      (BassProjectionPath.source P a) (fun j ↦ (BassProjectionPath.nodes P a j).1)
      (fun j ↦ (BassProjectionPath.nodes P a j).2)
      (BassLaurentBottomFace.source P u v) (BassLaurentBottomFace.vertices P u v)
      (BassLaurentBottomFace.references P u v) i⟩

theorem bottom_reference : ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
    (fun i ↦ (bottomNodes P u v i).1) (fun i ↦ (bottomNodes P u v i).2) =
    BassLaurentBottomFace.simplex P u v :=
  ModelSimplex.ofIsos_change_reference (referenceIso P u v) _ _

/-- Keep the two charts and complete bottom diagram; no shared-boundary quotient is taken. -/
def nodes : Fin 51 → BassOverlap.Node P u v :=
  Fin.addCases (m := 36) (n := 15) (motive := fun _ ↦ BassOverlap.Node P u v)
    (BassOverlap.nodes P u v) (bottomNodes P u v)

def simplex : ModelSimplex
    (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))) 50 :=
  ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
    (fun i ↦ (nodes P u v i).1) (fun i ↦ (nodes P u v i).2)

def chartFace : ⦋35⦌ ⟶ ⦋50⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.castAdd 15, fun _ _ h ↦ h⟩

def bottomFace : ⦋14⦌ ⟶ ⦋50⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.natAdd 36, fun _ _ h ↦ Nat.add_le_add_left h 36⟩

theorem chart_face : (simplex P u v).face chartFace = BassOverlap.simplex P u v := by
  unfold simplex BassOverlap.simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ (BassOverlap.nodes P u v)
    (fun i ↦ by
      change nodes P u v (Fin.castAdd 15 i) = _
      unfold nodes
      rw [Fin.addCases_left])

theorem bottom_face : (simplex P u v).face bottomFace =
    BassLaurentBottomFace.simplex P u v := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ (bottomNodes P u v)
    (fun i ↦ by
      change nodes P u v (Fin.natAdd 36 i) = _
      unfold nodes
      rw [Fin.addCases_right])).trans (bottom_reference P u v)

/-- Whole positive original chart, now in the same actual family as the original bottom face. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map chartFace.toOrderHom (StdSimplex.map BassOverlap.plusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s))), x) =
      (boundedFlatCoefficientBassCompositionPlusChart P u v).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) := by
  rw [prespectrumSimplexFamily_face, chart_face]
  exact BassOverlap.plusChart_native P u v n r s x

/-- Whole inverse original chart in that same family. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map chartFace.toOrderHom (StdSimplex.map BassOverlap.minusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s))), x) =
      (boundedFlatCoefficientBassCompositionMinusChart P u v).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) := by
  rw [prespectrumSimplexFamily_face, chart_face]
  exact BassOverlap.minusChart_native P u v n r s x

/-- Whole prescribed bottom cylinder face in the same actual family as both fixed charts. -/
theorem bottom_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map bottomFace.toOrderHom (BassLaurentBottomFace.parameter.{u} (r, t)), x) =
      (Quillen.LoopPrespectrum.Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientLaurentCompositionHomotopy P u v)).level n
        (r, Quillen.LoopPrespectrum.HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rw [prespectrumSimplexFamily_face, bottom_face]
  exact BassLaurentBottomFace.native P u v n r t x

/-- Exact positive chart edge in the enlarged common scalar simplex. -/
theorem plus_edge_parameter (r : unitInterval) :
    StdSimplex.map chartFace.toOrderHom (StdSimplex.map BassOverlap.plusFace.toOrderHom
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0))) =
        Quillen.SimplexParameters.binaryPath (k := 50) 15 16 17 r := by
  rw [BassOverlap.plus_lower_parameter]
  exact Quillen.SimplexParameters.map_binaryPath chartFace 15 16 17 r

/-- Exact negative chart edge in the enlarged common scalar simplex. -/
theorem minus_edge_parameter (r : unitInterval) :
    StdSimplex.map chartFace.toOrderHom (StdSimplex.map BassOverlap.minusFace.toOrderHom
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0))) =
        Quillen.SimplexParameters.binaryPath (k := 50) 33 34 35 r := by
  rw [BassOverlap.minus_lower_parameter]
  exact Quillen.SimplexParameters.map_binaryPath chartFace 33 34 35 r

/-- Exact positive edge of the full bottom face, before identifying its shared dependent nodes. -/
theorem bottom_left_parameter (r : unitInterval) :
    StdSimplex.map bottomFace.toOrderHom (BassLaurentBottomFace.parameter.{u} (r, 0)) =
      Quillen.SimplexParameters.binaryPath (k := 50) 42 43 44 r := by
  rw [BassLaurentBottomFace.parameter_left]
  exact Quillen.SimplexParameters.map_binaryPath bottomFace 6 7 8 r

/-- Exact negative edge of the full bottom face, before identifying its shared dependent nodes. -/
theorem bottom_right_parameter (r : unitInterval) :
    StdSimplex.map bottomFace.toOrderHom (BassLaurentBottomFace.parameter.{u} (r, 1)) =
      Quillen.SimplexParameters.binaryPath (k := 50) 48 49 50 r := by
  rw [BassLaurentBottomFace.parameter_right]
  exact Quillen.SimplexParameters.map_binaryPath bottomFace 12 13 14 r

end Quillen.PerfectComplexes.BassBottomCommonFamily
