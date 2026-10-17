/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierAttachment
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSourceMiddleRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MTargetMiddleNodes
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation

/-!
# Original positive C0 polynomial and projection rails

Full polynomial reference transport yields the original native cylinder input without
cancelling the Laurent chart functor. Both complete projection rails are identified before
evaluation, including their shifted copies. No null/seed subdivision is changed here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC0CarrierRails
open BassH0Merge CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierAttachment
/-- Small abstract transport proof; the actual full geometric references are not unfolded. -/
private theorem anchor_post {V W T : Model.{v}}
    (F : V ⟶ W) (J : W ⟶ T) (G K : V ⟶ T)
    (θ : K.functor ≅ G.functor) (η : G.functor ≅ (F ≫ J).functor) (N : Node F) :
    anchorNode θ (BassH1Join.postReferenceNode G J η N) =
      attachPostcompNode F J K (θ ≪≫ η) N := by
  rcases N with ⟨H, ρ⟩
  unfold anchorNode BassH1Join.postReferenceNode attachPostcompNode
  change (⟨H ≫ J, θ ≪≫ (η ≪≫ isoWhiskerRight ρ J.functor)⟩ : Node K) =
    ⟨H ≫ J, (θ ≪≫ η) ≪≫ isoWhiskerRight ρ J.functor⟩
  exact congrArg (fun ν : K.functor ≅ (H ≫ J).functor ↦ (⟨H ≫ J, ν⟩ : Node K))
    (Iso.trans_assoc θ η (isoWhiskerRight ρ J.functor)).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The actual polynomial column is postcomposition with projection, reanchored before
any Laurent map is applied. -/
def polynomialCoefficientAnchor : (polynomialReference P p q).functor ≅
    (BassMComponents.coefficientSource P p q ≫ normalizedMap (polynomialProjection P c)).functor :=
  (BassMOuterJoin.movingSideBaseIso P p q).symm ≪≫
    BinaryNormalizationSimplex.total (polynomialProjection P c)
      (coefficientMap P q ≫ coefficientMap P p)

/-- All three full polynomial nodes, not their images under the Laurent chart. -/
theorem coefficientPolynomial_nodes (i : Fin 3) :
    coefficientPolynomialNodes P p q i =
      attachPostcompNode (BassMComponents.coefficientSource P p q)
        (normalizedMap (polynomialProjection P c)) (polynomialReference P p q)
        (polynomialCoefficientAnchor P p q) (BassMComponents.coefficientNodes P p q i) := by
  have hi : BassMJoin.movingSourceFace.toOrderHom i =
      DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  unfold coefficientPolynomialNodes transportPolynomialNode
  rw [hi, BassMJoin.polynomial_coefficient_column]
  exact anchor_post (BassMComponents.coefficientSource P p q)
    (normalizedMap (polynomialProjection P c)) (BassMComponents.polynomialSource P p q)
    (polynomialReference P p q) (BassMOuterJoin.movingSideBaseIso P p q).symm
    (BinaryNormalizationSimplex.total (polynomialProjection P c)
      (coefficientMap P q ≫ coefficientMap P p)) (BassMComponents.coefficientNodes P p q i)

/-- Every polynomial rail value is the original projection of the original coefficient track. -/
theorem coefficientPolynomial_family_native (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (polynomialReference P p q) (coefficientPolynomialNodes P p q) n
      (binaryPath (k := 2) 0 1 2 r, x) =
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c)).map n
      ((boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) := by
  rw [show coefficientPolynomialNodes P p q =
      (fun i ↦ attachPostcompNode (BassMComponents.coefficientSource P p q)
        (normalizedMap (polynomialProjection P c)) (polynomialReference P p q)
        (polynomialCoefficientAnchor P p q) (BassMComponents.coefficientNodes P p q i)) from
      funext (coefficientPolynomial_nodes P p q)]
  rw [prespectrumFamily_attachPostcomp, prespectrumFamily_eq, BassMComponents.coefficient_native]
  rfl

/-- The unchanged compact polynomial rail retains all native levels, including zero. -/
theorem coefficientPolynomialParameter_native (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (polynomialReference P p q) (coefficientPolynomialParameter P p q)
      n (r, x) =
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c)).map n
      ((boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) :=
  (compactPrespectrumFamily_eq_simplex _ _ (coefficientPolynomialNodes P p q) r
    (binaryPath (k := 2) 0 1 2 r) rfl n x).trans
      (coefficientPolynomial_family_native P p q n r x)

/-- The original H0 target projection row, keeping the original direct-arrow source transport. -/
def sourceProjectionNodes (i : Fin 3) : Node (laurentReference P p q) :=
  BassH0Merge.nodes P p q (BassH0Diagram.plusFace.toOrderHom
    (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)))

/-- The actual q-pre-p H1 target projection row in the common Laurent reference. -/
def targetProjectionNodes (i : Fin 3) : Node (laurentReference P p q) :=
  BassH1References.middleNodes P p q (BassH0Diagram.plusFace.toOrderHom
    (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)))

def sourceProjectionParameter : C(I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (parameter (laurentReference P p q) (sourceProjectionNodes P p q)).comp
    (binaryPath (k := 2) 0 1 2).toContinuousMap

def targetProjectionParameter : C(I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (parameter (laurentReference P p q) (targetProjectionNodes P p q)).comp
    (binaryPath (k := 2) 0 1 2).toContinuousMap

/-- The entire source projection rail, for every original path time s. -/
theorem projection_source_rail (s : I) :
    positiveProjectionParameter P p q (0, s) = sourceProjectionParameter P p q s := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 0,
      StdSimplex.map BassProjectionPath.plusFace.toOrderHom
        (binaryPath (k := 2) 0 1 2 s))) =
    parameter (laurentReference P p q) (sourceProjectionNodes P p q)
      (binaryPath (k := 2) 0 1 2 s)
  rw [Path.source, SimplexGrid.parameter_row, parameter_face, parameter_face]
  apply congrArg (fun N : Fin 3 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (binaryPath (k := 2) 0 1 2 s))
  funext i
  change BassMReferences.middleNodes P p q
    (SimplexGrid.index 2 4 (0, BassProjectionPath.plusFace.toOrderHom i)) = _
  have hi : BassProjectionPath.plusFace.toOrderHom i = Fin.castAdd 2 i := by
    fin_cases i <;> rfl
  rw [hi]
  exact BassMOuterJoin.source_middle_plus_nodes P p q i

/-- The entire target projection rail, not just its two endpoint values. -/
theorem projection_target_rail (s : I) :
    positiveProjectionParameter P p q (1, s) = targetProjectionParameter P p q s := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 1,
      StdSimplex.map BassProjectionPath.plusFace.toOrderHom
        (binaryPath (k := 2) 0 1 2 s))) =
    parameter (laurentReference P p q) (targetProjectionNodes P p q)
      (binaryPath (k := 2) 0 1 2 s)
  rw [Path.target, SimplexGrid.parameter_row, parameter_face, parameter_face]
  apply congrArg (fun N : Fin 3 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (binaryPath (k := 2) 0 1 2 s))
  funext i
  change BassMReferences.middleNodes P p q
    (SimplexGrid.index 2 4 (2, BassProjectionPath.plusFace.toOrderHom i)) = _
  have hi : BassProjectionPath.plusFace.toOrderHom i = Fin.castAdd 2 i := by
    fin_cases i <;> rfl
  rw [hi]
  exact (BassMOuterJoin.target_middle_plus_nodes P p q i).trans
    (BassMOuterJoin.h1_middle_plus_nodes P p q
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))).symm

/-- The shifted source rail keeps its complete unit-reference label. -/
theorem shifted_projection_source_rail (s : I) :
    shiftedProjectionParameter P p q (0, s) =
      mapParameter (anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q))
        (sourceProjectionParameter P p q s) :=
  congrArg (mapParameter (anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q)))
    (projection_source_rail P p q s)

/-- The shifted target rail keeps its separate full unit-reference label. -/
theorem shifted_projection_target_rail (s : I) :
    shiftedProjectionParameter P p q (1, s) =
      mapParameter (anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q))
        (targetProjectionParameter P p q s) :=
  congrArg (mapParameter (anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q)))
    (projection_target_rail P p q s)

/-- Reversing C0 interchanges the entire rails once, without reversing seed time s. -/
theorem reversed_projection_rails (s : I) :
    positiveProjectionParameter P p q (unitInterval.symm 0, s) = targetProjectionParameter P p q s ∧
    positiveProjectionParameter P p q (unitInterval.symm 1, s) =
      sourceProjectionParameter P p q s := by
  constructor
  · simpa using projection_target_rail P p q s
  · simpa using projection_source_rail P p q s

/-- First cylinder: independent coefficient time r and cone time t, original native formula. -/
theorem cylinderMinus_native (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (CutOpenCarrier.cylinderMinus (polynomialReference P p q) (chartMap P (c := c))
        (laurentReference P p q) (ordinaryAnchor P p q)
        (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
        (coefficientPolynomialParameter P p q r, t)) x =
    ReducedMappingCone.cylinder _ _ ((prespectrumMap (chartMap P (c := c))).map n)
      (t, (boundedFlatPerfectPrespectrumMap (polynomialProjection P c)).map n
        ((boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x))) := by
  rw [CutOpenCarrier.nativeEval_cylinderMinus,
    pointwisePrespectrumFamily_eq_compact _ (coefficientPolynomialParameter P p q),
    coefficientPolynomialParameter_native]

/-- Second cylinder: the same native formula, retaining its separate carrier tip. -/
theorem cylinderPlus_native (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (CutOpenCarrier.cylinderPlus (polynomialReference P p q) (chartMap P (c := c))
        (laurentReference P p q) (ordinaryAnchor P p q)
        (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
        (coefficientPolynomialParameter P p q r, t)) x =
    ReducedMappingCone.cylinder _ _ ((prespectrumMap (chartMap P (c := c))).map n)
      (t, (boundedFlatPerfectPrespectrumMap (polynomialProjection P c)).map n
        ((boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x))) := by
  rw [CutOpenCarrier.nativeEval_cylinderPlus,
    pointwisePrespectrumFamily_eq_compact _ (coefficientPolynomialParameter P p q),
    coefficientPolynomialParameter_native]

/-- The actual polynomial cylinder input preserves the specific p;q=l source cast. -/
theorem actualPolynomialParameter_native (a : Under R) (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily
      (polynomialReference P ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))
      (coefficientPolynomialParameter P
        ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a)) n (r, x) =
    (boundedFlatPerfectPrespectrumMap
      (polynomialProjection P ((laurentUnderFunctor R).obj a))).map n
      (((boundedFlatCoefficientCompositionHomotopy P
        ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a)).cast
          (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap (coefficientMap P k))
            (polynomialUnderCoefficient_toLaurent R a)) rfl).level n (r, x)) :=
  coefficientPolynomialParameter_native P
    ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a) n r x

/-- The original supportedRight cylinder input reverses C0 exactly once. -/
theorem actualPolynomialParameter_reversed_native (a : Under R) (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily
      (polynomialReference P ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))
      (coefficientPolynomialParameter P
        ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))
      n (unitInterval.symm r, x) =
    (boundedFlatPerfectPrespectrumMap
      (polynomialProjection P ((laurentUnderFunctor R).obj a))).map n
      (((boundedFlatCoefficientLaurentPlusHomotopy P a).symm).level n (r, x)) :=
  actualPolynomialParameter_native P a n (unitInterval.symm r) x

end Quillen.PerfectComplexes.CoefficientBassPositiveC0CarrierRails
