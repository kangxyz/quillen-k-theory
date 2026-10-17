/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetChartAttachment
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionWholeReference
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.PolynomialLaurentNaturality

/-! Full reference transport for the actual target coefficient action. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetReferenceTransport
open BassH0Merge CommonReferenceNerve CoefficientBassSeedTargetChartAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)

/-- The exact scheme square, before any normalized pullback transport. -/
theorem projection_square :
    (laurentPlus P b ≫ polynomialProjection P b) ≫ coefficientMap P f =
      coefficientMap P ((laurentUnderFunctor R).map f) ≫
        (laurentPlus P a ≫ polynomialProjection P a) := by
  rw [laurentPlus_projection, laurentPlus_projection]
  exact (laurentProjection_naturality P f).symm

/-- Both original binary normalizations are retained in the target Laurent reference. -/
def projectionIso :
    (normalizedMap (coefficientMap P f) ≫ BassProjectionPath.source P b).functor ≅
      (BassProjectionPath.source P a ≫ L P f).functor :=
  (BinaryNormalizationSimplex.total
    (laurentPlus P b ≫ polynomialProjection P b) (coefficientMap P f)).symm ≪≫
  eqToIso (congrArg (fun g ↦ (normalizedMap g).functor) (projection_square P f)) ≪≫
  BinaryNormalizationSimplex.total
    (coefficientMap P ((laurentUnderFunctor R).map f))
    (laurentPlus P a ≫ polynomialProjection P a)

variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (τ : (BassProjectionPath.WholeReference.reference P a E).functor ≅ G.functor)

/-- The whole target coefficient reference, with its literal normalized coefficient action. -/
abbrev targetInput := E ≫ normalizedMap (coefficientMap P f)

/-- The postcomposed old Laurent reference enters the target whole-reference carrier. -/
def referenceIso :
    (BassProjectionPath.WholeReference.reference P b (targetInput P f E)).functor ≅
      (G ≫ L P f).functor :=
  Functor.associator E.functor (normalizedMap (coefficientMap P f)).functor
      (BassProjectionPath.source P b).functor ≪≫
    isoWhiskerLeft E.functor (projectionIso P f) ≪≫
    (Functor.associator E.functor (BassProjectionPath.source P a).functor
      (L P f).functor).symm ≪≫ isoWhiskerRight τ (L P f).functor

/-- Every postcomposed source node keeps its entire dependent reference. -/
def nodeMap : Node G → Node
    (BassProjectionPath.WholeReference.reference P b (targetInput P f E)) :=
  fun N ↦ CommonReferenceProduct.reanchor (referenceIso P f E G τ) (postcompNode (L P f) N)

/-- The same map on the whole Laurent realization. -/
def parameterMap := mapParameter (nodeMap P f E G τ)

/-- Its full node formula makes both original reference transports explicit. -/
theorem nodeMap_reference (N : Node G) :
    (nodeMap P f E G τ N).2 =
      referenceIso P f E G τ ≪≫ isoWhiskerRight N.2 (L P f).functor := rfl

variable (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
  (space (op P, (polynomialUnderFunctor R).obj a))))
  (ε : G.functor ≅ (D ≫ Ja P (a := a)).functor)

/-- The complete target sheet anchor in the shared whole Laurent reference. -/
def sheetReference :
    (BassProjectionPath.WholeReference.reference P b (targetInput P f E)).functor ≅
      ((D ≫ M P f) ≫ Jb P (b := b)).functor :=
  referenceIso P f E G τ ≪≫ targetAnchor P f D G ε

/-- The unit-shifted sheet retains its actual whiskered Laurent unit in the common reference. -/
theorem sheetReference_shifted (unitIso : G.functor ≅ G.functor) :
    sheetReference P f E G τ D (unitIso ≪≫ ε) =
      referenceIso P f E G τ ≪≫ isoWhiskerRight unitIso (L P f).functor ≪≫
        targetAnchor P f D G ε := by
  simp only [sheetReference, targetAnchor_shifted]

/-- Reanchoring the actual terminal chart node gives the complete target sheet attachment. -/
theorem terminal_node (N : Node D) :
    CommonReferenceProduct.reanchor (referenceIso P f E G τ)
        (movingNode P f D G ε N 4) =
      attachPostcompNode (D ≫ M P f) (Jb P (b := b))
        (BassProjectionPath.WholeReference.reference P b (targetInput P f E))
        (sheetReference P f E G τ D ε) (postcompNode (M P f) N) := by
  rw [movingNode_one]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact (Iso.trans_assoc _ _ _).symm

/-- Both whole terminal chart faces agree with their prescribed target sheet attachments. -/
theorem terminal_parameter (y : |CutOpenCarrier.parameterSSet D|) :
    mapParameter (CommonReferenceProduct.reanchor (referenceIso P f E G τ))
        (moving P f D G ε (y, 1)) =
      mapParameter
        (attachPostcompNode (D ≫ M P f) (Jb P (b := b))
          (BassProjectionPath.WholeReference.reference P b (targetInput P f E))
          (sheetReference P f E G τ D ε))
        (mapParameter (postcompNode (M P f)) y) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter D y
  rw [moving_one_attachment, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter _ ns z)
  funext i
  simpa only [movingNode_one] using terminal_node P f E G τ D ε (N i)

/-- The initial whole chart face is the actual postcomposed old attachment. -/
theorem initial_parameter (y : |CutOpenCarrier.parameterSSet D|) :
    mapParameter (CommonReferenceProduct.reanchor (referenceIso P f E G τ))
        (moving P f D G ε (y, 0)) =
      parameterMap P f E G τ
        (mapParameter (attachPostcompNode D (Ja P (a := a)) G ε) y) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter D y
  rw [moving_zero_attachment, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter]
  exact (mapParameter_parameter (nodeMap P f E G τ) _ z).symm

/-- The actual chart homotopy in the shared reference has both proved whole attachment faces. -/
def attachmentHomotopy :
    ((parameterMap P f E G τ).comp
      (mapParameter (attachPostcompNode D (Ja P (a := a)) G ε))).Homotopy
    ((mapParameter
      (attachPostcompNode (D ≫ M P f) (Jb P (b := b))
        (BassProjectionPath.WholeReference.reference P b (targetInput P f E))
        (sheetReference P f E G τ D ε))).comp
      (mapParameter (postcompNode (M P f)))) where
  toFun z := mapParameter (CommonReferenceProduct.reanchor (referenceIso P f E G τ))
    (moving P f D G ε (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left := initial_parameter P f E G τ D ε
  map_one_left := terminal_parameter P f E G τ D ε

end Quillen.PerfectComplexes.CoefficientBassSeedTargetReferenceTransport
