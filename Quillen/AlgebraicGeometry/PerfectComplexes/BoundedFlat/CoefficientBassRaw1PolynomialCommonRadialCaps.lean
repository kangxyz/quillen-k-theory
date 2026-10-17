/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialRadialLowerFaces

/-!
# Original radial caps in the fixed common polynomial sheet

The first, middle, and last pairs of corrected radial caps retain their whole original
polynomial references under the existing common-sheet maps. Complete Laurent18 nodes
identify their six lower paths with the source total, first intermediate, middle total,
and target total paths used by the three original radial squares. Both cap clocks and
all source-chart transports remain explicit.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonRadialCaps
open CommonReferenceNerve
open BassH0Merge (normalizedMap)
open CoefficientBassRaw1PolynomialTripleAnchor CoefficientBassRaw1PolynomialTripleLowerFaces


private theorem transport_node {U V W : Model.{u}} (A : U ⟶ V)
    {F G : V ⟶ W} {K T : U ⟶ W}
    (ε : (A ≫ F).functor ≅ K.functor) (ρ : F.functor ≅ G.functor)
    (η : (A ≫ G).functor ≅ T.functor) (N : Node G) :
    CommonReferenceProduct.reanchor
      (ε.symm ≪≫ isoWhiskerLeft A.functor ρ ≪≫ η)
      (CommonReferenceProduct.reanchor η.symm (precompNode A N)) =
    CommonReferenceProduct.reanchor ε.symm
      (precompNode A (CommonReferenceProduct.reanchor ρ N)) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [CommonReferenceProduct.reanchor, precompNode, Iso.trans_assoc,
    Iso.self_symm_id_assoc, isoWhiskerLeft_trans]

private theorem reanchor_refl_node {V W : Model.{u}} {F : V ⟶ W} (N : Node F) :
    CommonReferenceProduct.reanchor (Iso.refl F.functor) N = N := by
  rcases N with ⟨K, ρ⟩
  exact congrArg (fun e ↦ (⟨K, e⟩ : Node F)) (Iso.refl_trans ρ)

private theorem parameter_row {V W : Model.{u}} {F : V ⟶ W}
    (N : Fin 8 → Node F) (M : Fin 18 → Node F) (face : ⦋7⦌ ⟶ ⦋17⦌)
    (h : ∀ i, N i = M (face.toOrderHom i)) (ι : ⦋2⦌ ⟶ ⦋7⦌)
    (x : StdSimplex ℝ (Fin 3)) :
    parameter F (fun i ↦ N (ι.toOrderHom i)) x =
      parameter F M (StdSimplex.map (ι ≫ face).toOrderHom x) := by
  rw [parameter_face]
  exact congrArg (fun K ↦ parameter F K x) (funext (fun i ↦ h (ι.toOrderHom i)))

private theorem parameter_mapped_row {V₀ W₀ V₁ W₁ : Model.{u}}
    {F : V₀ ⟶ W₀} {G : V₁ ⟶ W₁} (g : Node F → Node G)
    (N : Fin 8 → Node F) (M : Fin 18 → Node G) (face : ⦋7⦌ ⟶ ⦋17⦌)
    (h : ∀ i, g (N i) = M (face.toOrderHom i)) (ι : ⦋2⦌ ⟶ ⦋7⦌)
    (x : StdSimplex ℝ (Fin 3)) :
    mapParameter g (parameter F (fun i ↦ N (ι.toOrderHom i)) x) =
      parameter G M (StdSimplex.map (ι ≫ face).toOrderHom x) := by
  rw [mapParameter_parameter, parameter_face]
  exact congrArg (fun K ↦ parameter G K x) (funext (fun i ↦ h (ι.toOrderHom i)))

private theorem binary_value_congr {k : ℕ} {a b c a' b' c' : Fin (k + 1)}
    (ha : a = a') (hb : b = b') (hc : c = c') (r : I) :
    binaryPath a b c r = binaryPath a' b' c' r := by
  subst a'
  subst b'
  subst c'
  rfl

private theorem first_left_scalar (r : I) :
    StdSimplex.map ((SplitTripleSimplex.triangleFace 0 1 2 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.firstFace).toOrderHom (binaryPath (k := 2) 0 1 2 r) =
    DoubleSquareScalarPaths.sourceTotal r := by
  let F : Fin 3 → Fin 18 :=
    ((SplitTripleSimplex.triangleFace 0 1 2 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.firstFace).toOrderHom
  have h₀ : F 0 = 0 := rfl
  have h₁ : F 1 = 1 := rfl
  have h₂ : F 2 = 2 := rfl
  exact (BassSupportOrder.map_any_binary (k := 2) (l := 17) F 0 1 2 r).trans
    (binary_value_congr h₀ h₁ h₂ r)

private theorem first_right_scalar (r : I) :
    StdSimplex.map ((SplitTripleSimplex.triangleFace 0 4 5 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.firstFace).toOrderHom (binaryPath (k := 2) 0 1 2 r) =
    DoubleSquareScalarPaths.firstIntermediate r := by
  let F : Fin 3 → Fin 18 :=
    ((SplitTripleSimplex.triangleFace 0 4 5 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.firstFace).toOrderHom
  have h₀ : F 0 = 0 := rfl
  have h₁ : F 1 = 8 := rfl
  have h₂ : F 2 = 9 := rfl
  exact (BassSupportOrder.map_any_binary (k := 2) (l := 17) F 0 1 2 r).trans
    (binary_value_congr h₀ h₁ h₂ r)

private theorem middle_left_scalar (r : I) :
    StdSimplex.map ((SplitTripleSimplex.triangleFace 0 1 2 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.middleFace).toOrderHom (binaryPath (k := 2) 0 1 2 r) =
    DoubleSquareScalarPaths.middleTotal r := by
  let F : Fin 3 → Fin 18 :=
    ((SplitTripleSimplex.triangleFace 0 1 2 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.middleFace).toOrderHom
  have h₀ : F 0 = 0 := rfl
  have h₁ : F 1 = 4 := rfl
  have h₂ : F 2 = 5 := rfl
  exact (BassSupportOrder.map_any_binary (k := 2) (l := 17) F 0 1 2 r).trans
    (binary_value_congr h₀ h₁ h₂ r)

private theorem middle_right_scalar (r : I) :
    StdSimplex.map ((SplitTripleSimplex.triangleFace 0 4 5 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.middleFace).toOrderHom (binaryPath (k := 2) 0 1 2 r) =
    DoubleSquareScalarPaths.firstIntermediate r := by
  let F : Fin 3 → Fin 18 :=
    ((SplitTripleSimplex.triangleFace 0 4 5 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.middleFace).toOrderHom
  have h₀ : F 0 = 0 := rfl
  have h₁ : F 1 = 8 := rfl
  have h₂ : F 2 = 9 := rfl
  exact (BassSupportOrder.map_any_binary (k := 2) (l := 17) F 0 1 2 r).trans
    (binary_value_congr h₀ h₁ h₂ r)

private theorem last_left_scalar (r : I) :
    StdSimplex.map ((SplitTripleSimplex.triangleFace 0 1 2 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.lastFace).toOrderHom (binaryPath (k := 2) 0 1 2 r) =
    DoubleSquareScalarPaths.middleTotal r := by
  let F : Fin 3 → Fin 18 :=
    ((SplitTripleSimplex.triangleFace 0 1 2 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.lastFace).toOrderHom
  have h₀ : F 0 = 0 := rfl
  have h₁ : F 1 = 4 := rfl
  have h₂ : F 2 = 5 := rfl
  exact (BassSupportOrder.map_any_binary (k := 2) (l := 17) F 0 1 2 r).trans
    (binary_value_congr h₀ h₁ h₂ r)

private theorem last_right_scalar (r : I) :
    StdSimplex.map ((SplitTripleSimplex.triangleFace 0 4 5 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.lastFace).toOrderHom (binaryPath (k := 2) 0 1 2 r) =
    DoubleSquareScalarPaths.targetTotal r := by
  let F : Fin 3 → Fin 18 :=
    ((SplitTripleSimplex.triangleFace 0 4 5 (by decide) (by decide)) ≫
      DoubleSquareMergedSimplex.lastFace).toOrderHom
  have h₀ : F 0 = 0 := rfl
  have h₁ : F 1 = 14 := rfl
  have h₂ : F 2 = 15 := rfl
  exact (BassSupportOrder.map_any_binary (k := 2) (l := 17) F 0 1 2 r).trans
    (binary_value_congr h₀ h₁ h₂ r)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- The original first left radial cap in the one common polynomial sheet. -/
def firstLeft : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f) :=
  CoefficientBassRaw1PolynomialRadialCaps.left P β ((polynomialUnderCoefficient R).app a) (α.app
    a) ((laurentUnderFunctor R).map f)

/-- The original first right radial cap in the one common polynomial sheet. -/
def firstRight : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f) :=
  CoefficientBassRaw1PolynomialRadialCaps.right P β ((polynomialUnderCoefficient R).app a) (α.app
    a) ((laurentUnderFunctor R).map f)

/-- Every original first triple node has its full common polynomial reference. -/
theorem first_triple_nodes (i : Fin 8) :
    CommonReferenceProduct.reanchor (referenceIso P β ((polynomialUnderCoefficient R).app a)
      (α.app a) ((laurentUnderFunctor R).map f)).symm
        (precompNode (normalizedMap (chart P β a)) (tripleNodes P ((polynomialUnderCoefficient
          R).app a) (α.app a) ((laurentUnderFunctor R).map f) i)) =
    nodes P α β f (DoubleSquareMergedSimplex.firstFace.toOrderHom i) := by
  have h : CommonReferenceProduct.reanchor (firstTransport P α β f)
      (CommonReferenceProduct.reanchor (referenceIso P β
        ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor R).map f)).symm
        (precompNode (normalizedMap (chart P β a))
          (tripleNodes P ((polynomialUnderCoefficient R).app a) (α.app a)
            ((laurentUnderFunctor R).map f) i))) =
      nodes P α β f (DoubleSquareMergedSimplex.firstFace.toOrderHom i) := by
    dsimp only [firstTransport, nodes, CoefficientBassRaw1LaurentChartRestriction.nodes]
    rw [first_nodes]
    exact transport_node (normalizedMap (chart P β a))
      (CoefficientBassRaw1PolynomialReference.referenceIso P α β f) (Iso.refl _)
      (referenceIso P β ((polynomialUnderCoefficient R).app a) (α.app a)
        ((laurentUnderFunctor R).map f)) _
  rw [first_transport] at h
  exact (reanchor_refl_node _).symm.trans h

/-- The entire first radial parameter is retained under its literal polynomial anchor. -/
theorem first_parameter (ι : ⦋2⦌ ⟶ ⦋7⦌) (x : StdSimplex ℝ (Fin 3)) :
    parameter (polynomialReference P ((polynomialUnderCoefficient R).app a) (α.app a)
      ((laurentUnderFunctor R).map f) ≫
          normalizedMap (chart P β ((laurentUnderFunctor R).obj b)))
        (fun i ↦ CommonReferenceProduct.reanchor (referenceIso P β ((polynomialUnderCoefficient
          R).app a) (α.app a) ((laurentUnderFunctor R).map f)).symm
          (precompNode (normalizedMap (chart P β a))
            (tripleNodes P ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor
              R).map f) (ι.toOrderHom i)))) x =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (ι ≫ DoubleSquareMergedSimplex.firstFace).toOrderHom x) := by
  exact parameter_row
    (fun i ↦ CommonReferenceProduct.reanchor (referenceIso P β ((polynomialUnderCoefficient R).app
      a) (α.app a) ((laurentUnderFunctor R).map f)).symm
      (precompNode (normalizedMap (chart P β a)) (tripleNodes P ((polynomialUnderCoefficient
        R).app a) (α.app a) ((laurentUnderFunctor R).map f) i)))
    (nodes P α β f) DoubleSquareMergedSimplex.firstFace
    (first_triple_nodes P α β f) ι x

/-- The original middle left radial cap in the one common polynomial sheet. -/
def middleLeft : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f) :=
  (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f).comp
    (CoefficientBassRaw1PolynomialRadialCaps.left P β ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b))

/-- The original middle right radial cap in the one common polynomial sheet. -/
def middleRight : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f) :=
  (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f).comp
    (CoefficientBassRaw1PolynomialRadialCaps.right P β ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b))

/-- Every original middle triple node has its full common polynomial reference. -/
theorem middle_triple_nodes (i : Fin 8) :
    CommonReferenceProduct.reanchor (middleTransport P α β f)
      (CommonReferenceProduct.reanchor (referenceIso P β ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f) (α.app b)).symm
        (precompNode (normalizedMap (chart P β a)) (tripleNodes P ((polynomialUnderCoefficient
          R).app a) ((polynomialUnderFunctor R).map f) (α.app b) i))) =
    nodes P α β f (DoubleSquareMergedSimplex.middleFace.toOrderHom i) := by
  dsimp only [middleTransport, nodes, CoefficientBassRaw1LaurentChartRestriction.nodes]
  rw [middle_nodes]
  exact transport_node (normalizedMap (chart P β a))
    (CoefficientBassRaw1PolynomialReference.referenceIso P α β f)
    (middleAnchor P α f) (referenceIso P β ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b)) _

/-- The entire middle radial parameter is retained under its literal polynomial anchor. -/
theorem middle_parameter (ι : ⦋2⦌ ⟶ ⦋7⦌) (x : StdSimplex ℝ (Fin 3)) :
    mapParameter (CommonReferenceProduct.reanchor (middleTransport P α β f))
      (parameter (polynomialReference P ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f) (α.app b) ≫
          normalizedMap (chart P β ((laurentUnderFunctor R).obj b)))
        (fun i ↦ CommonReferenceProduct.reanchor (referenceIso P β ((polynomialUnderCoefficient
          R).app a) ((polynomialUnderFunctor R).map f) (α.app b)).symm
          (precompNode (normalizedMap (chart P β a))
            (tripleNodes P ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map
              f) (α.app b) (ι.toOrderHom i)))) x) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (ι ≫ DoubleSquareMergedSimplex.middleFace).toOrderHom x) := by
  exact parameter_mapped_row (CommonReferenceProduct.reanchor (middleTransport P α β f))
    (fun i ↦ CommonReferenceProduct.reanchor (referenceIso P β ((polynomialUnderCoefficient R).app
      a) ((polynomialUnderFunctor R).map f) (α.app b)).symm
      (precompNode (normalizedMap (chart P β a)) (tripleNodes P ((polynomialUnderCoefficient
        R).app a) ((polynomialUnderFunctor R).map f) (α.app b) i)))
    (nodes P α β f) DoubleSquareMergedSimplex.middleFace
    (middle_triple_nodes P α β f) ι x

/-- The original last left radial cap in the one common polynomial sheet. -/
def lastLeft : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f) :=
  (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f).comp
    (CoefficientBassRaw1PolynomialRadialCaps.left P β f ((polynomialUnderCoefficient R).app b)
      (α.app b))

/-- The original last right radial cap in the one common polynomial sheet. -/
def lastRight : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f) :=
  (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f).comp
    (CoefficientBassRaw1PolynomialRadialCaps.right P β f ((polynomialUnderCoefficient R).app b)
      (α.app b))

/-- Every original last triple node has its full common polynomial reference. -/
theorem last_triple_nodes (i : Fin 8) :
    CommonReferenceProduct.reanchor (lastTransport P α β f)
      (CommonReferenceProduct.reanchor (referenceIso P β f ((polynomialUnderCoefficient R).app b)
        (α.app b)).symm
        (precompNode (normalizedMap (chart P β a)) (tripleNodes P f ((polynomialUnderCoefficient
          R).app b) (α.app b) i))) =
    nodes P α β f (DoubleSquareMergedSimplex.lastFace.toOrderHom i) := by
  dsimp only [lastTransport, nodes, CoefficientBassRaw1LaurentChartRestriction.nodes]
  rw [last_nodes]
  exact transport_node (normalizedMap (chart P β a))
    (CoefficientBassRaw1PolynomialReference.referenceIso P α β f)
    (lastAnchor P α f) (referenceIso P β f ((polynomialUnderCoefficient R).app b) (α.app b)) _

/-- The entire last radial parameter is retained under its literal polynomial anchor. -/
theorem last_parameter (ι : ⦋2⦌ ⟶ ⦋7⦌) (x : StdSimplex ℝ (Fin 3)) :
    mapParameter (CommonReferenceProduct.reanchor (lastTransport P α β f))
      (parameter (polynomialReference P f ((polynomialUnderCoefficient R).app b) (α.app b) ≫
          normalizedMap (chart P β ((laurentUnderFunctor R).obj b)))
        (fun i ↦ CommonReferenceProduct.reanchor (referenceIso P β f ((polynomialUnderCoefficient
          R).app b) (α.app b)).symm
          (precompNode (normalizedMap (chart P β a))
            (tripleNodes P f ((polynomialUnderCoefficient R).app b) (α.app b) (ι.toOrderHom i))))
              x) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (ι ≫ DoubleSquareMergedSimplex.lastFace).toOrderHom x) := by
  exact parameter_mapped_row (CommonReferenceProduct.reanchor (lastTransport P α β f))
    (fun i ↦ CommonReferenceProduct.reanchor (referenceIso P β f ((polynomialUnderCoefficient
      R).app b) (α.app b)).symm
      (precompNode (normalizedMap (chart P β a)) (tripleNodes P f ((polynomialUnderCoefficient
        R).app b) (α.app b) i)))
    (nodes P α β f) DoubleSquareMergedSimplex.lastFace
    (last_triple_nodes P α β f) ι x

/-- The original firstLeft cap has exactly the prescribed sourceTotal lower path. -/
theorem first_left_lower (r : I) :
    firstLeft P α β f (r, 0) =
      CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
        (parameter (targetReference P α β f) (nodes P α β f)
          (DoubleSquareScalarPaths.sourceTotal r)) := by
  change CoefficientBassRaw1PolynomialRadialCaps.left P β ((polynomialUnderCoefficient R).app a)
    (α.app a) ((laurentUnderFunctor R).map f) (r, 0) = _
  rw [CoefficientBassRaw1PolynomialRadialCaps.left_lower]
  exact congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f)
    ((first_parameter P α β f (SplitTripleSimplex.triangleFace 0 1 2 (by decide) (by decide))
    (binaryPath (k := 2) 0 1 2 r)).trans (congrArg (parameter (targetReference P α β f) (nodes P α
      β f))
      (first_left_scalar r)))

/-- The original firstRight cap has exactly the prescribed firstIntermediate lower path. -/
theorem first_right_lower (r : I) :
    firstRight P α β f (r, 0) =
      CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
        (parameter (targetReference P α β f) (nodes P α β f)
          (DoubleSquareScalarPaths.firstIntermediate r)) := by
  change CoefficientBassRaw1PolynomialRadialCaps.right P β ((polynomialUnderCoefficient R).app a)
    (α.app a) ((laurentUnderFunctor R).map f) (r, 0) = _
  rw [CoefficientBassRaw1PolynomialRadialCaps.right_lower]
  exact congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f)
    ((first_parameter P α β f (SplitTripleSimplex.triangleFace 0 4 5 (by decide) (by decide))
    (binaryPath (k := 2) 0 1 2 r)).trans (congrArg (parameter (targetReference P α β f) (nodes P α
      β f))
      (first_right_scalar r)))

/-- The original middleLeft cap has exactly the prescribed middleTotal lower path. -/
theorem middle_left_lower (r : I) :
    middleLeft P α β f (r, 0) =
      CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
        (parameter (targetReference P α β f) (nodes P α β f)
          (DoubleSquareScalarPaths.middleTotal r)) := by
  change CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f
    (CoefficientBassRaw1PolynomialRadialCaps.left P β ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b) (r, 0)) = _
  rw [CoefficientBassRaw1PolynomialRadialCaps.left_lower,
    CoefficientBassRaw1PolynomialCapLowerFaces.middleMap_laurent]
  exact congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f)
    ((middle_parameter P α β f (SplitTripleSimplex.triangleFace 0 1 2 (by decide) (by decide))
    (binaryPath (k := 2) 0 1 2 r)).trans (congrArg (parameter (targetReference P α β f) (nodes P α
      β f))
      (middle_left_scalar r)))

/-- The original middleRight cap has exactly the prescribed firstIntermediate lower path. -/
theorem middle_right_lower (r : I) :
    middleRight P α β f (r, 0) =
      CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
        (parameter (targetReference P α β f) (nodes P α β f)
          (DoubleSquareScalarPaths.firstIntermediate r)) := by
  change CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f
    (CoefficientBassRaw1PolynomialRadialCaps.right P β ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b) (r, 0)) = _
  rw [CoefficientBassRaw1PolynomialRadialCaps.right_lower,
    CoefficientBassRaw1PolynomialCapLowerFaces.middleMap_laurent]
  exact congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f)
    ((middle_parameter P α β f (SplitTripleSimplex.triangleFace 0 4 5 (by decide) (by decide))
    (binaryPath (k := 2) 0 1 2 r)).trans (congrArg (parameter (targetReference P α β f) (nodes P α
      β f))
      (middle_right_scalar r)))

/-- The original lastLeft cap has exactly the prescribed middleTotal lower path. -/
theorem last_left_lower (r : I) :
    lastLeft P α β f (r, 0) =
      CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
        (parameter (targetReference P α β f) (nodes P α β f)
          (DoubleSquareScalarPaths.middleTotal r)) := by
  change CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f
    (CoefficientBassRaw1PolynomialRadialCaps.left P β f ((polynomialUnderCoefficient R).app b)
      (α.app b) (r, 0)) = _
  rw [CoefficientBassRaw1PolynomialRadialCaps.left_lower,
    CoefficientBassRaw1PolynomialCapLowerFaces.lastMap_laurent]
  exact congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f)
    ((last_parameter P α β f (SplitTripleSimplex.triangleFace 0 1 2 (by decide) (by decide))
    (binaryPath (k := 2) 0 1 2 r)).trans (congrArg (parameter (targetReference P α β f) (nodes P α
      β f))
      (last_left_scalar r)))

/-- The original lastRight cap has exactly the prescribed targetTotal lower path. -/
theorem last_right_lower (r : I) :
    lastRight P α β f (r, 0) =
      CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
        (parameter (targetReference P α β f) (nodes P α β f)
          (DoubleSquareScalarPaths.targetTotal r)) := by
  change CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f
    (CoefficientBassRaw1PolynomialRadialCaps.right P β f ((polynomialUnderCoefficient R).app b)
      (α.app b) (r, 0)) = _
  rw [CoefficientBassRaw1PolynomialRadialCaps.right_lower,
    CoefficientBassRaw1PolynomialCapLowerFaces.lastMap_laurent]
  exact congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f)
    ((last_parameter P α β f (SplitTripleSimplex.triangleFace 0 4 5 (by decide) (by decide))
    (binaryPath (k := 2) 0 1 2 r)).trans (congrArg (parameter (targetReference P α β f) (nodes P α
      β f))
      (last_right_scalar r)))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonRadialCaps
