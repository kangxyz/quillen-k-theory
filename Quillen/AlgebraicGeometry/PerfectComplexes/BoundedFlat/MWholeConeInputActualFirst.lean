/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputFirst
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputCentral
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeReanchorNative

/-! The original first height half on the genuine coefficient identity-reference overlap. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputActual
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The input model is the genuine coefficient model. -/
abbrev model (a : Under R) := modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))

/-- The full node uses the actual model identity, with its identity reference. -/
def identityNode (a : Under R) : Node (𝟙 (model P a)) :=
  ⟨𝟙 (model P a), Iso.refl _⟩

/-- The identity node is realized as its actual zero simplex. -/
def identityParameter (a : Under R) : |parameterSSet (𝟙 (model P a))| :=
  CommonReferenceNerve.parameter (𝟙 (model P a))
    (fun _ : Fin 1 ↦ identityNode P a) (StdSimplex.single 0)

/-- Every arbitrary coefficient input is retained, also on its entire degree-zero loop. -/
theorem identityParameter_native (a : Under R) (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, a)))).space n) :
    pointwisePrespectrumFamily (𝟙 (model P a)) n (identityParameter P a) x = x := by
  let D : model P a ⟶ model P a := 𝟙 _
  let η : D.functor ⟶ D.functor := 𝟙 _
  have hη (A : model P a) : (model P a).waldhausen.weq (η.app A) :=
    (model P a).waldhausen.weq.id_mem _
  have h := prespectrumSimplexFamily_ofIsos_triangle D (fun _ : Fin 1 ↦ D)
    (fun _ ↦ Iso.refl _) (SimplexCategory.const ⦋2⦌ ⦋0⦌ 0) η η hη hη
    (by simp [η]) (by simp [η]) n 0 0 x
  have hz : StdSimplex.map (SimplexCategory.const ⦋2⦌ ⦋0⦌ 0).toOrderHom
      (Quillen.TheoremB.compositionTriangleHomotopy (0, 0)) =
      (StdSimplex.single 0 : StdSimplex ℝ (Fin 1)) := Subsingleton.elim _ _
  rw [hz] at h
  change pointwisePrespectrumFamily D n
    (CommonReferenceNerve.parameter D
      (fun _ : Fin 1 ↦ identityNode P a) (StdSimplex.single 0)) x = x
  rw [pointwisePrespectrumFamily_parameter, prespectrumFamily_eq]
  change prespectrumSimplexFamily
    (ModelSimplex.ofIsos D (fun _ : Fin 1 ↦ D) (fun _ ↦ Iso.refl _)) n
    (StdSimplex.single 0, x) = x
  rw [h]
  have hi : (prespectrumMap D).map n x = x :=
    congrArg (fun f : (prespectrum (model P a)).Hom (prespectrum (model P a)) ↦ f.map n x)
      (prespectrumFunctor.map_id (model P a))
  exact ((prespectrumTransformationCompositionHomotopy η η hη hη).level n).apply_zero
    (0, x) |>.trans ((prespectrumTransformationHomotopy (η ≫ η)
      (fun A ↦ (model P a).waldhausen.weq.comp_mem _ _ (hη A) (hη A))).at_zero n x
      |>.trans hi)

/-- The actual identity nerve point runs through the original four-quarter overlap. -/
def overlap (a : Under R) :
    C(I, FourEdgeTree.space (𝟙 (model P a)) (normalizedMap (polynomialProjection P a))) :=
  (FourEdgeTree.overlap (𝟙 (model P a)) (normalizedMap (polynomialProjection P a))).comp
    ⟨fun t ↦ (identityParameter P a, t), by fun_prop⟩

/-- Every original coefficient input is retained by the entire overlap. -/
theorem overlap_native (a : Under R) (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdgeTree.nativeEval (𝟙 (model P a)) (normalizedMap (polynomialProjection P a)) n
      (overlap P a t) x = input P (a := a) n t x := by
  change FourEdgeTree.nativeEval _ _ n
    (FourEdgeTree.overlap _ _ (identityParameter P a, t)) x = _
  rw [FourEdgeTree.nativeEval_overlap]
  dsimp only [FourEdgeTree.nativeCylinder]
  rw [identityParameter_native]
  rfl

variable {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "F" => TripleLaurent.input P p q w

/-- The actual identity composite is removed by its specified full unitor. -/
def removeIdentity :
    C(FourEdge.scalarCone P d (𝟙 (model P a) ≫ F), FourEdge.scalarCone P d F) :=
  FourEdge.Reanchor.cone P d (𝟙 (model P a) ≫ F) F
    (Functor.leftUnitor (F).functor).symm

/-- The first prescribed height half now has the same literal triple carrier as the second. -/
def first : C(I × (I × I), FourEdge.scalarCone P d F) :=
  (removeIdentity P p q w).comp ((InputLaurentProduct.first P p q w (𝟙 (model P a))).comp
    ⟨fun z ↦ (z.1, (overlap P a z.2.2, z.2.1)), by fun_prop⟩)

/-- The actual first half recovers K after B at every original coefficient input and degree. -/
theorem first_native_lower (n : ℕ) (r h t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P d F n (first P p q w (r, (h, t))) x =
      (BassMWhole.coneComposition P q w).level n
        (r, (boundedFlatCoefficientBassConeMap P p).map n
          (ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
            (Quillen.NativePathCells.lower h, input P (a := a) n t x))) := by
  dsimp only [first, removeIdentity, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [FourEdge.Reanchor.cone_native, InputLaurentProduct.first_native_lower, overlap_native]

/-- The whole old H0 target, including its full reference, is the retained midpoint datum. -/
theorem first_target (r t : I) :
    first P p q w (r, (1, t)) = removeIdentity P p q w
      (InputLaurentProduct.first P p q w (𝟙 (model P a)) (r, (overlap P a t, 1))) := rfl

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputActual
