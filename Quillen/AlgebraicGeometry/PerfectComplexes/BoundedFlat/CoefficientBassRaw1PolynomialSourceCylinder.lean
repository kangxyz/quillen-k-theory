/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskered
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleLift

/-!
# The actual polynomial source cylinder

The source is the genuine polynomial model and its actual identity morphism. Its full
identity-reference zero simplex evaluates to each original polynomial input in every degree.
The resulting first-sheet cylinder retains the unchanged native cone height, including at
level zero. No representation of arbitrary polynomial input by base input is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialSourceCylinder
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The source is the actual polynomial coefficient model. -/
abbrev model (a : Under R) :=
  modelOf (boundedFlatPerfectWaldhausen (space (op P, (polynomialUnderFunctor R).obj a)))

/-- The full node uses the actual model identity, with its identity reference. -/
def identityNode (a : Under R) : Node (𝟙 (model P a)) :=
  ⟨𝟙 (model P a), Iso.refl _⟩

/-- The identity node is realized as its actual zero simplex. -/
def identityParameter (a : Under R) : |parameterSSet (𝟙 (model P a))| :=
  parameter (𝟙 (model P a)) (fun _ : Fin 1 ↦ identityNode P a) (StdSimplex.single 0)

/-- Every arbitrary polynomial input is retained, also on its entire degree-zero loop. -/
theorem identityParameter_native (a : Under R) (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
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
    (parameter D (fun _ : Fin 1 ↦ identityNode P a) (StdSimplex.single 0)) x = x
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

variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (a : Under R)

/-- The original chart model morphism at the unchanged source coefficient. -/
abbrev chart := BassMWholeNerve.coefficientModel P (β.app a)

/-- The source chart reference keeps the actual identity composite explicitly. -/
abbrev reference := (𝟙 (model P a)) ≫ chart P β a

/-- The actual first unreduced sheet of the polynomial source chart. -/
abbrev carrier :=
  |firstSimplicial (𝟙 (model P a)) (chart P β a) (reference P β a) (Iso.refl _)|

local notation "D" => (𝟙 (model P a))
local notation "J" => chart P β a
local notation "G" => reference P β a

/-- The literal first-sheet inclusion into the checked native evaluator. -/
def embed : C(carrier P β a, CutOpenCarrier.space D J G (Iso.refl _) (Iso.refl _)) :=
  (SSet.toTop.map (left₁ D J G (Iso.refl _) (Iso.refl _))).hom

/-- Native evaluation is the existing evaluator restricted to the actual first sheet. -/
def evaluate (n : ℕ) (z : carrier P β a) :=
  nativeEval D J G (Iso.refl _) (Iso.refl _) n (embed P β a z)

/-- The actual source cylinder uses the identity nerve point and the unchanged height. -/
def cylinder : C(I, carrier P β a) where
  toFun h := DoubleCylinder.realizedCylinder (attaching D J G (Iso.refl _)) (erase D)
    (identityParameter P a, ULift.up h)
  continuous_toFun :=
    (DoubleCylinder.realizedCylinder (attaching D J G (Iso.refl _)) (erase D)).hom.continuous.comp
      (by fun_prop)

/-- The source sheet retains its original unreduced terminal tip. -/
def tip : carrier P β a :=
  SSet.toTop.map (right₀ D J G (Iso.refl _)) (default : |tipSSet.{u+1}|)

/-- The source cylinder starts at its whole original chart attachment. -/
theorem cylinder_zero : cylinder P β a 0 =
    SSet.toTop.map (left₀ D J G (Iso.refl _))
      (SSet.toTop.map (attaching D J G (Iso.refl _)) (identityParameter P a)) := by
  have h := ConcreteCategory.congr_hom
    (DoubleCylinder.realized_isPushout (attaching D J G (Iso.refl _)) (erase D)).w
      (Sum.inl (identityParameter P a))
  exact h.trans (FourEdgeTree.SetDescent.eval_realized_left _ _ _).symm

/-- The unchanged terminal height is the original unreduced tip. -/
theorem cylinder_one : cylinder P β a 1 = tip P β a := by
  have h := ConcreteCategory.congr_hom
    (DoubleCylinder.realized_isPushout (attaching D J G (Iso.refl _)) (erase D)).w
      (Sum.inr (identityParameter P a))
  exact h.trans ((FourEdgeTree.SetDescent.eval_realized_right _ _ _).symm.trans
    (congrArg (SSet.toTop.map (right₀ D J G (Iso.refl _))) (Subsingleton.elim _ _)))

/-- All native inputs and all degrees retain exactly the original chart-cone cylinder. -/
theorem cylinder_native (n : ℕ) (h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    evaluate P β a n (cylinder P β a h) x =
      Quillen.ReducedMappingCone.cylinder _ _ ((prespectrumMap J).map n) (h, x) := by
  change nativeEval D J G (Iso.refl _) (Iso.refl _) n
    (cylinderMinus D J G (Iso.refl _) (Iso.refl _) (identityParameter P a, h)) x = _
  rw [nativeEval_cylinderMinus, identityParameter_native]

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialSourceCylinder
