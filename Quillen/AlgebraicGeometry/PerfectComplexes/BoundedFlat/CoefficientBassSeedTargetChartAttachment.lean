/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareFiveSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteParameter
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCarrier

/-! The original five-node positive chart square over every full source polynomial node. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetChartAttachment
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
private theorem terminal_node {V W T U : Model.{u}}
    (D : V ⟶ W) (G : V ⟶ T) (M : W ⟶ U) (J : U ⟶ T) (H : W ⟶ T)
    (δ : G.functor ≅ (D ≫ H).functor) (θ : H.functor ≅ (M ≫ J).functor)
    (N : Node D) :
    (⟨N.1 ≫ (M ≫ J), δ ≪≫ isoWhiskerLeft D.functor θ ≪≫
      isoWhiskerRight N.2 (M ≫ J).functor⟩ : Node G) =
    attachPostcompNode (D ≫ M) J G
      (δ ≪≫ isoWhiskerLeft D.functor θ ≪≫
        (Functor.associator D.functor M.functor J.functor).symm)
      (postcompNode M N) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp [attachPostcompNode, postcompNode, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]; rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (polynomialUnderFunctor R).obj a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))

/-- The normalized model map induced by the Laurent image of `f`. -/
abbrev L := BassH0Merge.normalizedMap (coefficientMap P ((laurentUnderFunctor R).map f))
/-- The normalized model map induced by the polynomial image of `f`. -/
abbrev M := BassH0Merge.normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map f))
/-- The normalized positive-chart map at the source coefficient object `a`. -/
abbrev Ja := BassH0Merge.normalizedMap (laurentPlus P a)
/-- The normalized positive-chart map at the target coefficient object `b`. -/
abbrev Jb := BassH0Merge.normalizedMap (laurentPlus P b)
/-- The square reference for the Laurent coefficient map and the source positive chart. -/
abbrev H := NativeSquareFiveSimplex.source
  (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentPlus P a)
/-- The normalization isomorphism for the left composite of the positive-chart coefficient
square. -/
abbrev leftIso := BinaryNormalizationSimplex.total
  (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentPlus P a)
/-- The reference isomorphism through the square to the normalized right composite. -/
abbrev rightIso := NativeSquareFiveSimplex.sourceIso
  (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentPlus P a)
  (laurentPlus P b) (coefficientMap P ((polynomialUnderFunctor R).map f))
  (coefficientMap_naturality P (underToLaurent R) f) ≪≫
  BinaryNormalizationSimplex.total (laurentPlus P b)
    (coefficientMap P ((polynomialUnderFunctor R).map f))

variable (ε : G.functor ≅ (D ≫ Ja P (a := a)).functor)

/-- The original source attachment is transported to the complete square reference. -/
def squareAnchor : (G ≫ L P f).functor ≅ (D ≫ H P f).functor :=
  isoWhiskerRight ε (L P f).functor ≪≫
    Functor.associator D.functor (Ja P (a := a)).functor (L P f).functor ≪≫
    isoWhiskerLeft D.functor (leftIso P f).symm

/-- The target attachment includes the exact geometric-square normalization transport. -/
def targetAnchor : (G ≫ L P f).functor ≅ ((D ≫ M P f) ≫ Jb P (b := b)).functor :=
  squareAnchor P f D G ε ≪≫ isoWhiskerLeft D.functor (rightIso P f) ≪≫
    (Functor.associator D.functor (M P f).functor (Jb P (b := b)).functor).symm

/-- Shifting retains the full right-whiskered unit action, rather than a polynomial unit lift. -/
theorem targetAnchor_shifted (τ : G.functor ≅ G.functor) :
    targetAnchor P f D G (τ ≪≫ ε) =
      isoWhiskerRight τ (L P f).functor ≪≫ targetAnchor P f D G ε := by
  simp only [targetAnchor, squareAnchor, isoWhiskerRight_trans, Iso.trans_assoc]

/-- Every source node and every original square vertex keep their full dependent references. -/
def movingNode (N : Node D) (i : Fin 5) : Node (G ≫ L P f) :=
  let Z := NativeSquareFiveSimplex.nodes
    (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentPlus P a)
    (laurentPlus P b) (coefficientMap P ((polynomialUnderFunctor R).map f))
    (coefficientMap_naturality P (underToLaurent R) f) i
  ⟨N.1 ≫ Z.1, squareAnchor P f D G ε ≪≫
    isoWhiskerLeft D.functor Z.2 ≪≫ isoWhiskerRight N.2 Z.1.functor⟩

/-- The initial full node is the original attachment followed by the Laurent action. -/
theorem movingNode_zero (N : Node D) :
    movingNode P f D G ε N 2 =
      postcompNode (L P f) (attachPostcompNode D (Ja P (a := a)) G ε N) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp [movingNode, NativeSquareFiveSimplex.nodes, squareAnchor,
    attachPostcompNode, postcompNode, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]; rfl

/-- The last full node is the target polynomial attachment with its exact transported anchor. -/
theorem movingNode_one (N : Node D) :
    movingNode P f D G ε N 4 =
      attachPostcompNode (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
        (targetAnchor P f D G ε) (postcompNode (M P f) N) := by
  exact terminal_node D (G ≫ L P f) (M P f) (Jb P (b := b)) (H P f)
    (squareAnchor P f D G ε) (rightIso P f) N

/-- The complete original reversed-binary then binary clock remains in the Laurent nerve. -/
def moving : C(|parameterSSet D| × I, |parameterSSet (G ≫ L P f)|) :=
  (FiniteParameter.parameter D (G ≫ L P f) (movingNode P f D G ε)).comp
    ⟨fun z ↦ (z.1, NativeSquareFiveSimplex.parameter z.2), by fun_prop⟩

/-- The first whole face is recorded without discarding any source-node reference. -/
theorem moving_zero (y : |parameterSSet D|) :
    moving P f D G ε (y, 0) = mapParameter (fun N ↦ movingNode P f D G ε N 2) y := by
  change FiniteParameter.parameter D (G ≫ L P f) (movingNode P f D G ε)
    (y, NativeSquareFiveSimplex.parameter 0) = _
  rw [Path.source]
  exact FiniteParameter.parameter_vertex _ _ _ _ _

/-- The last whole face retains the separately ordered target chart node. -/
theorem moving_one (y : |parameterSSet D|) :
    moving P f D G ε (y, 1) = mapParameter (fun N ↦ movingNode P f D G ε N 4) y := by
  change FiniteParameter.parameter D (G ≫ L P f) (movingNode P f D G ε)
    (y, NativeSquareFiveSimplex.parameter 1) = _
  rw [Path.target]
  exact FiniteParameter.parameter_vertex _ _ _ _ _

/-- The first attachment face agrees on every point of the source polynomial nerve. -/
theorem moving_zero_attachment (y : |parameterSSet D|) :
    moving P f D G ε (y, 0) =
      mapParameter (fun N ↦ postcompNode (L P f)
        (attachPostcompNode D (Ja P (a := a)) G ε N)) y := by
  rw [moving_zero]
  exact congrArg (fun h ↦ mapParameter h y) (funext (movingNode_zero P f D G ε))

/-- The terminal attachment face retains the full transported target reference. -/
theorem moving_one_attachment (y : |parameterSSet D|) :
    moving P f D G ε (y, 1) =
      mapParameter (fun N ↦ attachPostcompNode (D ≫ M P f) (Jb P (b := b))
        (G ≫ L P f) (targetAnchor P f D G ε) (postcompNode (M P f) N)) y := by
  rw [moving_one]
  exact congrArg (fun h ↦ mapParameter h y) (funext (movingNode_one P f D G ε))

/-- The original chart square is a whole-nerve attachment homotopy with its literal clock. -/
def attachmentHomotopy :
    (mapParameter (fun N ↦ postcompNode (L P f)
      (attachPostcompNode D (Ja P (a := a)) G ε N))).Homotopy
    (mapParameter (fun N ↦ attachPostcompNode (D ≫ M P f) (Jb P (b := b))
      (G ≫ L P f) (targetAnchor P f D G ε) (postcompNode (M P f) N))) where
  toFun z := moving P f D G ε (z.2, z.1)
  continuous_toFun := (moving P f D G ε).continuous.comp (by fun_prop)
  map_zero_left := moving_zero_attachment P f D G ε
  map_one_left := moving_one_attachment P f D G ε

end Quillen.PerfectComplexes.CoefficientBassSeedTargetChartAttachment
