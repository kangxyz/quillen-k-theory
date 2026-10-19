/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanParameterNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationUnit
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCompactFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-!
# The actual two-tip mixed evaluation seed carrier

The eight-node projection square and original mixed Laurent total supply the polynomial and
Laurent references. The ordinary attachment is the previously proved full positive-chart
anchor. The second attachment retains the actual strict forward Laurent unit. The entire
projection square attaches on both sheets before evaluation; no polynomial unit is required.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u v₁ v₂ v₃ u₁ u₂ u₃
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedCarrier
open GlobalSectionChangeIndex CommonReferenceNerve

private theorem preserved_onFunctor {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (A : C ⥤ D) (B : D ⥤ E) (α : 𝟭 D ≅ 𝟭 D) (β : 𝟭 E ≅ 𝟭 E)
    (h : Preserves B α β) :
    isoWhiskerRight (onFunctor A α) B = onFunctor (A ⋙ B) β := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  exact h (A.obj x)

private theorem central_anchor {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (A B : C ⥤ D) (ρ : A ≅ B) (β : 𝟭 D ≅ 𝟭 D) :
    onFunctor A β ≪≫ ρ = ρ ≪≫ onFunctor B β := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  exact (β.hom.naturality (ρ.hom.app x)).symm

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original eight-node projection-square reference, before positive chart attachment. -/
abbrev polyRef := InputSpanParameterNodes.projectionSource g

/-- The unchanged normalized positive chart, with its actual zero-preserving Model map. -/
abbrev chart := evaluationRawMap (plus.app X)

/-- The original strict total Laurent pullback followed by evaluation. -/
abbrev laurentRef := InputMixedDesc.sourceMap g

/-- The actual full positive-chart reference isomorphism from the original mixed construction. -/
def ordinary : (laurentRef g).functor ≅ (polyRef g ≫ chart (X := X)).functor :=
  InputSpanParameterNodes.sourceIso g plus GlobalRawBass.plus_projection

/-- The original strict forward Laurent unit on the actual mixed total reference. -/
def commonUnit : (laurentRef g).functor ≅ (laurentRef g).functor :=
  isoWhiskerRight
    (onFunctor
      (globalModel.map (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y).op).functor
      (GlobalSchemeLaurentTrack.unit (op X)))
    (evaluationModel (op (laurent.obj X))).functor

/-- This actual identity action is transported by the already proved original evaluation. -/
theorem commonUnit_eq_target : commonUnit g =
    onFunctor (laurentRef g).functor
      (evaluationSmallUnit (op (laurent.obj X)) (GlobalSchemeLaurentTrack.laurentScalar (op X))) :=
  preserved_onFunctor
    (globalModel.map (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y).op).functor
    (evaluationModel (op (laurent.obj X))).functor
    (GlobalSchemeLaurentTrack.unit (op X)) _
    (evaluationModel_unit (op (laurent.obj X)) (GlobalSchemeLaurentTrack.laurentScalar (op X)))

/-- Every full reference anchor intertwines the original strict Laurent unit as an isomorphism. -/
theorem anchor_unit (N : Node (laurentRef g)) :
    commonUnit g ≪≫ N.2 = N.2 ≪≫ onFunctor N.1.functor
      (evaluationSmallUnit (op (laurent.obj X))
        (GlobalSchemeLaurentTrack.laurentScalar (op X))) := by
  rw [commonUnit_eq_target]
  exact central_anchor _ _ N.2 _

/-- The shifted attachment retains the original unit before the full ordinary anchor. -/
def shifted : (laurentRef g).functor ≅ (polyRef g ≫ chart (X := X)).functor :=
  commonUnit g ≪≫ ordinary g

/-- The full ordinary attachment also intertwines the original target Laurent action. -/
theorem ordinary_unit :
    shifted g = ordinary g ≪≫ onFunctor (polyRef g ≫ chart (X := X)).functor
      (evaluationSmallUnit (op (laurent.obj X)) (GlobalSchemeLaurentTrack.laurentScalar (op X))) :=
  anchor_unit g ⟨polyRef g ≫ chart (X := X), ordinary g⟩

/-- The actual two-tip carrier keeps the two polynomial endpoints distinct. -/
abbrev Carrier := CutOpenCarrier.space (polyRef g) (chart (X := X)) (laurentRef g)
  (ordinary g) (shifted g)

/-- The entire original projection square in its own full-node nerve. -/
def projectionParameter : C(I × I, |nerve (Codiscrete (Node (polyRef g)))|) :=
  (parameter (polyRef g) (InputSpanParameterNodes.projectionNodes g)).comp
    InputCommutingParameter.parameter

/-- The whole original projection square has precisely its proved ordinary chart attachment. -/
theorem projection_attach (z : I × I) :
    InputSpanParameterNodes.parameter g plus GlobalRawBass.plus_projection z =
      mapParameter (attachPostcompNode (polyRef g) (chart (X := X))
        (laurentRef g) (ordinary g)) (projectionParameter g z) := by
  change parameter (laurentRef g) _ (InputCommutingParameter.parameter z) =
    mapParameter _ (parameter (polyRef g) _ (InputCommutingParameter.parameter z))
  rw [mapParameter_parameter]
  rfl

/-- Every shifted polynomial node keeps its actual Model arrow and complete unit anchor. -/
theorem shifted_node (N : Node (polyRef g)) :
    CommonReferenceProduct.reanchor (commonUnit g)
      (attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g) N) =
    attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (shifted g) N := by
  apply congrArg (fun a => (⟨N.1 ≫ chart (X := X), a⟩ : Node (laurentRef g)))
  exact (Iso.trans_assoc _ _ _).symm

/-- Both times of the original projection square survive its separate unit-shifted attachment. -/
theorem shifted_projection_attach (z : I × I) :
    mapParameter (CommonReferenceProduct.reanchor (commonUnit g))
      (InputSpanParameterNodes.parameter g plus GlobalRawBass.plus_projection z) =
    mapParameter (attachPostcompNode (polyRef g) (chart (X := X))
      (laurentRef g) (shifted g)) (projectionParameter g z) := by
  rw [projection_attach]
  exact reanchor_attach_parameter (polyRef g) (chart (X := X)) (laurentRef g)
    (commonUnit g) (ordinary g) (projectionParameter g z)

/-- Distinct scalar tips remain distinct despite their common native cone-basepoint value. -/
theorem tips_distinct :
    CutOpenCarrier.tipMinus (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) ≠
      CutOpenCarrier.tipPlus (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) :=
  CutOpenCarrier.tips_ne _ _ _ _ _

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedCarrier
