/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationInputRoutes
public import Quillen.Aglib.CategoryTheory.Functor.EqToHomApplicationTransport

/-! # Original pair-arrow equality transport under genuine support inclusion

The independently formed geometric square and the original strict section transport retain
their ambient components under the actual full-subcategory inclusion. These are categorical
morphism identities before normalization or realization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation
  evaluationPullbackIso supportedPairReindexEvaluationIso

/-- Equality of original pair arrows keeps its actual geometric transport under inclusion. -/
theorem supportedPullbackEquality_forget_hom_app {E F : Scheme.OpenPairs.{u}}
    {r s : E ⟶ F} (e : r = s)
    (L : (boundedFlatPerfectSupported F.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget E.obj.hom).map
        ((eqToHom (congrArg boundedFlatPerfectSupportedPullback e)).app L) =
      (eqToHom (congrArg (fun k : E ⟶ F => boundedFlatPerfectPullback k.hom.right) e)).app
        ((tensorCoefficientSupportedForget F.obj.hom).obj L) := by
  subst s
  exact (tensorCoefficientSupportedForget E.obj.hom).map_id
    ((boundedFlatPerfectSupportedPullback r).obj L)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
