/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.PointwiseCoproduct

/-!
# Pointwise coproducts and postcomposition

A coproduct-preserving functor gives the canonical comparison between the original pointwise coproduct functors.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
open Quillen.Waldhausen
namespace Quillen.PerfectComplexes.OpenFunctorNaturality
/-- Canonical postcomposition comparison for the original selected coproducts. -/
def coproductPostcomposeIso {C : Type v} [Category C] {D E : Type w} [Category D] [Category E]
    [HasBinaryCoproducts D] [HasBinaryCoproducts E] (H F : C ⥤ D) (J : D ⥤ E)
    [PreservesColimitsOfShape (Discrete WalkingPair) J] :
    Additivity.sumFunctor H F ⋙ J ≅ Additivity.sumFunctor (H ⋙ J) (F ⋙ J) :=
  (NatIso.ofComponents
    (fun K => asIso (coprodComparison J (H.obj K) (F.obj K)))
    (fun f => (coprodComparison_natural J (H.map f) (F.map f)).symm)).symm


end Quillen.PerfectComplexes.OpenFunctorNaturality
end
end
