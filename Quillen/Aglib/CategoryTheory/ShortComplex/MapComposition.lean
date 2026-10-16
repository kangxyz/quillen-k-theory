/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Literal short-complex mapping and composition

The original short exactness of two successive maps is transported to the same composite functor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
theorem shortExact_map_comp_of
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    [HasZeroMorphisms C₀] [HasZeroMorphisms C₁] [HasZeroMorphisms C₂]
    (S : ShortComplex C₀) (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (h : ((S.map F).map G).ShortExact) : (S.map (F ⋙ G)).ShortExact := by
  simpa only [ShortComplex.map_comp] using h


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
end
end
