/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.ChangeWeakMixedHomotopy
public import Quillen.Waldhausen.Additivity.SplitSequence

/-! # Original mixed-grid, chosen-zero and parameter consumers -/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen.Waldhausen.Additivity Quillen.MixedOrdinalCylinder
open scoped Simplicial Topology
universe u v
namespace QuillenTest.ChangeWeakMixedHomotopy

open Quillen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (N : Fibration.NestedWeakEquivalences W)
  {F G : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)

/-- Every mixed cut retains exactly the original grid. -/
theorem original_grid {n m : SimplexCategory} (φ : Cut n)
    (A : Grid₂ (mixedOrdinal φ) m ⥤ C) :
    normalizedMixedGrid V W a hF hG hc φ A =
      normalizedMixedGrid V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc) φ A :=
  normalizedMixedGrid_changeWeak V W N a hF hG hc φ A

/-- The target normalization still uses the original coarse chosen zero. -/
theorem original_zero :
    (normalizedPushoutFunctor V W a hF hG hc).obj (Arrow.mk (𝟙 V.zero)) = N.coarse.zero :=
  (normalizedPushoutFunctor_obj_zero V W a hF hG hc).trans N.zero_eq.symm

/-- The deformation parameter is independent of any path parameter in the source realization. -/
theorem original_two_parameters
    {x y : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|}
    (p : Path x y) (s t : unitInterval) :
    SSet.toTop.map (TheoremA.diagonalMap
      (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
        (realizationSimplicialHomotopy
          (normalizedMixedEndpointHomotopy V W a hF hG hc) (s, p t)) =
      realizationSimplicialHomotopy
        (normalizedMixedEndpointHomotopy V N.coarse a
          (hF.comp (Fibration.changeWeak_exact N))
          (hG.comp (Fibration.changeWeak_exact N))
          (isCofibrationTransformation_changeWeak V W N a hc)) (s, p t) :=
  normalizedMixedRealizationHomotopy_changeWeak V W N a hF hG hc s (p t)

/-- The actual split sequence supplies its cofibration condition without a filler hypothesis. -/
theorem original_split_sequence [HasBinaryCoproducts D] {H : C ⥤ D}
    (hH : IsExact V.cof V.weq W.cof W.weq H)
    (s : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    SSet.toTop.map (TheoremA.diagonalMap
      (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
        (realizationSimplicialHomotopy
          (normalizedMixedEndpointHomotopy V W (sumInr H F) hF
            (sumFunctor_isExact V W hH hF)
            (splitIsCofibrationSequence V W hH hF).cofibration) (s, x)) =
      realizationSimplicialHomotopy
        (normalizedMixedEndpointHomotopy V N.coarse (sumInr H F)
          (hF.comp (Fibration.changeWeak_exact N))
          ((sumFunctor_isExact V W hH hF).comp (Fibration.changeWeak_exact N))
          (isCofibrationTransformation_changeWeak V W N (sumInr H F)
            (splitIsCofibrationSequence V W hH hF).cofibration)) (s, x) :=
  normalizedMixedRealizationHomotopy_changeWeak V W N (sumInr H F) hF
    (sumFunctor_isExact V W hH hF) (splitIsCofibrationSequence V W hH hF).cofibration s x

end QuillenTest.ChangeWeakMixedHomotopy
