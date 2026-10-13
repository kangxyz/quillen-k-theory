/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Additivity.EndpointHomotopies
public import Quillen.Waldhausen.Additivity.RealizationHomotopy

/-! # Genuine realized additivity for cofibration sequences of exact functors

For a structural cofibration sequence `F → G → H`, the original map of
Waldhausen S-realizations induced by `G` is homotopic to that induced by
`H ⨿ F`. The proof uses actual pushout diagrams on the mixed ordinal cylinder,
their coherent endpoint isomorphisms, and the proved ordinary subdivision
realization equivalence. No additivity or fibration assertion is a hypothesis.

These are explicitly unbased homotopies. The chosen-zero track and the
resulting canonical based K-map equality require an additional argument.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v

namespace Quillen.Waldhausen.Additivity

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
variable {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
variable (hs : IsCofibrationSequence V W a b)

/-- Before cancelling ordinary subdivision, the original middle map is
homotopic to the actual common separated-sum endpoint. -/
theorem subdivided_middle_homotopic_sum :
    ((realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG)).comp
      (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))).Homotopic
      (realizedDiagonalMap (separatedSumMap V W hs.exactH hs.exactF)) := by
  have h₀ : (realizedDiagonalMap (identityDeformationMap V W a hs.exactF hs.exactG
    hs.cofibration)).Homotopic
      (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG)) :=
    ⟨realizationSimplicialHomotopy (identityEndpointHomotopy V W a hs.exactF hs.exactG
      hs.cofibration)⟩
  have h₁ : (realizedDiagonalMap (separatedDeformationMap V W a hs.exactF hs.exactG
    hs.cofibration)).Homotopic
      (realizedDiagonalMap (separatedSumMap V W hs.exactH hs.exactF)) :=
    ⟨realizationSimplicialHomotopy (separatedEndpointHomotopy V W a b hs)⟩
  have hm := mixed_deformation_endpoints (bisimplicialSSet V) (bisimplicialSSet W)
    (mixedDeformationMap V W a hs.exactF hs.exactG hs.cofibration)
  rw [mixedDeformationMap_zero, mixedDeformationMap_one] at hm
  exact (h₀.comp (ContinuousMap.Homotopic.refl _)).symm.trans (hm.trans h₁)

/-- The genuine additivity homotopy on the independent-grid model. -/
theorem bisimplicial_additivity :
    (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG)).Homotopic
      (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq
        (sumFunctor_isExact V W hs.exactH hs.exactF))) := by
  have h := (subdivided_middle_homotopic_sum V W a b hs).trans
    (subdivided_middle_homotopic_sum V W (sumInr H F) (sumProjection W H F)
      (splitIsCofibrationSequence V W hs.exactH hs.exactF)).symm
  exact homotopic_of_precomp_equivalence
    (OrdinalSubdivision.horizontalRealizationHomotopyEquiv (bisimplicialSSet V)) _ _ h

omit [HasBinaryCoproducts D] in
/-- The exact diagonal identification respects the original realized S-map. -/
theorem realizedDiagonalMap_exact_naturality {J : C ⥤ D}
    (hJ : IsExact V.cof V.weq W.cof W.weq J) :
    (SSet.toTop.map (bisimplicialDiagonalIso W).hom).hom.comp
        (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hJ)) =
      (deloopingMap hJ).hom.comp (SSet.toTop.map (bisimplicialDiagonalIso V).hom).hom := by
  have h := congrArg SSet.toTop.map (bisimplicialDiagonalIso_naturality V.cof V.weq hJ)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact congrArg TopCat.Hom.hom h

/-- Actual Waldhausen additivity for a genuine cofibration sequence of exact
functors, retaining the original `deloopingMap` at both endpoints. -/
theorem deloopingMap_additivity :
    (deloopingMap hs.exactG).hom.Homotopic
      (deloopingMap (sumFunctor_isExact V W hs.exactH hs.exactF)).hom := by
  have h := (ContinuousMap.Homotopic.refl
    (SSet.toTop.map (bisimplicialDiagonalIso W).hom).hom).comp
      (bisimplicial_additivity V W a b hs)
  rw [realizedDiagonalMap_exact_naturality V W hs.exactG,
    realizedDiagonalMap_exact_naturality V W (sumFunctor_isExact V W hs.exactH hs.exactF)] at h
  exact homotopic_of_precomp_equivalence
    (TopCat.homeoOfIso (SSet.toTop.mapIso (bisimplicialDiagonalIso V))).toHomotopyEquiv _ _ h

/-- A chosen actual continuous additivity homotopy. This construction does
not assert that its track at the chosen zero vertex is constant. -/
def additivityHomotopy :
    (deloopingMap hs.exactG).hom.Homotopy
      (deloopingMap (sumFunctor_isExact V W hs.exactH hs.exactF)).hom :=
  Classical.choice (deloopingMap_additivity V W a b hs)

end Quillen.Waldhausen.Additivity
