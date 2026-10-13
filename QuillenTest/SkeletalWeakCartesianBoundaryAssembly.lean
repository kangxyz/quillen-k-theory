/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.TheoremB.SkeletalWeakCartesianBoundaryAssembly

/-!
# Arbitrary-coefficient incoming boundary regression consumers

The coefficient map need not be weak: independent product geometry already
makes the boundary-to-cell comparison genuinely Cartesian. The assembled
weak statement uses arbitrary two coefficient diagrams, with the original
boundary point and full constant path retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
open Quillen Quillen.CartesianRealization.Skeletal
universe u

example {X Y K L : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace K] [TopologicalSpace L]
    (r : C(X,Y)) (k : C(K,L)) :
    Cartesian (r.prodMap (ContinuousMap.id K)) (r.prodMap (ContinuousMap.id L))
      ((ContinuousMap.id X).prodMap k) ((ContinuousMap.id Y).prodMap k) rfl :=
  coefficientProduct_cartesian r k

example {K L X Y : SSet.{u}} [LocallyCompactSpace |K|] [LocallyCompactSpace |L|]
    (k : K ⟶ L) (r : X ⟶ Y) :
    Cartesian (realizationFunctor.map (TheoremA.outerProductCoefficientMap (K := K) r)).hom
      (realizationFunctor.map (TheoremA.outerProductCoefficientMap (K := L) r)).hom
      (realizationFunctor.map (TheoremA.outerProductMap (X := X) k)).hom
      (realizationFunctor.map (TheoremA.outerProductMap (X := Y) k)).hom
      (congrArg TopCat.Hom.hom (coefficientOuter_square k r)) :=
  coefficientOuter_cartesian k r

example {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J) (n : ℕ) :
    WeakCartesian (cellBoundaryProjection η n).hom (cellProjection η n).hom
      (boundaryLeg H n).hom (boundaryLeg J n).hom
      (congrArg TopCat.Hom.hom (cellBoundarySquare η n)) :=
  replacementBoundary_weakCartesian η n

example {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J) (n : ℕ)
    (z : (realizationFunctor.obj (TheoremA.replacementCellBoundaries H n))) :
    (HomotopyPullback.comparison (cellProjection η n).hom (boundaryLeg J n).hom
      (cellBoundaryProjection η n).hom (boundaryLeg H n).hom
      (congrArg TopCat.Hom.hom (cellBoundarySquare η n)) z).val =
      (cellBoundaryProjection η n z,boundaryLeg H n z,
        ContinuousMap.const unitInterval (boundaryLeg J n (cellBoundaryProjection η n z))) := rfl
