/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Realization.Cartesian.WeakDomains

/-! Regression consumers for actual two-coefficient finite-domain descent.
The target coefficient stays arbitrary, and conclusions concern original
constant-path comparisons in all degrees and for empty domains. -/
@[expose] public section


noncomputable section
open CategoryTheory Limits Opposite Quillen Quillen.CartesianRealization.Skeletal
open scoped Simplicial Topology unitInterval
universe u

variable {E T : TopCat.{u}} (q : E ⟶ T) {X Y : SSet.{u}} (r : X ⟶ Y) (K : SSet.{u})
  (s : (realizedOuterProductFunctor Y).obj K ⟶ T)
  (t : (realizedOuterProductFunctor X).obj K ⟶ E)
  (w : t ≫ q = coefficientDomainMap r K ≫ s)

-- The original comparison induces bijections in every degree, with no
-- weak-equivalence assumption on r and no specialization of Y to a point.
example (N : ℕ) [K.HasDimensionLT N]
    (h : coefficientDomainChartsWeakCartesian q r K s t w)
    (x : (realizedOuterProductFunctor X).obj K) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (HomotopyPullback.comparison q.hom s.hom (coefficientDomainMap r K).hom t.hom
        (congrArg TopCat.Hom.hom w)) (x := x) rfl) :=
  (finiteCoefficientDomain_weakCartesian q r K s t w N h).homotopy_bijective x n

-- Every finite-dimensional restriction uses its original two coefficient
-- maps; chart hypotheses are inherited through the actual domain map.
example {L : SSet.{u}} (f : L ⟶ K) (N : ℕ) [L.HasDimensionLT N]
    (h : coefficientDomainChartsWeakCartesian q r K s t w) :
    WeakCartesian (coefficientDomainMap r L).hom q.hom
      ((realizedOuterProductFunctor X).map f ≫ t).hom
      ((realizedOuterProductFunctor Y).map f ≫ s).hom
      (congrArg TopCat.Hom.hom (coefficientDomainMap_square q r K s t w f)) :=
  finiteCoefficientDomain_weakCartesian q r L _ _ _ N
    (coefficientDomainChartsWeakCartesian_map q r K s t w h f)

-- An actually empty parameter domain produces an actually empty pullback,
-- not only vacuous based group conditions.
example [K.HasDimensionLT 0] : IsEmpty (HomotopyPullback q.hom s.hom) :=
  (emptyCoefficientDomain_weakCartesian q r K s t w).isEmpty_target

example (x : (realizedOuterProductFunctor X).obj K) :
    let z := HomotopyPullback.comparison q.hom s.hom (coefficientDomainMap r K).hom t.hom
      (congrArg TopCat.Hom.hom w) x
    z.val.1 = coefficientDomainMap r K x ∧ z.val.2.1 = t x ∧
      ∀ u, z.val.2.2 u = s (coefficientDomainMap r K x) :=
  ⟨rfl,rfl,fun _ ↦ rfl⟩

-- The coefficient square keeps the original coefficient transformation
-- after an arbitrary change of the simplicial parameter.
example {L : SSet.{u}} (f : L ⟶ K) :
    (realizedOuterProductFunctor X).map f ≫ coefficientDomainMap r K =
      coefficientDomainMap r L ≫ (realizedOuterProductFunctor Y).map f :=
  coefficientDomainMap_naturality r f
