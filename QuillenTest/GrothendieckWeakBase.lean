/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.ClassifyingSpace.GrothendieckWeakBase
/-! Regression clients for original Grothendieck fiber inclusions. -/
noncomputable section
open CategoryTheory Quillen
universe u v w t z
example {C : Type u} [Category.{v} C] (F : C ⥤ Cat.{w, t}) (c : C) :
    GrothendieckForget.commaTransport F c ⊣ GrothendieckForget.commaEntry F c :=
  GrothendieckForget.commaTransportAdjunction F c
example {C : Type u} [Category.{v} C] (F : C ⥤ Cat.{w, t}) (c : C) :
    GrothendieckForget.commaEntry F c ⋙ CostructuredArrow.proj (Grothendieck.forget F) c =
      Grothendieck.ι F c := rfl
example {C : Type u} [Category.{v} C] (F : C ⥤ Cat.{w, t})
    (e : ∀ {c d : C} (_ : c ⟶ d),
      ContinuousMap.HomotopyEquiv (ClassifyingSpace (F.obj c)) (ClassifyingSpace (F.obj d)))
    (he : ∀ {c d : C} (f : c ⟶ d),
      (e f).toFun = classifyingSpaceMapUniversal (F.map f).toFunctor)
    (hC : IsWeakHomotopyEquivalence
      (ContinuousMap.const (ClassifyingSpace C) (PUnit.unit : PUnit.{z + 1}))) (c : C) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (Grothendieck.ι F c)) :=
  GrothendieckForget.fiberInclusion_isWeakHomotopyEquivalence F e he hC c
