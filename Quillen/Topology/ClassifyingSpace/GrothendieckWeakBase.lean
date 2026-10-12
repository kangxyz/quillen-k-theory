/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.Grothendieck.ForgetComma
public import Quillen.Topology.ClassifyingSpace.UniverseHomotopy
public import Quillen.Topology.HomotopyEquiv.HomotopySquare
public import Quillen.CategoryTheory.TheoremB.UniverseWeakComparison

/-! # Original Grothendieck fiber inclusions over weakly contractible bases -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w t z
namespace Quillen.GrothendieckForget
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] (F : C ⥤ Cat.{w, t})

/-- The original fiber-to-comma entry has the inverse supplied by its actual adjunction. -/
def commaEntryClassifyingHomotopyEquiv (c : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (F.obj c))
      (ClassifyingSpace (CostructuredArrow (Grothendieck.forget F) c)) :=
  (adjunctionClassifyingHomotopyEquivUniversal (commaTransportAdjunction F c)).symm

/-- The original comma transition square commutes through its cocartesian natural transformation. -/
def commaEntryTransitionHomotopy {c d : C} (f : c ⟶ d) :
    ((classifyingSpaceMapUniversal (CostructuredArrow.map
      (S := Grothendieck.forget F) f)).comp
        (classifyingSpaceMapUniversal (commaEntry F c))).Homotopy
      ((classifyingSpaceMapUniversal (commaEntry F d)).comp
        (classifyingSpaceMapUniversal (F.map f).toFunctor)) :=
  (classifyingSpaceUniversalHomotopy (commaEntryTransition F f)).cast
    (classifyingSpaceMapUniversal_comp _ _) (classifyingSpaceMapUniversal_comp _ _)

/-- Original transition homotopy equivalences imply the actual projection's Theorem B condition. -/
theorem forget_transitionWeakEquivalences
    (e : ∀ {c d : C} (_ : c ⟶ d),
      ContinuousMap.HomotopyEquiv (ClassifyingSpace (F.obj c)) (ClassifyingSpace (F.obj d)))
    (he : ∀ {c d : C} (f : c ⟶ d),
      (e f).toFun = classifyingSpaceMapUniversal (F.map f).toFunctor) :
    TheoremB.TransitionWeakEquivalencesUniversal (Grothendieck.forget F) := by
  intro c d f
  let h := ContinuousMap.HomotopyEquiv.ofHomotopySquare
    (commaEntryClassifyingHomotopyEquiv F c)
    (commaEntryClassifyingHomotopyEquiv F d) (e f)
    (classifyingSpaceMapUniversal (CostructuredArrow.map (S := Grothendieck.forget F) f))
    (by
      change ((classifyingSpaceMapUniversal (CostructuredArrow.map
        (S := Grothendieck.forget F) f)).comp
          (classifyingSpaceMapUniversal (commaEntry F c))).Homotopic
        ((classifyingSpaceMapUniversal (commaEntry F d)).comp (e f).toFun)
      rw [he]
      exact ⟨commaEntryTransitionHomotopy F f⟩)
  exact isWeakHomotopyEquivalence_of_homotopyEquiv h

/-- Every original fiber inclusion is a weak equivalence over an actual weakly contractible base. -/
theorem fiberInclusion_isWeakHomotopyEquivalence
    (e : ∀ {c d : C} (_ : c ⟶ d),
      ContinuousMap.HomotopyEquiv (ClassifyingSpace (F.obj c)) (ClassifyingSpace (F.obj d)))
    (he : ∀ {c d : C} (f : c ⟶ d),
      (e f).toFun = classifyingSpaceMapUniversal (F.map f).toFunctor)
    (hC : IsWeakHomotopyEquivalence
      (ContinuousMap.const (ClassifyingSpace C) (PUnit.unit : PUnit.{z + 1}))) (c : C) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (Grothendieck.ι F c)) := by
  have hp := TheoremB.commaProjectionUniversal_isWeakHomotopyEquivalence_of_weakBase
    (Grothendieck.forget F) (forget_transitionWeakEquivalences F e he) c hC
  have hi := isWeakHomotopyEquivalence_of_homotopyEquiv (commaEntryClassifyingHomotopyEquiv F c)
  change IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (commaEntry F c)) at hi
  have h := hp.comp hi
  rw [← classifyingSpaceMapUniversal_comp, commaEntry_projection] at h
  exact h

end Quillen.GrothendieckForget
