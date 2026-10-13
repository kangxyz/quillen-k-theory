/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.TheoremB.Comparison
public import Quillen.Topology.ClassifyingSpace.Equivalence
public import Quillen.Topology.HomotopyFiber.SourceEquivalence
public import Mathlib.CategoryTheory.Adjunction.Comma

/-!
# Quillen's Theorem B for left adjoints

If `F` has a right adjoint, each comma category `(F ↓ d)` has a terminal
object. Its classifying space is therefore contractible. The actual map
`|N F|` is a homotopy equivalence, so its path-space homotopy fiber is also
contractible. Consequently the canonical comma-to-fiber comparison itself
is a homotopy equivalence.

This proves a genuine special case with the prescribed comparison as the
forward map. It neither assumes the conclusion nor proves general Theorem B.
-/
@[expose] public section


noncomputable section

open CategoryTheory
open scoped Topology

universe u v

namespace Quillen

/-- All continuous maps into a contractible space are homotopic. -/
theorem homotopic_of_contractible_target {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace Y]
    (f g : C(X, Y)) : f.Homotopic g := by
  obtain ⟨y, h⟩ := id_nullhomotopic Y
  have hf : f.Homotopic (ContinuousMap.const X y) :=
    h.comp (ContinuousMap.Homotopic.refl f)
  have hg : g.Homotopic (ContinuousMap.const X y) :=
    h.comp (ContinuousMap.Homotopic.refl g)
  exact hf.trans hg.symm

/-- Every continuous map between contractible spaces has a homotopy inverse,
with exactly the specified continuous map as its forward map. -/
def homotopyEquivOfContractible {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] [ContractibleSpace Y] (f : C(X, Y)) :
    ContinuousMap.HomotopyEquiv X Y :=
  HomotopyFiber.replaceForward (Classical.choice (ContractibleSpace.hequiv X Y)) f
    (homotopic_of_contractible_target _ _)

@[simp]
theorem homotopyEquivOfContractible_toFun {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] [ContractibleSpace Y] (f : C(X, Y)) :
    (homotopyEquivOfContractible f).toFun = f := rfl

namespace TheoremB

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F : C ⥤ D} {G : D ⥤ C}

/-- The counit object is terminal in the comma category of a left adjoint,
so the actual realization of that comma category is contractible. -/
theorem comma_contractible_of_adjunction (a : F ⊣ G) (d : D) :
    ContractibleSpace (ClassifyingSpace (CostructuredArrow F d)) :=
  classifyingSpace_contractible_of_isTerminal (mkTerminalOfRightAdjoint G a d)

/-- The actual path-space homotopy fiber of the realized left adjoint is
contractible, because the unit and counit realize to inverse homotopies. -/
theorem homotopyFiber_contractible_of_adjunction (a : F ⊣ G) (d : D) :
    ContractibleSpace (HomotopyFiber (classifyingSpaceMap F).hom
      (classifyingSpacePoint d)) :=
  HomotopyFiber.contractibleSpace_homotopyEquiv
    (adjunctionClassifyingHomotopyEquiv a) (classifyingSpacePoint d)

/-- Quillen's canonical Theorem B comparison is a homotopy equivalence
whenever the functor has a right adjoint. The forward map is exactly the
comparison built from the structure-arrow nullhomotopy. -/
def fiberComparisonHomotopyEquivOfAdjunction (a : F ⊣ G) (d : D) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (CostructuredArrow F d))
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) := by
  letI := comma_contractible_of_adjunction a d
  letI := homotopyFiber_contractible_of_adjunction a d
  exact homotopyEquivOfContractible (fiberComparison F d)

@[simp]
theorem fiberComparisonHomotopyEquivOfAdjunction_toFun (a : F ⊣ G) (d : D) :
    (fiberComparisonHomotopyEquivOfAdjunction a d).toFun = fiberComparison F d := rfl

@[simp]
theorem fiberComparisonHomotopyEquivOfAdjunction_apply (a : F ⊣ G) (d : D)
    (x : ClassifyingSpace (CostructuredArrow F d)) :
    fiberComparisonHomotopyEquivOfAdjunction a d x = fiberComparison F d x := rfl

/-- Left adjoints also satisfy Theorem B's hypothesis: each prescribed
postcomposition map of comma classifying spaces is a homotopy equivalence. -/
theorem transitionHomotopyEquivalences_of_adjunction (a : F ⊣ G) :
    TransitionHomotopyEquivalences F := by
  intro d e f
  let := comma_contractible_of_adjunction a d
  let := comma_contractible_of_adjunction a e
  let h := homotopyEquivOfContractible (transitionMap F f)
  exact ⟨h.invFun, h.left_inv, h.right_inv⟩

/-- Instance-based form of the left-adjoint special case of Theorem B. -/
def fiberComparisonHomotopyEquivOfIsLeftAdjoint (F : C ⥤ D) [F.IsLeftAdjoint]
    (d : D) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (CostructuredArrow F d))
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  fiberComparisonHomotopyEquivOfAdjunction (Adjunction.ofIsLeftAdjoint F) d

@[simp]
theorem fiberComparisonHomotopyEquivOfIsLeftAdjoint_toFun (F : C ⥤ D)
    [F.IsLeftAdjoint] (d : D) :
    (fiberComparisonHomotopyEquivOfIsLeftAdjoint F d).toFun = fiberComparison F d := rfl

/-- In particular the canonical comparison for the identity functor is a
homotopy equivalence onto the actual homotopy fiber of its realization. -/
def fiberComparisonHomotopyEquivId (d : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (CostructuredArrow (𝟭 C) d))
      (HomotopyFiber (classifyingSpaceMap (𝟭 C)).hom (classifyingSpacePoint d)) :=
  fiberComparisonHomotopyEquivOfAdjunction (Adjunction.id) d

@[simp]
theorem fiberComparisonHomotopyEquivId_toFun (d : C) :
    (fiberComparisonHomotopyEquivId d).toFun = fiberComparison (𝟭 C) d := rfl

end TheoremB
end Quillen
