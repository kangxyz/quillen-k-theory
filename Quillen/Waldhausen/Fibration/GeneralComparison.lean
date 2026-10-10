/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.SmallModel.Fiber
public import Quillen.Waldhausen.SmallModel.Joint
public import Quillen.Waldhausen.Fibration.GlobalComparison

/-! # The original global fibration with distinct category universes

The exact common-universe model transports both structural cylinder data and
the actual canonical fiber comparison, including its full nullhomotopy path.
The result concerns the unchanged original map in its original universes.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- Structural cylinder data on the original common-universe model gives the
weak theorem for the original canonical fiber map, preserving its full path. -/
theorem canonicalFiberMap_isWeakHomotopyEquivalence_of_smallModelCylinder
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N.smallModel)
    (hs : RowFactorization.SecondEndpointSection N.smallModel D) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N) := by
  let : N.smallModel.coarse.weq.HasTwoOutOfThreeProperty :=
    N.coarse.smallModel_twoOutOfThree
  exact canonicalFiberMap_isWeakHomotopyEquivalence_of_smallModel N
    (canonicalFiberMap_isWeakHomotopyEquivalence N.smallModel
      (N.coarse.smallModel_extensionAxiom he) D hs)
/-- The original global fibration theorem for distinct object and hom universes. -/
theorem canonicalFiberMap_isWeakHomotopyEquivalence_general
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N) :=
  canonicalFiberMap_isWeakHomotopyEquivalence_of_smallModelCylinder N he D.smallModel hs.smallModel
end Quillen.Waldhausen.Fibration
