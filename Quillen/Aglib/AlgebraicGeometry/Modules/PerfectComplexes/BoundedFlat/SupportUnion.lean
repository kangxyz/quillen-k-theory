/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Support
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Union

/-!
# The actual union of bounded-flat acyclicity opens

Support away from the union is exactly the original auxiliary support together with actual acyclicity on the specified open immersion.
-/
@[expose] public section



open AlgebraicGeometry.Scheme.Modules.Complex


open CategoryTheory.ExactCategory


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
lemma boundedFlatPerfectSupported_sup_opensRange_iff {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (A : CochainComplex X.Modules ℤ) :
    boundedFlatPerfectSupported (T ⊔ j.opensRange).ι A ↔
      boundedFlatPerfectSupported T.ι A ∧ ((restrict j).obj A).Acyclic := by
  change (boundedFlatPerfect X A ∧ _) ↔ (boundedFlatPerfect X A ∧ _) ∧ _
  rw [restrictAcyclic_sup_iff, restrictAcyclic_opensRange_iff]
  tauto

end Quillen.PerfectComplexes

end


end
