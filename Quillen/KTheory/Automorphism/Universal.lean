/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Automorphism.Class
public import Quillen.Topology.ClassifyingSpace.UniversalComposition

/-!
# The actual Q-cone loop map in mixed categorical universes

Universal realization extends the original zero-first cone construction.
Its small-category specialization is pointwise equal to the existing map.
The current consumers are the native completion marking and its actual
finite-module transport; this module changes no cube or sign convention.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped Topology unitInterval
namespace Quillen.Automorphism
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The original zero-first Q-cone loop family in the actual categorical universes. -/
def universalCoreLoopMap : C(ClassifyingSpace (Core C), Path E.kBasepoint E.kBasepoint) :=
  ConePair.naturalPair (zeroCone E) (fullCone E)

end Quillen.Automorphism

namespace Quillen.Automorphism
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- In the original small-category API, the universal map is pointwise the same zero-first map. -/
theorem universalCoreLoopMap_eq : universalCoreLoopMap E = coreLoopMap E := by
  ext z t
  change (((ConePair.realizedCone (zeroCone E)).evalAt z).trans
    ((ConePair.realizedCone (fullCone E)).evalAt z).symm) t =
      ((conePath E (zeroCone E) z).trans (conePath E (fullCone E) z).symm) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact classifyingSpaceUniversalHomotopy_eq (zeroCone E) _ z
  · exact classifyingSpaceUniversalHomotopy_eq (fullCone E) _ z

end Quillen.Automorphism
