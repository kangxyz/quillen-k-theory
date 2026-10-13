/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Fibration.RelativeRows.FiberTransport
public import Quillen.Topology.HELP.SquareRealizationLifting

/-! # Actual lifting for normalized relative-row transition comparisons

Every fiber premise is derived from genuine degreewise row additivity and
individual path transport. The original normalized comparison's mapping-path
endpoint therefore lifts over every realized simplicial monomorphism.
This supplies a relative-cell lifting input, without asserting global gluing.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{u} C] {V : Structure C}
  (N : NestedWeakEquivalences V) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)

/-- The unchanged actual normalized mapping-path comparison of the ordinal square. -/
def rowNormalizedComparison : C(
    MappingPath (SSet.toTop.map ((tailSRows N).app m)).hom,
    {z : |(ordinarySRows (acyclicStructure N)).obj m| ×
        MappingPath (SSet.toTop.map ((tailSRows N).app n)).hom //
      MappingPath.endpoint (SSet.toTop.map ((tailSRows N).app n)).hom z.2 =
        SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α) z.1}) :=
  MappingPath.strictComparison
  (SSet.toTop.map ((relativeSRows N).map α)).hom
  (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
  (rowTransitionSquare N α)

/-- Both original normalized source coordinates are retained literally. -/
@[simp] theorem rowNormalizedComparison_apply
    (z : MappingPath (SSet.toTop.map ((tailSRows N).app m)).hom) :
    (rowNormalizedComparison N α z).val =
      (MappingPath.endpoint (SSet.toTop.map ((tailSRows N).app m)).hom z,
       MappingPath.map (SSet.toTop.map ((relativeSRows N).map α)).hom
         (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
         (rowTransitionSquare N α) z) := rfl

/-- The actual normalized comparison endpoint lifts every realized simplicial
inclusion, with no finite-dimensional or compact target assumption. -/
theorem rowNormalizedComparison_endpoint_realization_mono
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i)
      (TopCat.ofHom (MappingPath.endpoint (rowNormalizedComparison N α))) :=
  MappingPath.strictComparison_endpoint_realization_mono
    (SSet.toTop.map ((relativeSRows N).map α)).hom
    (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
    (rowTransitionSquare N α) (fun b ↦ rowTransitionFiberAt_compactHELP N α b) i

end Quillen.Waldhausen.Fibration.RelativeRows
