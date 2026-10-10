/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SmallModel.Basic
public import Quillen.Waldhausen.ExtensionCategory.Functoriality
public import Quillen.Waldhausen.Fibration.Rows.SecondEndpoint
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Actual joint-cylinder data on a common-universe model

The original exact joint functor, its coproduct endpoints, and its weak projection
are transported through the genuine `AsSmall` equivalence. The second-endpoint
section identity is retained for the actual transported endpoint maps.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen
variable {C : Type u} [Category.{v} C]

local instance jointSmallUp_isEquivalence : (AsSmall.up : C ⥤ SmallModel C).IsEquivalence :=
  (AsSmall.equiv : C ≌ SmallModel C).isEquivalence_functor
local instance jointSmallDown_isEquivalence : (AsSmall.down : SmallModel C ⥤ C).IsEquivalence :=
  (AsSmall.equiv : C ≌ SmallModel C).isEquivalence_inverse

namespace Structure
variable (W : Structure C)

/-- Lowering actual arrows preserves their pointwise Waldhausen structure. -/
theorem smallModel_down_mapArrow_exact :
    IsExact (ArrowCategory.waldhausenStructure W.smallModel).cof
      (ArrowCategory.waldhausenStructure W.smallModel).weq
      (ArrowCategory.waldhausenStructure W).cof
      (ArrowCategory.waldhausenStructure W).weq
      (AsSmall.down : SmallModel C ⥤ C).mapArrow where
  zero h := IsZero.of_full_of_faithful_of_isZero
    (AsSmall.up : C ⥤ SmallModel C).mapArrow _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (AsSmall.down : SmallModel C ⥤ C).mapArrow

end Structure
namespace Fibration.RowFactorization
variable {W : Structure C} {N : NestedWeakEquivalences W}

/-- The original joint cylinder with the actual lifted endpoint and projection maps. -/
def JointData.smallModel (D : JointData N) : JointData N.smallModel where
  joint := (AsSmall.down : SmallModel C ⥤ C).mapArrow ⋙ D.joint ⋙
    ExtensionCategory.postcompose W W.smallModel W.smallModel_up_exact
  exact := W.smallModel_down_mapArrow_exact.comp
    (D.exact.comp (ExtensionCategory.postcompose_exact W W.smallModel W.smallModel_up_exact))
  inl := {
    app f := (AsSmall.up : C ⥤ SmallModel C).map (D.inl.app ((AsSmall.down : SmallModel C ⥤
      C).mapArrow.obj f))
    naturality f g α := by
      exact congrArg (AsSmall.up : C ⥤ SmallModel C).map
        (D.inl.naturality ((AsSmall.down : SmallModel C ⥤ C).mapArrow.map α)) }
  inr := {
    app f := (AsSmall.up : C ⥤ SmallModel C).map (D.inr.app ((AsSmall.down : SmallModel C ⥤
      C).mapArrow.obj f))
    naturality f g α := by
      exact congrArg (AsSmall.up : C ⥤ SmallModel C).map
        (D.inr.naturality ((AsSmall.down : SmallModel C ⥤ C).mapArrow.map α)) }
  coproduct f := mapIsColimitOfPreservesOfIsColimit (AsSmall.up : C ⥤ SmallModel C) _ _
    (D.coproduct ((AsSmall.down : SmallModel C ⥤ C).mapArrow.obj f))
  projection := {
    app f := (AsSmall.up : C ⥤ SmallModel C).map (D.projection.app ((AsSmall.down : SmallModel C
      ⥤ C).mapArrow.obj f))
    naturality f g α := by
      exact congrArg (AsSmall.up : C ⥤ SmallModel C).map
        (D.projection.naturality ((AsSmall.down : SmallModel C ⥤ C).mapArrow.map α)) }
  factorization f := congrArg (AsSmall.up : C ⥤ SmallModel C).map
    (D.factorization ((AsSmall.down : SmallModel C ⥤ C).mapArrow.obj f))
  weak f := D.weak ((AsSmall.down : SmallModel C ⥤ C).mapArrow.obj f)

/-- The actual transported second endpoint retains its original section identity. -/
theorem SecondEndpointSection.smallModel {D : JointData N} (hs : SecondEndpointSection N D) :
    SecondEndpointSection N.smallModel D.smallModel := by
  intro f
  exact congrArg (AsSmall.up : C ⥤ SmallModel C).map (hs ((AsSmall.down : SmallModel C ⥤
    C).mapArrow.obj f))

end Fibration.RowFactorization
end Quillen.Waldhausen
