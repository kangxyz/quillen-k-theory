import Quillen.Devissage.Setup
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-! # Finite products in a Serre class

This is derived from extension closure using split short exact sequences;
it is not an additional assumption on a Serre class.
-/

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace Quillen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

instance serre_isClosedUnderFiniteProducts : P.IsClosedUnderFiniteProducts := by
  let : P.IsClosedUnderBinaryProducts :=
    ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
      rintro _ ⟨F, hF⟩
      let e := (HasLimit.isoOfNatIso (diagramIsoPair F)).trans
        (biprod.isoProd (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)).symm
      exact P.prop_of_iso e.symm (P.prop_biprod (hF _) (hF _)))
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

end Quillen
