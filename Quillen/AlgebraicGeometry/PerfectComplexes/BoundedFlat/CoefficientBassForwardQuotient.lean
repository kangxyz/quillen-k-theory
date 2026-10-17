/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassQuotientIso

/-!
# The original signed forward-unit Bass quotient

The literal forward Laurent unit induces an isomorphism to the original Bass quotient. Its
composite with the unchanged geometric first-coordinate boundary is minus the identity. Thus
the actual raw seed sign is retained, rather than replacing its unit operation by the inverse.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Waldhausen.Additivity.KCommGroup
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The literal forward Laurent-unit operation, natural under every coefficient map. -/
def boundedFlatCoefficientForwardUnitSection (n : ℕ) :
    boundedFlatCoefficientKAddFunctor P n ⟶
      laurentUnderFunctor R ⋙ boundedFlatCoefficientKAddFunctor P (n + 1) where
  app a := AddCommGrpCat.ofHom (boundedFlatCoefficientLaurentKOperation P a n).toAdditive
  naturality {a b} f := by
    apply AddCommGrpCat.hom_ext
    exact (congrArg MonoidHom.toAdditive
      (boundedFlatCoefficientLaurentKOperation_naturality P f n)).symm

/-- The original forward unit followed by the unchanged original quotient projection. -/
def boundedFlatCoefficientForwardUnitQuotient (n : ℕ) :
    boundedFlatCoefficientKAddFunctor P n ⟶
      contraction (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientKAddFunctor P (n + 1)) :=
  boundedFlatCoefficientForwardUnitSection P n ≫
    contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientKAddFunctor P (n + 1))

variable [CompactSpace P.left] [QuasiSeparatedSpace P.left] (a : Under R)

/-- The actual geometric comparison detects precisely the original forward-unit minus sign. -/
@[reassoc]
theorem boundedFlatCoefficientForwardUnitQuotient_boundary (n : ℕ) :
    (boundedFlatCoefficientForwardUnitQuotient P n).app a ≫
      (boundedFlatCoefficientPositiveBassBoundaryQuotientIso P a n).hom = -𝟙 _ := by
  change ((boundedFlatCoefficientForwardUnitSection P n).app a ≫ _) ≫ _ = _
  rw [Category.assoc, boundedFlatCoefficientPositiveBassBoundaryQuotientIso_π]
  apply AddCommGrpCat.hom_ext
  exact congrArg MonoidHom.toAdditive
    (boundedFlatCoefficientPositiveBassBoundary_comp_forward P a n)

/-- The unchanged forward unit is the signed inverse of the original boundary comparison. -/
theorem boundedFlatCoefficientForwardUnitQuotient_eq_neg_inv (n : ℕ) :
    (boundedFlatCoefficientForwardUnitQuotient P n).app a =
      -(boundedFlatCoefficientPositiveBassBoundaryQuotientIso P a n).inv := by
  apply (cancel_mono (boundedFlatCoefficientPositiveBassBoundaryQuotientIso P a n).hom).mp
  rw [boundedFlatCoefficientForwardUnitQuotient_boundary, Preadditive.neg_comp, Iso.inv_hom_id]

instance boundedFlatCoefficientForwardUnitQuotient_app_isIso (n : ℕ) :
    IsIso ((boundedFlatCoefficientForwardUnitQuotient P n).app a) := by
  rw [boundedFlatCoefficientForwardUnitQuotient_eq_neg_inv]
  change IsIso (-(boundedFlatCoefficientPositiveBassBoundaryQuotientIso P a n)).inv
  infer_instance

instance boundedFlatCoefficientForwardUnitQuotient_isIso (n : ℕ) :
    IsIso (boundedFlatCoefficientForwardUnitQuotient P n) := NatIso.isIso_of_isIso_app _

end Quillen.PerfectComplexes
