/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Basic

/-!
# Actual support opens as scheme pairs

The original support inclusion, inverse-image support square and compact-ambient wrapper preserve
their actual scheme maps.-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The original support open, viewed as an actual open-pair object. -/
def supportOpenPair : AlgebraicGeometry.Scheme.OpenPairs.{u} :=
  ⟨Arrow.mk T.ι, (by change IsOpenImmersion T.ι; infer_instance)⟩

/-- The literal inverse-image support square. -/
def supportRestrictionPair : supportOpenPair (j ⁻¹ᵁ T) ⟶ supportOpenPair T :=
  ObjectProperty.homMk (Arrow.homMk (j.resLE T (j ⁻¹ᵁ T) le_rfl) j
    (j.resLE_comp_ι le_rfl))

variable [CompactSpace X] [CompactSpace U]

/-- The same original square in the existing qc open-pair category. -/
def qcSupportRestrictionPair :
    (⟨supportOpenPair (j ⁻¹ᵁ T), (by change CompactSpace U; infer_instance)⟩ :
      AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}) ⟶
      ⟨supportOpenPair T, (by change CompactSpace X; infer_instance)⟩ :=
  ObjectProperty.homMk (supportRestrictionPair j T)

end Quillen.PerfectComplexes

end

end
