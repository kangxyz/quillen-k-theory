/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Pairs

/-!
# The actual identity-base support square

An inequality of support opens retains its original inclusion and identity ambient map, with
the unchanged compact-ambient wrapper.
-/
@[expose] public section



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {X : Scheme.{u}} {S T : X.Opens} (h : S ≤ T)

/-- The actual identity-base square for an inclusion of auxiliary opens. -/
def supportChangeOpenPair : supportOpenPair S ⟶ supportOpenPair T :=
  ObjectProperty.homMk (Arrow.homMk (X.homOfLE h) (𝟙 X)
    (by change X.homOfLE h ≫ T.ι = S.ι ≫ 𝟙 X
        rw [Category.comp_id, Scheme.homOfLE_ι]))

variable [CompactSpace X]

/-- The actual auxiliary-support change as a morphism of quasi-compact open pairs. -/
def qcSupportChangeOpenPair :
    (⟨supportOpenPair S, (by change CompactSpace X; infer_instance)⟩ :
      AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}) ⟶
      ⟨supportOpenPair T, (by change CompactSpace X; infer_instance)⟩ :=
  ObjectProperty.homMk (supportChangeOpenPair h)

end Quillen.PerfectComplexes

end

end
