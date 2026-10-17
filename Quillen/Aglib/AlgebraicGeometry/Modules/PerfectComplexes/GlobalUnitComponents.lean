/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnitInversion
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnit

/-!
# Original flat-pullback unit components

The inverse unit and actual natural-automorphism components retain the original functor and
geometric unit.-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Inverting the unit inverts the same actual natural automorphism of flat pullback. -/
theorem perfectFlatPullbackUnitIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (q : (Γ(X, ⊤))ˣ) :
    perfectFlatPullbackUnitIso f q⁻¹ = (perfectFlatPullbackUnitIso f q).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have h := congrArg Iso.hom
    (perfectGlobalUnitIso_app_inv X q ((perfectFlatPullback f).obj K))
  simpa [perfectFlatPullbackUnitIso] using h

end Quillen.PerfectComplexes

end

end

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
  (q : (Γ(X, ⊤))ˣ) (K : Perfect Y)

/-- The actual right-unitor factors leave precisely the original forward unit component. -/
theorem perfectFlatPullbackUnitIso_app :
    (perfectFlatPullbackUnitIso f q).app K =
      (perfectGlobalUnitIso X q).app ((perfectFlatPullback f).obj K) := by
  apply Iso.ext
  simp [perfectFlatPullbackUnitIso]

end Quillen.PerfectComplexes

end

end
