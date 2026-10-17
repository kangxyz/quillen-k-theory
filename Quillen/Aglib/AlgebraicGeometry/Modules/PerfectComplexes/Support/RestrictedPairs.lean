/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Pairs
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.ChangeOpenPairs

/-!
# The scheme pair of a restricted support inequality

The original pair square retains the specified restricted map. Its ambient map determines it
uniquely.-/
@[expose] public section



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (S : U.Opens) (T : X.Opens) (h : S ≤ j ⁻¹ᵁ T)

/-- The actual pair square underlying this supported restriction. -/
def supportRestrictedPair : supportOpenPair S ⟶ supportOpenPair T :=
  supportChangeOpenPair h ≫ supportRestrictionPair j T

omit [IsOpenImmersion j] in
@[simp] theorem supportRestrictedPair_right :
    (supportRestrictedPair j S T h).hom.right = j := by
  change 𝟙 U ≫ j = j
  simp

omit [IsOpenImmersion j] in
/-- Both original support inclusions remain the actual maps of the pair square. -/
theorem supportRestrictedPair_left :
    (supportRestrictedPair j S T h).hom.left = j.resLE T S h := by
  apply (cancel_mono T.ι).mp
  have hw : (supportRestrictedPair j S T h).hom.left ≫ T.ι =
      S.ι ≫ (supportRestrictedPair j S T h).hom.right := (supportRestrictedPair j S T h).hom.w
  rw [hw, j.resLE_comp_ι h, supportRestrictedPair_right]

/-- The right map determines a morphism of the actual open-pair category. -/
theorem supportOpenPair_hom_ext {U X : Scheme.{u}} {S : U.Opens} {T : X.Opens}
    {f g : supportOpenPair S ⟶ supportOpenPair T} (he : f.hom.right = g.hom.right) : f = g := by
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · apply (cancel_mono T.ι).mp
    have hf : f.hom.left ≫ T.ι = S.ι ≫ f.hom.right := f.hom.w
    have hg : g.hom.left ≫ T.ι = S.ι ≫ g.hom.right := g.hom.w
    rw [hf, hg, he]
  · exact he

end Quillen.PerfectComplexes


end

end
