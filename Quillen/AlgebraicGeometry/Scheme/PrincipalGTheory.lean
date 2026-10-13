/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.GTheory
public import Quillen.AlgebraicGeometry.Scheme.Coherent.PrincipalLocalization

/-!
# Principal-open localization for the public global G-theory

These maps use `Quillen.Scheme.G` and `SupportedG` in universe `u + 1`.
The open map is the original geometric `restrictG`. This is the principal
open of a noetherian affine scheme, not the still-open general quotient theorem.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.Scheme.Principal
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

/-- Canonical inclusion of the actual supported coherent G-group. -/
abbrev inclusionG (n : ℕ) :
    SupportedG (CoherentScheme.principalOpen R r) n →* G (Spec R) n :=
  CoherentScheme.globalPrincipalInclusionGMap R r n

/-- The actual path-space localization boundary in the global scheme model. -/
abbrev boundaryG (n : ℕ) :
    G (Spec (CommRingCat.of (Localization.Away r))) (n + 1) →*
      SupportedG (CoherentScheme.principalOpen R r) n :=
  CoherentScheme.globalPrincipalConnectingHom R r n

/-- Exactness at the ambient scheme in every nonnegative degree. -/
theorem inclusion_range_eq_restrict_ker (n : ℕ) :
    (inclusionG R r n).range = (restrictG (CoherentScheme.principalOpen R r) n).ker :=
  CoherentScheme.globalPrincipal_inclusion_range_eq_restriction_ker R r n

/-- Exactness at the principal open in every positive degree. -/
theorem restrict_range_eq_boundary_ker (n : ℕ) :
    (restrictG (CoherentScheme.principalOpen R r) (n + 1)).range = (boundaryG R r n).ker :=
  CoherentScheme.globalPrincipal_restriction_range_eq_connecting_ker R r n

/-- Exactness at supported G-theory, including degree zero. -/
theorem boundary_range_eq_inclusion_ker (n : ℕ) :
    (boundaryG R r n).range = (inclusionG R r n).ker :=
  CoherentScheme.globalPrincipal_connecting_range_eq_inclusion_ker R r n

/-- The connective tail ends in a surjection onto the open's G-zero. -/
theorem restrictG_zero_surjective :
    Function.Surjective (restrictG (CoherentScheme.principalOpen R r) 0) :=
  CoherentScheme.globalPrincipal_GZero_surjective R r
end Quillen.Scheme.Principal
