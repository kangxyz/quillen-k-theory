/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.PrincipalLocalization
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.ClosedDevissage
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison

/-!
# Public lower-universe affine coherent G-theory

These groups use the established `u`-small affine presentation. They are kept
separate from the `u + 1`-small global `Quillen.Scheme.G` until the corresponding
presentation comparison is proved. All maps below retain the original geometric
restriction, supported inclusion and path-space connecting homomorphism.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Affine
variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Actual affine coherent G-theory in its established `u`-small presentation. -/
abbrev G (n : ℕ) : Type u := AlgebraicGeometry.Scheme.Modules.Coherent.AffineG R n

/-- The canonical equivalence induced by affine global sections. -/
abbrev moduleEquiv (n : ℕ) : G R n ≃* AlgebraicGeometry.Scheme.Modules.Coherent.RingG R n :=
  AlgebraicGeometry.Scheme.Modules.Coherent.affineGEquiv R n

variable (r : R)

/-- The actual principal-closed supported G-term. -/
abbrev SupportedG (n : ℕ) : Type u := AlgebraicGeometry.Scheme.Modules.Coherent.PrincipalSupportedG
  R r n

/-- Geometric restriction from `Spec R` to its principal open. -/
abbrev restrictG (n : ℕ) : G R n →* G (CommRingCat.of (Localization.Away r)) n :=
  AlgebraicGeometry.Scheme.Modules.Coherent.principalRestrictionGMap R r n

/-- The canonical supported inclusion. -/
abbrev inclusionG (n : ℕ) : SupportedG R r n →* G R n :=
  AlgebraicGeometry.Scheme.Modules.Coherent.principalInclusionGMap R r n

/-- The connecting homomorphism constructed from the actual path-space boundary. -/
abbrev boundaryG (n : ℕ) :
    G (CommRingCat.of (Localization.Away r)) (n + 1) →* SupportedG R r n :=
  AlgebraicGeometry.Scheme.Modules.Coherent.principalConnectingHom R r n

/-- The public principal-open map is the original exact restriction K-map. -/
@[simp] theorem restrictG_eq_smallKMap (n : ℕ) :
    restrictG R r n = (AlgebraicGeometry.Scheme.Modules.Coherent.affinePrincipalRestrictionExact R
      r).smallKMap n := rfl

/-- Exactness at the ambient affine G-group. -/
theorem inclusion_range_eq_restrict_ker (n : ℕ) :
    (inclusionG R r n).range = (restrictG R r n).ker :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.principal_localization_longExact R r).1 n

/-- Exactness at the principal-open G-group. -/
theorem restrict_range_eq_boundary_ker (n : ℕ) :
    (restrictG R r (n + 1)).range = (boundaryG R r n).ker :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.principal_localization_longExact R r).2.1 n

/-- Exactness at the genuine support group. -/
theorem boundary_range_eq_inclusion_ker (n : ℕ) :
    (boundaryG R r n).range = (inclusionG R r n).ker :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.principal_localization_longExact R r).2.2.1 n

/-- The connective affine sequence ends in a surjection on G₀. -/
theorem restrictG_zero_surjective : Function.Surjective (restrictG R r 0) :=
  AlgebraicGeometry.Scheme.Modules.Coherent.principal_GZero_surjective R r

end AlgebraicGeometry.Scheme.Affine
