/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.GTheory
public import Quillen.AlgebraicGeometry.Scheme.Coherent.GlobalLocalization

/-!
# Canonical supported G-localization on noetherian schemes

For an actual open immersion into a noetherian scheme, these public maps
and exactness theorems use the original supported inclusion and geometric
restriction. Coherent extension and the quotient equivalence are proved
internally; neither is an input hypothesis.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme

/-- The actual inclusion of supported coherent sheaves on G-theory. -/
abbrev inclusionG {U X : AlgebraicGeometry.Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) : SupportedG j n →* G X n :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.supportedCoherentInclusionExact j).smallKMap n

variable {U X : AlgebraicGeometry.Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The genuine path-space boundary, with the actual supported G-model. -/
abbrev boundaryG (n : ℕ) : G U (n + 1) →* SupportedG j n :=
  AlgebraicGeometry.Scheme.Modules.Coherent.globalConnectingHom j n

/-- Exactness at the ambient scheme in every nonnegative degree. -/
theorem inclusion_range_eq_restrict_ker (n : ℕ) :
    (inclusionG j n).range = (restrictG j n).ker := by
  exact (AlgebraicGeometry.Scheme.Modules.Coherent.global_localization_canonical_longExact j).1 n

/-- Exactness at the open in every positive degree. -/
theorem restrict_range_eq_boundary_ker (n : ℕ) :
    (restrictG j (n + 1)).range = (boundaryG j n).ker :=
  AlgebraicGeometry.Scheme.Modules.Coherent.global_restriction_range_eq_connecting_ker j n

/-- Exactness at supported G-theory, including degree zero. -/
theorem boundary_range_eq_inclusion_ker (n : ℕ) :
    (boundaryG j n).range = (inclusionG j n).ker := by
  simpa only [AlgebraicGeometry.Scheme.Modules.Coherent.globalInclusionGMap_eq_smallKMap] using
    AlgebraicGeometry.Scheme.Modules.Coherent.global_connecting_range_eq_inclusion_ker j n

/-- The connective tail ends in a surjection onto the open's G-zero. -/
theorem restrictG_zero_surjective : Function.Surjective (restrictG j 0) :=
  AlgebraicGeometry.Scheme.Modules.Coherent.global_GZero_surjective j

/-- The complete supported localization sequence with both canonical arrows. -/
theorem localization_longExact :
    (∀ n, (inclusionG j n).range = (restrictG j n).ker) ∧
    (∀ n, (restrictG j (n + 1)).range = (boundaryG j n).ker) ∧
    (∀ n, (boundaryG j n).range = (inclusionG j n).ker) ∧
    Function.Surjective (restrictG j 0) :=
  ⟨inclusion_range_eq_restrict_ker j, restrict_range_eq_boundary_ker j,
    boundary_range_eq_inclusion_ker j, restrictG_zero_surjective j⟩
end AlgebraicGeometry.Scheme
