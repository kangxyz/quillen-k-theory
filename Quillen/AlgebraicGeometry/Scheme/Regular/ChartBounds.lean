/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Regular.AffineChartDimension
public import Quillen.AlgebraicGeometry.Scheme.Regular.Regularity
public import Quillen.Algebra.RegularLocal.GlobalProjectiveDimension

/-!
# Objectwise finite bounds on a finite regular affine cover

The projective-dimension bound depends on the chosen coherent sheaf. It is
the maximum of finitely many actual chart-module bounds. No finite Krull
dimension of the scheme or bound uniform in all sheaves is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory AlgebraicGeometry

namespace Quillen.SchemeSheaf
variable {X : AlgebraicGeometry.Scheme.{u}} [IsLocallyNoetherian X]

/-- A bound on the projective dimensions of the actual module restrictions
to each chart in a specified affine cover. -/
def AffineCoverDimensionLE (U : X.AffineOpenCover.{v})
    (M : CoherentScheme.FiniteTypeSheaves X) (n : ℕ) : Prop :=
  ∀ i, HasProjectiveDimensionLE ((coherentChartModule (U.X i) (U.f i)).obj M) n

omit [IsLocallyNoetherian X] in
/-- Finitely many finite chart-module dimensions admit one bound for the
specified coherent sheaf. This is only a finite maximum, not a uniform
regular-scheme dimension assertion. -/
theorem exists_affineCoverDimensionLE_of_finite (U : X.AffineOpenCover.{v}) [Finite U.I₀]
    (M : CoherentScheme.FiniteTypeSheaves X)
    (hM : ∀ i, projectiveDimension ((coherentChartModule (U.X i) (U.f i)).obj M) ≠ ⊤) :
    ∃ n, AffineCoverDimensionLE U M n := by
  classical
  let := Fintype.ofFinite U.I₀
  have h (i : U.I₀) := (projectiveDimension_ne_top_iff
    ((coherentChartModule (U.X i) (U.f i)).obj M)).mp (hM i)
  choose d hd using h
  refine ⟨Finset.univ.sup d, ?_⟩
  intro i
  have := hd i
  exact hasProjectiveDimensionLT_of_ge _ (d i + 1) (Finset.univ.sup d + 1)
    (Nat.add_le_add_right (Finset.le_sup (Finset.mem_univ i)) 1)

end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
variable {X : AlgebraicGeometry.Scheme.{u}}

/-- On a finite affine cover of an actually regular scheme, every coherent
sheaf has an object-dependent finite chart-module bound. -/
theorem exists_affineCoverDimensionLE_of_regular [Scheme.IsRegular X]
    (U : X.AffineOpenCover.{v}) [Finite U.I₀] (M : CoherentScheme.FiniteTypeSheaves X) :
    ∃ n, AffineCoverDimensionLE U M n := by
  apply exists_affineCoverDimensionLE_of_finite U M
  intro i
  have := Scheme.regular_affineChart (U.X i) (U.f i)
  exact CoherentScheme.projectiveDimension_ne_top_of_regular (U.X i)
    ((coherentChartModule (U.X i) (U.f i)).obj M)

/-- Quasi-compactness supplies the finite affine cover needed for the
objectwise bound. -/
theorem exists_finiteCoverDimensionLE_of_regular [Scheme.IsRegular X] [CompactSpace X]
    (M : CoherentScheme.FiniteTypeSheaves X) :
    ∃ n, AffineCoverDimensionLE (Scheme.finiteAffineOpenCover X) M n :=
  exists_affineCoverDimensionLE_of_regular (Scheme.finiteAffineOpenCover X) M

end Quillen.SchemeSheaf
