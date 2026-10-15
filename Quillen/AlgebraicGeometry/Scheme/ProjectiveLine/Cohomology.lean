/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.AffineComparison
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts

/-! # Higher quasicoherent cohomology of the original projective line

For every quasicoherent module sheaf on the genuine two-chart projective line,
actual right-derived additive global sections vanish in degrees at least two.
The proof uses the original polynomial charts and original Laurent intersection,
via their established open immersions. It applies over every commutative ring.

No degree-one vanishing, twisting-sheaf computation, pushforward perfection,
or projective bundle formula is asserted.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.TwoOpen
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
variable (R : CommRingCat.{u})

/-- Original sections of any actual injective resolution of a quasicoherent
module sheaf are exact in degrees at least two on the two-chart line. -/
theorem injectiveResolution_sections_exact_add_two
    (M : (twoChartLine R).Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) (n : ℕ) :
    (((sectionsFunctor (twoChartLine R) ⊤).mapHomologicalComplex _).obj I.cocomplex).ExactAt
      (n + 2) :=
  twoAffine_injectiveResolution_exact_add_two (plusChart R) (minusChart R)
    (laurentPlus R ≫ plusChart R) (chart_ranges_cover R) (chart_ranges_inter R).symm M I n

/-- The actual positive derived global sections of every quasicoherent module
sheaf vanish above degree one on the original projective line. -/
theorem isZero_rightDerived_globalSections_add_two
    (M : (twoChartLine R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((sectionsFunctor (twoChartLine R) ⊤).rightDerived (n + 2)).obj M) :=
  twoAffine_isZero_rightDerived_add_two (plusChart R) (minusChart R)
    (laurentPlus R ≫ plusChart R) (chart_ranges_cover R) (chart_ranges_inter R).symm M n

end AlgebraicGeometry.Scheme.ProjectiveLine
