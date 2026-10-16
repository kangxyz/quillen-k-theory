/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientConeAdditivity
/-! Strict consumers of the actual tautological factorization and all-degree cone difference. -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.TautologicalCoefficientConeAdditivity
variable (R : CommRingCat.{u})

/-- Every original coordinate, rather than a replacement scalar, is the same composite. -/
theorem original_coordinate_factorization :
    tautologicalCoefficientInclusionNat R ≫ tautologicalCoefficientProjectionNat R =
      tautologicalCoefficientPerfectTransformation R :=
  tautologicalCoefficientInclusionNat_projection R

/-- The signed quotient is the literal original chain map on every perfect coefficient. -/
theorem original_signed_quotient (K : Perfect (twoChartLine R)) :
    ((tautologicalCoefficientConeProjectionNat R).app K).hom =
      SplitFactorization.quotientToCone (tautologicalCoefficientPerfectCoordinate R K).hom := rfl

/-- Both natural arrows form a genuine inherited cofibration sequence. -/
theorem original_cofibration_sequence :
    Additivity.IsCofibrationSequence (perfectWaldhausen (twoChartLine R))
      (perfectWaldhausen (twoChartLine R)) (tautologicalCoefficientInclusionNat R)
      (tautologicalCoefficientConeProjectionNat R) :=
  tautologicalCoefficientCofibrationSequence R

/-- The actual projection is weak on every input before any geometric transport. -/
theorem original_projection_weak (K : Perfect (twoChartLine R)) :
    (perfectWaldhausen (twoChartLine R)).weq ((tautologicalCoefficientProjectionNat R).app K) :=
  tautologicalCoefficientProjectionNat_weak R K

/-- The original sequence keeps the subobject-first multiplication order. -/
theorem original_sequence_order (n : ℕ) (x : PerfectK (twoChartLine R) n) :
    x = tautologicalCoefficientTensorKMap R n x *
      perfectSupportedKMap (plusChart R) n (tautologicalCoefficientConeKMap R n x) :=
  tautologicalCoefficientConeKMap_mul R n x

/-- Every connective class has the exact support-forgotten cone difference. -/
theorem arbitrary_original_class (n : ℕ) (x : PerfectK (twoChartLine R) n) :
    perfectSupportedKMap (plusChart R) n (tautologicalCoefficientConeKMap R n x) =
      x * (tautologicalCoefficientTensorKMap R n x)⁻¹ :=
  tautologicalCoefficientConeKMap_forget R n x

/-- Degree zero accepts an arbitrary original class, with no object-generation premise. -/
theorem arbitrary_original_kzero (x : PerfectK (twoChartLine R) 0) :
    perfectSupportedKMap (plusChart R) 0 (tautologicalCoefficientConeKMap R 0 x) =
      x * (tautologicalCoefficientTensorKMap R 0 x)⁻¹ :=
  tautologicalCoefficientConeKMap_forget R 0 x

/-- The support-forgetting composite is the exact original composite functor K-map. -/
theorem original_support_forgetting_hom (n : ℕ) :
    (perfectSupportedKMap (plusChart R) n).comp (tautologicalCoefficientConeKMap R n) =
      KMap (tautologicalCoefficientForgottenConeFunctor_waldhausenExact R) n :=
  tautologicalCoefficientForgottenCone_KMap R n

local instance (n : ℕ) : CommGroup (PerfectK (twoChartLine R) n) :=
  Additivity.KCommGroup (perfectWaldhausen (twoChartLine R)) n

/-- The equality is of the full original homomorphisms in every connective degree. -/
theorem entire_original_homomorphism (n : ℕ) :
    (perfectSupportedKMap (plusChart R) n).comp (tautologicalCoefficientConeKMap R n) =
      MonoidHom.id (PerfectK (twoChartLine R) n) *
        (invMonoidHom.comp (tautologicalCoefficientTensorKMap R n)) :=
  tautologicalCoefficientConeKMap_forget_hom R n

end QuillenTest.TautologicalCoefficientConeAdditivity
