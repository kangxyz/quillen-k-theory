/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassFineTelescopeComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeMapNaturality

/-!
# Invertibility of the original native Bass negative-class map

For a compact quasi-separated scheme, the pre-existing negative-class transformation is
invertible. Its unchanged formula is precisely the forward map of the proved fine-telescope
comparison. Its actual inverse respects arbitrary scheme-over-base restrictions between
qcqs schemes, using the already proved naturality of the original forward map.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}

/-- The proved comparison has exactly the pre-existing original negative-class map. -/
theorem boundedFlatCoefficientAmbientNegativeKTelescopeComparison_hom
    (P : Over (Spec R)) [CompactSpace P.left] [QuasiSeparatedSpace P.left] (i : ℕ) :
    (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom =
      boundedFlatCoefficientAmbientBassNegativeMap P i := rfl

/-- The unchanged original negative-class transformation is an isomorphism. -/
instance boundedFlatCoefficientAmbientBassNegativeMap_isIso
    (P : Over (Spec R)) [CompactSpace P.left] [QuasiSeparatedSpace P.left] (i : ℕ) :
    IsIso (boundedFlatCoefficientAmbientBassNegativeMap P i) := by
  rw [← boundedFlatCoefficientAmbientNegativeKTelescopeComparison_hom P i]
  infer_instance

variable {P Q : Over (Spec R)} (f : P ⟶ Q)
  [CompactSpace P.left] [QuasiSeparatedSpace P.left]
  [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The actual inverse negative-class map retains arbitrary original scheme restriction. -/
theorem boundedFlatCoefficientAmbientBassNegativeMap_inv_schemeRestriction (i : ℕ) :
    Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f)
        (stableHomotopyFunctor (-(i : ℤ))) ≫
      inv (boundedFlatCoefficientAmbientBassNegativeMap P i) =
    inv (boundedFlatCoefficientAmbientBassNegativeMap Q i) ≫
      boundedFlatCoefficientOriginalNegativeKRestriction f i := by
  apply (cancel_mono (boundedFlatCoefficientAmbientBassNegativeMap P i)).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc,
    boundedFlatCoefficientAmbientBassNegativeMap_schemeRestriction,
    IsIso.inv_hom_id_assoc]

end Quillen.PerfectComplexes
