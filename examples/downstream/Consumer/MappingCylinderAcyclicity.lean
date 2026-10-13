/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.MappingCylinderAcyclicity

/-! # A downstream original-map consequence without source injectivity -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open Quillen.LocalCoefficients
universe u
namespace Consumer.MappingCylinderAcyclicity
variable {X Y M : TopCat.{u}} {f : X ⟶ Y}
  {l : X ⊗ TopCat.I ⟶ M} {c : Y ⟶ M}

/-- Downstream use takes the literal f and returns all positive relative groups of its cylinder
pair. -/
theorem original_quasiIso_relative_homology_zero
    (sq : IsPushout (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I) f l c)
    (V : ModuleCat.{u} ℤ) (hq : QuasiIso (pushforwardChainMap f.hom (constant Y V)))
    (n : ℕ) :
    IsZero ((relativeSingularChainComplex (Set.range (TopCat.ι₀ ≫ l).hom)
      (constant M V)).homology (n + 1)) :=
  (mappingCylinderRelative_constant_acyclic_of_quasiIso sq V hq (n + 1)).isZero_homology

end Consumer.MappingCylinderAcyclicity
