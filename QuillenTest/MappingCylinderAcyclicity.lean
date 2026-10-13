/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.MappingCylinderAcyclicity

/-! # Actual original-map and embedded-pair tests for mapping-cylinder acyclicity -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open Quillen Quillen.LocalCoefficients
universe u
namespace QuillenTest.MappingCylinderAcyclicity
variable {X Y M : TopCat.{u}} {f : X ⟶ Y}
  {l : X ⊗ TopCat.I ⟶ M} {c : Y ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I) f l c)

include sq

/-- The original map is retained without an injectivity hypothesis. -/
theorem original_map_retained (x : X) :
    MappingCylinder.mappingCylinderProjection sq ((TopCat.ι₀ ≫ l) x) = f x :=
  ConcreteCategory.congr_hom (MappingCylinder.mappingCylinderProjection_start sq) x

/-- The quotient comparison uses the actual range of the original source endpoint map. -/
theorem embedded_quotient_retained (A : System.{u, u} M) :
    cokernel.π (pushforwardChainMap (TopCat.ι₀ ≫ l).hom A) ≫
      (embeddingCokernelIsoRelative (TopCat.ι₀ ≫ l).hom
        (MappingCylinder.mappingCylinderStart_isEmbedding sq) A).hom =
    cokernel.π (pushforwardChainMap
      (subspaceInclusion (Set.range (TopCat.ι₀ ≫ l).hom)) A) :=
  embeddingCokernelIsoRelative_quotient _ _ _

/-- Arbitrary original-map quasi-isomorphisms kill degree-zero relative homology too. -/
theorem relative_degree_zero (A : System.{u, u} Y)
    (hq : QuasiIso (pushforwardChainMap f.hom A)) :
    IsZero ((relativeSingularChainComplex (Set.range (TopCat.ι₀ ≫ l).hom)
      (pullback (MappingCylinder.mappingCylinderProjection sq).hom A)).homology 0) :=
  (mappingCylinderRelative_acyclic_of_quasiIso sq A hq 0).isZero_homology

/-- Integer coefficients live in the same universe as the actual singular complex. -/
theorem integral_relative_degree_two
    (hq : QuasiIso (pushforwardChainMap f.hom
      (constant Y (ModuleCat.of ℤ (ULift.{u} ℤ))))) :
    IsZero ((relativeSingularChainComplex (Set.range (TopCat.ι₀ ≫ l).hom)
      (constant M (ModuleCat.of ℤ (ULift.{u} ℤ)))).homology 2) :=
  (mappingCylinderRelative_constant_acyclic_of_quasiIso sq _ hq 2).isZero_homology

end QuillenTest.MappingCylinderAcyclicity
