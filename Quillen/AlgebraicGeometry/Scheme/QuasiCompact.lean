/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Quasi-compact schemes with all scheme morphisms

This full subcategory restricts objects only. Its morphisms have no flatness,
separatedness or quasi-compactness premise.
-/
@[expose] public section


universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.Scheme

/-- Quasi-compactness of a scheme, with no restriction on its morphisms. -/
abbrev quasiCompactSchemeProperty : ObjectProperty AlgebraicGeometry.Scheme.{u} :=
  fun X => CompactSpace X

/-- Quasi-compact schemes with all scheme morphisms. -/
abbrev QuasiCompactSchemes := quasiCompactSchemeProperty.{u}.FullSubcategory

instance quasiCompactSchemes_compactSpace (X : QuasiCompactSchemes.{u}) :
    CompactSpace X.obj := X.property

/-- The full-subcategory inclusion of quasi-compact schemes into all schemes. -/
abbrev quasiCompactSchemesInclusion : QuasiCompactSchemes.{u} ⥤ AlgebraicGeometry.Scheme.{u} :=
  quasiCompactSchemeProperty.{u}.ι

end Quillen.Scheme
