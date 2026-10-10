/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Quasi-compact schemes with all scheme morphisms

This full subcategory restricts objects only. Its morphisms have no flatness,
separatedness or quasi-compactness premise.
-/

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

abbrev quasiCompactSchemesInclusion : QuasiCompactSchemes.{u} ⥤ AlgebraicGeometry.Scheme.{u} :=
  quasiCompactSchemeProperty.{u}.ι

end Quillen.Scheme
