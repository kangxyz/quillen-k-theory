/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Scheme-open pairs and their actual commutative squares

Objects are original open immersions. Morphisms are arbitrary commutative
squares of scheme maps, not necessarily cartesian or flat. The qc full
subcategory restricts the ambient scheme only; the open need not be qc.
-/
@[expose] public section


universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.Scheme

/-- The property that an object of the scheme arrow category is an open immersion. -/
abbrev openPairProperty : ObjectProperty (Arrow AlgebraicGeometry.Scheme.{u}) :=
  fun j => IsOpenImmersion j.hom
/-- The full category of open immersions of schemes, with arbitrary commutative squares as
morphisms. -/
abbrev OpenPairs := openPairProperty.{u}.FullSubcategory
instance openPairs_openImmersion (X : OpenPairs.{u}) : IsOpenImmersion X.obj.hom := X.property

/-- The property that the ambient scheme of an open pair is quasi-compact; no quasi-compactness
condition is imposed on its open subscheme. -/
abbrev quasiCompactOpenPairProperty : ObjectProperty OpenPairs.{u} :=
  fun X => CompactSpace X.obj.right
/-- The full category of open pairs with quasi-compact ambient scheme, retaining all commutative
squares between such pairs. -/
abbrev QuasiCompactOpenPairs := quasiCompactOpenPairProperty.{u}.FullSubcategory
instance quasiCompactOpenPairs_compactSpace (X : QuasiCompactOpenPairs.{u}) :
    CompactSpace X.obj.obj.right := X.property

/-- The full-subcategory inclusion forgetting quasi-compactness of the ambient scheme of an open
pair. -/
abbrev quasiCompactOpenPairsInclusion : QuasiCompactOpenPairs.{u} ⥤ OpenPairs.{u} :=
  quasiCompactOpenPairProperty.{u}.ι

end Quillen.Scheme
namespace Quillen.Scheme

/-- The functor sending a quasi-compact open pair to its ambient quasi-compact scheme and a pair
square to its ambient scheme morphism. -/
def quasiCompactOpenPairsBase : QuasiCompactOpenPairs.{u} ⥤ QuasiCompactSchemes.{u} where
  obj X := ⟨X.obj.obj.right, inferInstance⟩
  map f := ObjectProperty.homMk f.hom.hom.right

end Quillen.Scheme
