/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Scheme.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Scheme-open pairs and their actual commutative squares

Objects are original open immersions. Morphisms are arbitrary commutative
squares of scheme maps, not necessarily cartesian or flat. The qc full
subcategory restricts the ambient scheme only; the open need not be qc.
-/

universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.Scheme

abbrev openPairProperty : ObjectProperty (Arrow AlgebraicGeometry.Scheme.{u}) :=
  fun j => IsOpenImmersion j.hom
abbrev OpenPairs := openPairProperty.{u}.FullSubcategory
instance openPairs_openImmersion (X : OpenPairs.{u}) : IsOpenImmersion X.obj.hom := X.property

abbrev quasiCompactOpenPairProperty : ObjectProperty OpenPairs.{u} :=
  fun X => CompactSpace X.obj.right
abbrev QuasiCompactOpenPairs := quasiCompactOpenPairProperty.{u}.FullSubcategory
instance quasiCompactOpenPairs_compactSpace (X : QuasiCompactOpenPairs.{u}) :
    CompactSpace X.obj.obj.right := X.property

abbrev quasiCompactOpenPairsInclusion : QuasiCompactOpenPairs.{u} ⥤ OpenPairs.{u} :=
  quasiCompactOpenPairProperty.{u}.ι

end Quillen.Scheme
namespace Quillen.Scheme

def quasiCompactOpenPairsBase : QuasiCompactOpenPairs.{u} ⥤ QuasiCompactSchemes.{u} where
  obj X := ⟨X.obj.obj.right, inferInstance⟩
  map f := ObjectProperty.homMk f.hom.hom.right

end Quillen.Scheme
