/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.ZeroSection
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.OpenPairs

/-!
# Actual zero sections and projection triangles for supported Bass products

Both entries of the original open-support pair use the same polynomial zero
section. Their commutative square is its scheme naturality square; the original
projection therefore splits on pairs, without requiring a quasi-compact
vanishing open. Both actual Laurent charts retain this pair projection.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.Products

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Bass

/-- The original first projection applied to both entries of the supported product. -/

def pairBaseProductProjection {S : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) [QuasiCompact p] : pairBaseProductFunctor p ⟶ 𝟭 _ where
  app A := ⟨⟨((Functor.mapArrowFunctor _ _).map (baseProductProjection p)).app A.obj.obj⟩⟩
  naturality {A B} f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact ((Functor.mapArrowFunctor _ _).map (baseProductProjection p)).naturality f.hom.hom

/-- The original polynomial projection of the same open-support pair. -/

abbrev pairPolynomialProjection : pairPolynomialFunctor.{u} ⟶ 𝟭 _ :=
  pairBaseProductProjection (PolynomialLaurent.polynomialProjection integerRing)

/-- The original Laurent projection of the same open-support pair. -/

abbrev pairLaurentProjection : pairLaurentFunctor.{u} ⟶ 𝟭 _ :=
  pairBaseProductProjection (PolynomialLaurent.laurentProjection integerRing)

/-- The natural zero section on both original scheme entries of the support pair. -/

def pairPolynomialZero : 𝟭 QuasiCompactOpenPairs.{u} ⟶ pairPolynomialFunctor where
  app A := ⟨⟨Arrow.homMk (nativePolynomialZero A.obj.obj.left)
    (nativePolynomialZero A.obj.obj.right)
    (nativePolynomialZero_naturality A.obj.obj.hom).symm⟩⟩
  naturality {A B} f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact nativePolynomialZero_naturality f.hom.hom.left
    · exact nativePolynomialZero_naturality f.hom.hom.right

@[reassoc (attr := simp)]

theorem pairPolynomialZero_projection (A : QuasiCompactOpenPairs.{u}) :
    pairPolynomialZero.app A ≫ pairPolynomialProjection.app A = 𝟙 A := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · exact nativePolynomialZero_projection A.obj.obj.left
  · exact nativePolynomialZero_projection A.obj.obj.right

@[reassoc (attr := simp)]

theorem pairPlus_projection (A : QuasiCompactOpenPairs.{u}) :
    pairPlus.app A ≫ pairPolynomialProjection.app A = pairLaurentProjection.app A := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · exact baseProductTransformation_projection _ _ _
      (PolynomialLaurent.laurentPlus_projection integerRing) A.obj.obj.left
  · exact baseProductTransformation_projection _ _ _
      (PolynomialLaurent.laurentPlus_projection integerRing) A.obj.obj.right

@[reassoc (attr := simp)]

theorem pairMinus_projection (A : QuasiCompactOpenPairs.{u}) :
    pairMinus.app A ≫ pairPolynomialProjection.app A = pairLaurentProjection.app A := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · exact baseProductTransformation_projection _ _ _
      (PolynomialLaurent.laurentMinus_projection integerRing) A.obj.obj.left
  · exact baseProductTransformation_projection _ _ _
      (PolynomialLaurent.laurentMinus_projection integerRing) A.obj.obj.right

@[simp]

theorem pairPolynomialZero_base (A : QuasiCompactOpenPairs.{u}) :
    quasiCompactOpenPairsBase.map (pairPolynomialZero.app A) =
      polynomialZero.app (quasiCompactOpenPairsBase.obj A) := rfl

@[simp]

theorem pairPolynomialProjection_base (A : QuasiCompactOpenPairs.{u}) :
    quasiCompactOpenPairsBase.map (pairPolynomialProjection.app A) =
      polynomialProjection.app (quasiCompactOpenPairsBase.obj A) := rfl

end AlgebraicGeometry.Scheme.Bass
