/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeCoefficientSeedNaturality
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseSpecSquare

/-!
# Affine specialization of the original Scheme-to-coefficient seed square

The actual affine four-corner index isomorphism and an arbitrary complete coefficient
diagram map form the exact square-map type used by the geometric unit consumer.
Only the stated same-time original scalar compatibility is assumed here.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open Quillen.KTheory.Bass
open NaturalTrack GeometricSeedCospan SchemeCoefficientSeedNaturality
universe u w

example {F : Scheme.{u}ᵒᵖ ⥤ Quillen.LoopPrespectrum.{w}}
    {G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ Quillen.LoopPrespectrum.{w}}
    (A : Track laurent.op coefficient F) (B : LaurentSeed.Track G)
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (hU : ∀ n r x,
      (F.mapArrow.mapArrow.map (specSquareIso a).hom ≫
        diagramSquareMap ρ (laurentUnderSquare _ a)).right.right.map n
          ((A.homotopy (specUnder.obj a)).level n (r, x)) =
        (B.homotopy a).level n
          (r, (F.mapArrow.mapArrow.map (specSquareIso a).hom ≫
            diagramSquareMap ρ (laurentUnderSquare _ a)).left.left.map n x)) :
    (SchemeNaturalSeed.seed A).app (specUnder.obj a) ≫
        strictSquareLoopedConeFunctor.map
          (F.mapArrow.mapArrow.map (specSquareIso a).hom ≫
            diagramSquareMap ρ (laurentUnderSquare _ a)) =
      (F.mapArrow.mapArrow.map (specSquareIso a).hom ≫
        diagramSquareMap ρ (laurentUnderSquare _ a)).left.left ≫ B.seed.app a :=
  seed_naturality A B (specUnder.obj a) a _ hU
