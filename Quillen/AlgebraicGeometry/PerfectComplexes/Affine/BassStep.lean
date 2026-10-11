/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurent
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnit
public import Quillen.Topology.Prespectrum.HomotopyPushout

/-!
The actual affine polynomial/Laurent square and its parameter-correct cone transition, defined using
the original Laurent-unit track and original cone nullhomotopy. This is a one-step construction:
stable cone exactness, a functorial iterated Bass tower, the fundamental theorem and nonconnective
K-theory are separate claims.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum

open Quillen.Scheme.PolynomialLaurent

/-- The genuine Laurent-unit self-homotopy of the original flat geometric spectrum map. -/
def laurentUnitHomotopy (R : CommRingCat.{u}) :
    LoopPrespectrum.Homotopy (perfectFlatPrespectrumMap (laurentProjection R))
      (perfectFlatPrespectrumMap (laurentProjection R)) :=
  perfectFlatUnitHomotopy (laurentProjection R) (laurentGlobalUnit R)

/-- The positive polynomial leg is normalized against the literal Laurent coefficient map. -/
def laurentPlusHomotopy (R : CommRingCat.{u}) :
    Homotopy (perfectFlatPrespectrumMap (laurentProjection R))
      (perfectFlatPrespectrumMap (polynomialProjection R) ≫ perfectFlatPrespectrumMap (laurentPlus
        R)) := by
  have H := perfectFlatPrespectrumCompHomotopy (laurentPlus R) (polynomialProjection R)
  simpa only [laurentPlus_projection] using H

/-- The inverse-coordinate polynomial leg uses its actual geometric composition comparison. -/
def laurentMinusHomotopy (R : CommRingCat.{u}) :
    Homotopy (perfectFlatPrespectrumMap (laurentProjection R))
      (perfectFlatPrespectrumMap (polynomialProjection R) ≫ perfectFlatPrespectrumMap (laurentMinus
        R)) := by
  have H := perfectFlatPrespectrumCompHomotopy (laurentMinus R) (polynomialProjection R)
  simpa only [laurentMinus_projection] using H

/-- The actual polynomial/Laurent square carries a displayed whole-prespectrum homotopy. -/
def bassSquareHomotopy (R : CommRingCat.{u}) :
    Homotopy
      (perfectFlatPrespectrumMap (polynomialProjection R) ≫ perfectFlatPrespectrumMap (laurentPlus
        R))
      (perfectFlatPrespectrumMap (polynomialProjection R) ≫ perfectFlatPrespectrumMap (laurentMinus
        R)) :=
  (laurentPlusHomotopy R).symm.trans (laurentMinusHomotopy R)

/-- The literal double-cylinder comparison from the two polynomial corners to the Laurent corner. -/
def bassSquareComparison (R : CommRingCat.{u}) :
    HomotopyPushout.prespectrum (perfectFlatPrespectrumMap (polynomialProjection R))
      (perfectFlatPrespectrumMap (polynomialProjection R)) ⟶
      originalPrespectrum (perfectWaldhausen (Spec (.of (LaurentPolynomial R)))) :=
  HomotopyPushout.desc _ _ (perfectFlatPrespectrumMap (laurentPlus R))
    (perfectFlatPrespectrumMap (laurentMinus R)) (bassSquareHomotopy R)

/--
The parameter-correct desuspended actual square cone for this affine polynomial/Laurent diagram.
-/
def affineBassStep (R : CommRingCat.{u}) : LoopPrespectrum :=
  parameterLooping (mappingCone (bassSquareComparison R))

/-- The source leg into the polynomial-chart homotopy pushout, using original flat pullback. -/
def bassSourceLeg (R : CommRingCat.{u}) :
    originalPrespectrum (perfectWaldhausen (Spec R)) ⟶
      HomotopyPushout.prespectrum (perfectFlatPrespectrumMap (polynomialProjection R))
        (perfectFlatPrespectrumMap (polynomialProjection R)) :=
  perfectFlatPrespectrumMap (polynomialProjection R) ≫ HomotopyPushout.inl _ _

lemma bassSourceLeg_comparison (R : CommRingCat.{u}) :
    bassSourceLeg R ≫ bassSquareComparison R =
      perfectFlatPrespectrumMap (polynomialProjection R) ≫ perfectFlatPrespectrumMap (laurentPlus R)
        := by
  unfold bassSourceLeg bassSquareComparison
  rw [Category.assoc, HomotopyPushout.inl_desc]

/-- The original Laurent map becomes genuinely null after the actual square-cone inclusion. -/
def bassLaurentNullHomotopy (R : CommRingCat.{u}) :
    Homotopy (perfectFlatPrespectrumMap (laurentProjection R) ≫ mappingConeInclusion
      (bassSquareComparison R))
      (zeroHom (originalPrespectrum (perfectWaldhausen (Spec R))) (mappingCone (bassSquareComparison
        R))) := by
  have N := Homotopy.precomp (bassSourceLeg R) (mappingConeHomotopy (bassSquareComparison R))
  change Homotopy ((bassSourceLeg R ≫ bassSquareComparison R) ≫ mappingConeInclusion
    (bassSquareComparison R))
    (zeroHom _ _) at N
  rw [bassSourceLeg_comparison] at N
  exact ((laurentPlusHomotopy R).postcomp (mappingConeInclusion (bassSquareComparison R))).trans N

/-- The actual affine Bass transition: conjugate the Laurent-unit loop by the original cone
  nullhomotopy.
The target uses the proved parameter-correct loop structure. -/
def affineBassTransition (R : CommRingCat.{u}) :
    originalPrespectrum (perfectWaldhausen (Spec R)) ⟶ affineBassStep R :=
  ((laurentUnitHomotopy R).postcomp (mappingConeInclusion (bassSquareComparison R))).nullLoopMap
    (bassLaurentNullHomotopy R)

/--
The whole original transition loop retains its supplied Laurent action and both nullhomotopy legs.
-/
theorem affineBassTransition_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : (originalPrespectrum (perfectWaldhausen (Spec R))).space n) (s : unitInterval) :
    Path.toContinuousMap ((affineBassTransition R).map n x) s =
      (((laurentUnitHomotopy R).postcomp (mappingConeInclusion (bassSquareComparison
        R))).conjugateToZero
        (bassLaurentNullHomotopy R)).level n (s,x) := rfl


end Quillen.PerfectComplexes
