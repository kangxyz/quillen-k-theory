/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnit

/-!
# The actual bounded-flat affine Bass transition

The original Laurent-unit track and the original cone nullhomotopy define a parameter-correct
one-step transition. Coefficient compatibility and coherent iteration are further assertions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- The actual Laurent scalar gives the original bounded-flat Laurent-unit self-homotopy. -/
def boundedFlatLaurentUnitHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection R))
      (boundedFlatPerfectPrespectrumMap (laurentProjection R)) :=
  boundedFlatPerfectUnitHomotopy (laurentProjection R) (laurentGlobalUnit R)

/--
The parameter-correct desuspended actual square cone for this affine polynomial/Laurent diagram.
-/
def boundedFlatAffineBassStep (R : CommRingCat.{u}) : LoopPrespectrum :=
  parameterLooping (mappingCone (boundedFlatBassSquareComparison R))

/-- The source leg into the polynomial-chart homotopy pushout, using original bounded-flat
      pullback. -/
def boundedFlatBassSourceLeg (R : CommRingCat.{u}) :
    originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R)) ⟶
      HomotopyPushout.prespectrum (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) :=
  boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫ HomotopyPushout.inl _ _

lemma boundedFlatBassSourceLeg_comparison (R : CommRingCat.{u}) :
    boundedFlatBassSourceLeg R ≫ boundedFlatBassSquareComparison R =
      boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus R) := by
  unfold boundedFlatBassSourceLeg boundedFlatBassSquareComparison
  rw [Category.assoc, HomotopyPushout.inl_desc]

/-- The original Laurent map becomes genuinely null after the actual square-cone inclusion. -/
def boundedFlatBassLaurentNullHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection R) ≫ mappingConeInclusion
      (boundedFlatBassSquareComparison R))
      (zeroHom (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R)))
        (mappingCone (boundedFlatBassSquareComparison R))) := by
  have N := Homotopy.precomp (boundedFlatBassSourceLeg R) (mappingConeHomotopy
      (boundedFlatBassSquareComparison R))
  change Homotopy ((boundedFlatBassSourceLeg R ≫ boundedFlatBassSquareComparison R) ≫
    mappingConeInclusion (boundedFlatBassSquareComparison R)) (zeroHom _ _) at N
  rw [boundedFlatBassSourceLeg_comparison] at N
  exact ((boundedFlatLaurentPlusHomotopy R).postcomp (mappingConeInclusion
      (boundedFlatBassSquareComparison R))).trans N

/-- The actual affine Bass transition: conjugate the Laurent-unit loop by the original cone
  nullhomotopy.
The target uses the proved parameter-correct loop structure. -/
def boundedFlatAffineBassTransition (R : CommRingCat.{u}) :
    originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R)) ⟶ boundedFlatAffineBassStep R :=
  ((boundedFlatLaurentUnitHomotopy R).postcomp (mappingConeInclusion
      (boundedFlatBassSquareComparison R))).nullLoopMap
    (boundedFlatBassLaurentNullHomotopy R)

/--
The whole original transition loop retains its supplied Laurent action and both nullhomotopy legs.
-/
theorem boundedFlatAffineBassTransition_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) (s : unitInterval) :
    Path.toContinuousMap ((boundedFlatAffineBassTransition R).map n x) s =
      (((boundedFlatLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion (boundedFlatBassSquareComparison R))).conjugateToZero
          (boundedFlatBassLaurentNullHomotopy R)).level n (s, x) := rfl


/-- The inverse Laurent scalar used in this transition is the literal inverse coordinate. -/
lemma boundedFlatLaurentUnit_inverse_coordinate (R : CommRingCat.{u}) :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom (↑(laurentGlobalUnit R)⁻¹) =
      LaurentPolynomial.T (-1) := by
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.T (-1))) = _
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv_hom_id _

end Quillen.PerfectComplexes
