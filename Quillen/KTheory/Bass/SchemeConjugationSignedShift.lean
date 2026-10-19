/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeConjugationStableSign
public import Quillen.KTheory.Bass.GeometricConeDoubleBottomShift

/-!
# The second finite correction after its actual double signed shift

Both genuine parameter shifts transport the proved negative double-loop word
to the same unlooped geometric word. Its full equality transports remain in
`wordAt`; no action on a double cokernel is identified with a sign here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum.FiniteLoopWords
open Quillen.KTheory.Bass.GeometricConeFixedWords
open Quillen.KTheory.Bass.GeometricConeInterchange
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed

private theorem doubleShift_naturality {E G : LoopPrespectrum.{w}}
    (f : E ⟶ G) (d : ℤ) :
    (stableHomotopyFunctor d).map (parameterLoopingMap (parameterLoopingMap f)) ≫
        (parameterStableHomotopyIso (parameterLooping G) d).hom ≫
        (parameterStableHomotopyIso G (d + 1)).hom =
      (parameterStableHomotopyIso (parameterLooping E) d).hom ≫
        (parameterStableHomotopyIso E (d + 1)).hom ≫
        (stableHomotopyFunctor ((d + 1) + 1)).map f := by
  rw [← Category.assoc, parameterStableHomotopyIso_naturality, Category.assoc,
    parameterStableHomotopyIso_naturality]

/-- The original second correction retains its negative geometric word after both shifts. -/
theorem conjugatingIso_two_signedShift (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    (stableHomotopyFunctor d).map ((conjugatingIso 2 F).hom.app X) ≫
        (doubleNormalizedShift F X d).hom =
      -((doubleNormalizedShift F X d).hom ≫
        (stableHomotopyFunctor ((d + 1) + 1)).map ((wordAt 2 F).hom.app X)) := by
  rw [conjugatingIso_two_stable, ← wordAt_two_hom, Preadditive.neg_comp]
  congr 1
  exact doubleShift_naturality ((wordAt 2 F).hom.app X) d

end Quillen.KTheory.Bass.SchemeNaturalSeed
