/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.Square
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionDiagram
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare

/-!
# Original fixed-open coefficient diagram consumers

Every coefficient object uses its fixed pullback of the original open. Consumers retain both
literal lift projections, the actual identity-base-change isomorphism, the unchanged original
supported map and the positive/inverse Laurent legs over the fixed base ring.
-/
@[expose] public section

open Quillen.PerfectComplexes


open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace QuillenTest.SupportedSectionDiagram

open Quillen
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

omit [IsOpenImmersion j] in
/-- The original pullback lift retains both its original open and coefficient projections. -/
theorem original_lift_projections {a b : Under R} (f : a ⟶ b) :
    openMap j f ≫ projection j a = projection j b ∧
      openMap j f ≫ inclusion j a = inclusion j b ≫ Spec.map f.right :=
  ⟨openMap_projection j f, openMap_inclusion j f⟩

/-- Composites have the identical chosen endpoints, with no iterated-pullback identification. -/
theorem original_fixed_endpoint_composition {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c) :
    openMap j (f ≫ g) = openMap j g ≫ openMap j f :=
  openMap_comp j f g

omit [IsOpenImmersion j] in
/-- The identity-algebra comparison is the actual projection iso, with its genuine inverse. -/
theorem original_identity_projection :
    (identityProjectionIso j).inv ≫ projection j (Under.mk (𝟙 R)) = 𝟙 U ∧
      (identityProjectionIso j).hom ≫ j = inclusion j (Under.mk (𝟙 R)) :=
  ⟨(identityProjectionIso j).inv_hom_id, identityProjectionIso_inclusion j⟩

/-- The actual diagram arrow retains the unchanged original supported coefficient map on points.
-/
theorem original_supported_diagram_value {a b : Under R} (f : a ⟶ b) (n : ℕ)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).map f).map n x =
      (boundedFlatAffineSupportedSectionPrespectrumMap (inclusion j a) (inclusion j b)
        f.right (openMap j f) (openMap_inclusion j f)).map n x := rfl

/-- Forgetting the fixed-base structure retains the entire original four-corner Laurent square.
-/
theorem original_laurent_square (a : Under R) :
    (Under.forget R).mapArrow.mapArrow.obj (laurentUnderSquare R a) =
      laurentSquare a.right :=
  laurentUnderSquare_forget R a

/-- Both unchanged Laurent legs have the same original coefficient composite in Under R. -/
theorem original_two_laurent_composites (a : Under R) :
    (polynomialUnderCoefficient R).app a ≫ (underToLaurent R).app a =
        (laurentUnderCoefficient R).app a ∧
      (polynomialUnderCoefficient R).app a ≫ (underToLaurentInvert R).app a =
        (laurentUnderCoefficient R).app a :=
  ⟨polynomialUnderCoefficient_toLaurent R a, polynomialUnderCoefficient_toLaurentInvert R a⟩

/-- The inverse-coordinate leg retains the original invert-after-toLaurent ring homomorphism. -/
theorem original_inverse_coordinate_leg (a : Under R) :
    ((underToLaurentInvert R).app a).right = CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) := rfl

end QuillenTest.SupportedSectionDiagram
