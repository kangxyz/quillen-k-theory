/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MChartSideRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareFiveSimplex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareReferenceCancellation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0PolynomialMovement

/-! Exact normalization of the original polynomial moving-side reference before cancellation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1PolynomialSourceReference
open BassReferenceMerge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The actual outer polynomial square, with its original association and naturality proofs. -/
theorem outer_square :
    polynomialProjection P c ≫ (coefficientMap P q ≫ coefficientMap P p) =
      (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
        coefficientMap P ((polynomialUnderFunctor R).map p)) ≫ polynomialProjection P a :=
  (DoubleSquareTrack.total_eq (coefficientMap P p) (coefficientMap P q)
    (coefficientMap P ((polynomialUnderFunctor R).map p))
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
    (coefficientMap_naturality P (polynomialUnderCoefficient R) p).symm
    (coefficientMap_naturality P (polynomialUnderCoefficient R) q).symm).symm

/-- The entire side reference is its actual outer-square transport followed by the binary total. -/
theorem moving_side_reference :
    BassMOuterJoin.movingSideBaseIso P p q =
      NativeSquareFiveSimplex.sourceIso (polynomialProjection P c)
        (coefficientMap P q ≫ coefficientMap P p)
        (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
          coefficientMap P ((polynomialUnderFunctor R).map p))
        (polynomialProjection P a) (outer_square P p q) ≪≫
      BinaryNormalizationSimplex.total
        (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
          coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a) := by
  change smallIso (eqToIso _) ≪≫ smallIso (eqToIso _ ≪≫ _) =
    eqToIso _ ≪≫ smallIso _
  rw [smallIso_trans, smallIso_eqToIso, smallIso_eqToIso, ← Iso.trans_assoc, eqToIso_trans]


section Actual
open BassH0Merge CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierRails CoefficientBassPositiveC0PolynomialEndpoints
variable (d : Under R)

/-- The actual polynomial coefficient composite is transported to the unchanged direct arrow. -/
theorem actual_polynomial_composite :
    coefficientMap P ((polynomialUnderFunctor R).map ((underToLaurent R).app d)) ≫
      coefficientMap P ((polynomialUnderFunctor R).map ((polynomialUnderCoefficient R).app d)) =
    coefficientMap P ((polynomialUnderFunctor R).map ((laurentUnderCoefficient R).app d)) :=
  (polynomial_composite P ((polynomialUnderCoefficient R).app d)
    ((underToLaurent R).app d)).symm.trans
      (congrArg (fun w ↦ coefficientMap P ((polynomialUnderFunctor R).map w))
        (polynomialUnderCoefficient_toLaurent R d))

/-- The actual coefficient total retains its original direct-arrow equality transport. -/
theorem actual_coefficient_composite :
    coefficientMap P ((underToLaurent R).app d) ≫
      coefficientMap P ((polynomialUnderCoefficient R).app d) =
    coefficientMap P ((laurentUnderCoefficient R).app d) :=
  (coefficientMap_comp P ((polynomialUnderCoefficient R).app d)
    ((underToLaurent R).app d)).symm.trans
      (congrArg (coefficientMap P) (polynomialUnderCoefficient_toLaurent R d))

/-- Equality of the actual source model functors, used only with its full reference equation. -/
theorem initial_functor :
    (polynomialReference P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d)).functor =
    (CoefficientBassPositiveJ0PolynomialMovement.nodes P d 2).1.functor :=
  congrArg (fun f ↦ (normalizedMap (polynomialProjection P d) ≫ normalizedMap f).functor)
    (actual_polynomial_composite P d)

/-- The complete chosen source reference is precisely the induced actual source transport. -/
theorem initial_reference :
    (CoefficientBassPositiveJ0PolynomialMovement.nodes P d 2).2 =
      eqToIso (initial_functor P d) := by
  have h := NativeSquareReferenceCancellation.source_reference
    (coefficientMap P ((polynomialUnderFunctor R).map ((underToLaurent R).app d)) ≫
      coefficientMap P ((polynomialUnderFunctor R).map ((polynomialUnderCoefficient R).app d)))
    (coefficientMap P ((polynomialUnderFunctor R).map ((laurentUnderCoefficient R).app d)))
    (polynomialProjection P d) (polynomialProjection P ((laurentUnderFunctor R).obj d))
    (coefficientMap P ((underToLaurent R).app d) ≫
      coefficientMap P ((polynomialUnderCoefficient R).app d))
    (coefficientMap P ((laurentUnderCoefficient R).app d))
    (actual_polynomial_composite P d) (actual_coefficient_composite P d)
    (outer_square P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d))
    (coefficientMap_naturality P (polynomialUnderCoefficient R)
      ((laurentUnderCoefficient R).app d))
  rw [← moving_side_reference] at h
  simp only [← Iso.trans_assoc] at h
  change (CoefficientBassPositiveJ0PolynomialMovement.nodes P d 2).2 =
    eqToIso (initial_functor P d) at h
  exact h

private theorem reflexive_node_eq {V W : Model.{u}} {F : V ⟶ W}
    (N : Node F) (h : F.functor = N.1.functor) (he : N.2 = eqToIso h) :
    (⟨F, Iso.refl F.functor⟩ : Node F) = N := by
  rcases N with ⟨G, ρ⟩
  change ρ = eqToIso h at he
  apply ModelSimplex.reference_node_eq h
  simpa only [Iso.refl_hom, Category.id_comp, eqToIso.hom] using
    (congrArg Iso.hom he).symm

private theorem precomp_reflexive {V W T : Model.{u}} (J : T ⟶ V) (F : V ⟶ W) :
    precompNode J (⟨F, Iso.refl F.functor⟩ : Node F) =
      (⟨J ≫ F, Iso.refl (J ≫ F).functor⟩ : Node (J ≫ F)) := by
  change (⟨J ≫ F, isoWhiskerLeft J.functor (Iso.refl F.functor)⟩ : Node (J ≫ F)) = _
  rw [isoWhiskerLeft_refl]; rfl

/-- The original C1 polynomial source is the full actual old-cone input node and reference. -/
theorem polynomial_source_node :
    polynomialNodes P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) 0 =
      CoefficientBassPositiveJ0PolynomialMovement.nodes P d 2 := by
  change precompNode (BassOverlap.projectionMap P (a := d))
    (⟨BassMOuterJoin.sideBinarySource P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d), Iso.refl _⟩ : Node
        (BassMOuterJoin.sideBinarySource P ((polynomialUnderCoefficient R).app d)
          ((underToLaurent R).app d))) = _
  rw [precomp_reflexive]
  exact reflexive_node_eq (CoefficientBassPositiveJ0PolynomialMovement.nodes P d 2)
    (initial_functor P d) (initial_reference P d)

end Actual

end Quillen.PerfectComplexes.CoefficientBassPositiveC1PolynomialSourceReference
