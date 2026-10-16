/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNervePolynomialInitialFace

/-!
# The initial polynomial e0 face is the old postcomposed first-stage M face

The scalar square here is the original moving square at pause time zero. It is not the
paused terminal square. Every reference equality precedes the three-support transfer.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve.PolynomialInitialClients
open BassReferenceMerge BassH0Merge BassH1Join

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Strict named consumer of the complete original equality. -/
theorem client_polynomial_initial_anchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    polynomialFixedSideAnchor P u v w α hc 0 =
      postcompAnchor P u v w ≪≫ isoWhiskerRight (BassMReferences.movingIso P u v α hc)
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor := by
  exact BassMWholeNerve.polynomial_initial_anchor P u v w α hc

/-- Strict named consumer of the complete original equality. -/
theorem client_polynomial_initial_reference_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (i : Fin 18) :
    polynomialOuterNodes P u v w α hc 0 i =
      anchorNode (postcompAnchor P u v w)
        (CommonReferenceNerve.postcompNode
          (coefficientModel P ((laurentUnderFunctor R).map w))
          (BassMReferences.movingNodes P u v α hc i)) := by
  exact BassMWholeNerve.polynomial_initial_reference_nodes P u v w α hc i

/-- Strict named consumer of the complete original equality. -/
theorem client_initial_polynomial_plus_nodes (i : Fin 18) :
    postcompNodes P u v w (initialPolynomialIndex false i) =
      polynomialOuterNodes P u v w (underToLaurent R) (laurentPlus_projection P c) 0 i := by
  exact BassMWholeNerve.initial_polynomial_plus_nodes P u v w i

/-- Strict named consumer of the complete original equality. -/
theorem client_initial_polynomial_minus_nodes (i : Fin 18) :
    postcompNodes P u v w (initialPolynomialIndex true i) =
      polynomialOuterNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P c) 0 i := by
  exact BassMWholeNerve.initial_polynomial_minus_nodes P u v w i

/-- Strict named consumer of the complete original equality. -/
theorem client_polynomial_outer_initial_plus (q t : unitInterval) :
    polynomialOuterSurface P u v w (underToLaurent R) (laurentPlus_projection P c) 0
      ![0, q, t] = postcompLift P u v w ![lower q, 1, lower t] := by
  exact BassMWholeNerve.polynomial_outer_initial_plus P u v w q t

/-- Strict named consumer of the complete original equality. -/
theorem client_polynomial_outer_initial_minus (q t : unitInterval) :
    polynomialOuterSurface P u v w (underToLaurentInvert R) (laurentMinus_projection P c) 0
      ![0, q, unitInterval.symm t] = postcompLift P u v w ![lower q, 1, upper (upper t)] := by
  exact BassMWholeNerve.polynomial_outer_initial_minus P u v w q t

/-- The physical original product face retains its inverse coordinate and old cube speed. -/
theorem client_polynomial_pause_initial_plus (q t : unitInterval) :
    polynomialPause P u v w (underToLaurent R) (laurentPlus_projection P c) false ![0, q, 0, t] =
      postcompLift P u v w ![lower q, 1, lower t] := by
  have h := polynomial_pause_outer_face P u v w (underToLaurent R)
    (laurentPlus_projection P c) false 0 0 q t
  exact h.trans (polynomial_outer_initial_plus P u v w q t)

/-- The physical original product face retains its inverse coordinate and old cube speed. -/
theorem client_polynomial_pause_initial_minus (q t : unitInterval) :
    polynomialPause P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      true ![0, q, 0, t] =
      postcompLift P u v w ![lower q, 1, upper (upper t)] := by
  have h := polynomial_pause_outer_face P u v w (underToLaurentInvert R)
    (laurentMinus_projection P c) true 0 0 q t
  exact h.trans (polynomial_outer_initial_minus P u v w q t)

end Quillen.PerfectComplexes.BassMWholeNerve.PolynomialInitialClients
