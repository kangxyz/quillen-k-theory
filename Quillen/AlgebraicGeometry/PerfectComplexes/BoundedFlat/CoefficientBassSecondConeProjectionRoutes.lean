/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSecondCoefficientProjection

/-! Exact original projection routes before parameter looping, for summand-wise descent. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassSecondConeProjectionRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The positive-chart cone composition route with the polynomial coefficient equality cast. -/
def plusComposition (a : Under R) :=
  (BassMWhole.coneComposition P ((polynomialUnderCoefficient R).app a)
    ((underToLaurent R).app a)).cast
      (congrArg (boundedFlatCoefficientBassConeMap P)
        (polynomialUnderCoefficient_toLaurent R a)) rfl

/-- The negative-chart cone composition route with the polynomial coefficient equality cast. -/
def minusComposition (a : Under R) :=
  (BassMWhole.coneComposition P ((polynomialUnderCoefficient R).app a)
    ((underToLaurentInvert R).app a)).cast
      (congrArg (boundedFlatCoefficientBassConeMap P)
        (polynomialUnderCoefficient_toLaurentInvert R a)) rfl

variable {a b : Under R} (u : a ⟶ b)

/-- The selected first-step composition tracks lift the literal naturality equation.
The reversed first track and the forward second track retain their original half clocks. -/
def naturalitySquare {M N : Under R ⥤ Under R} (α : M ⟶ N) :
    Homotopy
      (boundedFlatCoefficientBassConeMap P (α.app a) ≫
        boundedFlatCoefficientBassConeMap P (N.map u))
      (boundedFlatCoefficientBassConeMap P (M.map u) ≫
        boundedFlatCoefficientBassConeMap P (α.app b)) :=
  (BassMWhole.coneComposition P (α.app a) (N.map u)).symm.trans
    ((BassMWhole.coneComposition P (M.map u) (α.app b)).cast
      (congrArg (boundedFlatCoefficientBassConeMap P) (α.naturality u)) rfl)

/-- The actual polynomial leg square at the first raw stage. -/
def polynomialSquare := naturalitySquare P u (polynomialUnderCoefficient R)

/-- The positive Laurent chart square at the first raw stage. -/
def plusSquare := naturalitySquare P u (underToLaurent R)

/-- The inverse Laurent chart has its own unchanged coefficient square. -/
def minusSquare := naturalitySquare P u (underToLaurentInvert R)

/-- Both chart pastings use this same literal Laurent-projection square. -/
def laurentSquare := naturalitySquare P u (laurentUnderCoefficient R)

/-- The polynomial span map exists before the missing Laurent comparison is filled. -/
def spanMap := HomotopyPushout.mapOfHomotopies
  (boundedFlatCoefficientBassConeMap P ((polynomialUnderCoefficient R).app a))
  (boundedFlatCoefficientBassConeMap P ((polynomialUnderCoefficient R).app a))
  (boundedFlatCoefficientBassConeMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatCoefficientBassConeMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatCoefficientBassConeMap P u)
  (boundedFlatCoefficientBassConeMap P ((polynomialUnderFunctor R).map u))
  (boundedFlatCoefficientBassConeMap P ((polynomialUnderFunctor R).map u))
  (polynomialSquare P u) (polynomialSquare P u)

/-- The positive route first crosses its chart square, then the polynomial square. -/
def plusLeft :=
  ((Homotopy.precomp
    (boundedFlatCoefficientBassConeMap P ((polynomialUnderCoefficient R).app a))
    (plusSquare P u)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((polynomialSquare P u).postcomp
      (boundedFlatCoefficientBassConeMap P ((underToLaurent R).app b)))

/-- The positive comparison retains the fixed second-object chart tracks and their casts. -/
def plusRight :=
  ((plusComposition P a).postcomp
    (boundedFlatCoefficientBassConeMap P ((laurentUnderFunctor R).map u))).symm.trans
    ((laurentSquare P u).trans
      ((Homotopy.precomp (boundedFlatCoefficientBassConeMap P u)
        (plusComposition P b)).cast
          rfl (Category.assoc _ _ _).symm))

/-- The inverse route uses the distinct inverse chart square, with the same polynomial leg. -/
def minusLeft :=
  ((Homotopy.precomp
    (boundedFlatCoefficientBassConeMap P ((polynomialUnderCoefficient R).app a))
    (minusSquare P u)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((polynomialSquare P u).postcomp
      (boundedFlatCoefficientBassConeMap P ((underToLaurentInvert R).app b)))

/-- The inverse comparison retains the original fixed inverse composition and common square. -/
def minusRight :=
  ((minusComposition P a).postcomp
    (boundedFlatCoefficientBassConeMap P ((laurentUnderFunctor R).map u))).symm.trans
    ((laurentSquare P u).trans
      ((Homotopy.precomp (boundedFlatCoefficientBassConeMap P u)
        (minusComposition P b)).cast
          rfl (Category.assoc _ _ _).symm))

private theorem trans_eval {E F E' F' : LoopPrespectrum.{u}}
    {f g h : E ⟶ F} {f' g' h' : E' ⟶ F'}
    (H : Homotopy f g) (K : Homotopy g h)
    (H' : Homotopy f' g') (K' : Homotopy g' h') (n : ℕ)
    {T : Type v} (φ : F.space n → T) (ψ : F'.space n → T)
    (x : E.space n) (x' : E'.space n)
    (hH : ∀ r, φ (H.level n (r, x)) = ψ (H'.level n (r, x')))
    (hK : ∀ r, φ (K.level n (r, x)) = ψ (K'.level n (r, x'))) (r : I) :
    φ ((H.trans K).level n (r, x)) = ψ ((H'.trans K').level n (r, x')) := by
  change φ (((H.levelHomotopy n).trans (K.levelHomotopy n)) (r, x)) =
    ψ (((H'.levelHomotopy n).trans (K'.levelHomotopy n)) (r, x'))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _

theorem naturalitySquare_native {M N : Under R ⥤ Under R} (α : M ⟶ N)
    (n : ℕ) (r s : I) (x : (boundedFlatCoefficientBassStep P (M.obj a)).space n) :
    Path.toContinuousMap
      ((CoefficientBassSecondCoefficientProjection.naturalitySquare P u α).level n (r, x)) s =
      (naturalitySquare P u α).level n (r, Path.toContinuousMap x s) := by
  unfold CoefficientBassSecondCoefficientProjection.naturalitySquare naturalitySquare
  exact trans_eval _ _ _ _ n (fun y : (boundedFlatCoefficientBassStep P (N.obj b)).space n ↦
      Path.toContinuousMap y s) id x (x.toContinuousMap s)
    (fun _ ↦ rfl) (fun _ ↦ rfl) r

theorem plusLeft_native (n : ℕ) (r s : I)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    Path.toContinuousMap
      ((CoefficientBassSecondCoefficientProjection.plusLeft P u).level n (r, x)) s =
      (plusLeft P u).level n (r, Path.toContinuousMap x s) := by
  unfold CoefficientBassSecondCoefficientProjection.plusLeft plusLeft
  apply trans_eval _ _ _ _ n
      (fun y : (boundedFlatCoefficientBassStep P ((laurentUnderFunctor R).obj b)).space n ↦
      Path.toContinuousMap y s) id x (x.toContinuousMap s)
  · intro t
    exact naturalitySquare_native P u (underToLaurent R) n t s
      ((boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a)).map n x)
  · intro t
    exact congrArg
      ((boundedFlatCoefficientBassConeMap P ((underToLaurent R).app b)).map n)
      (naturalitySquare_native P u (polynomialUnderCoefficient R) n t s x)

theorem plusRight_native (n : ℕ) (r s : I)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    Path.toContinuousMap
      ((CoefficientBassSecondCoefficientProjection.plusRight P u).level n (r, x)) s =
      (plusRight P u).level n (r, Path.toContinuousMap x s) := by
  unfold CoefficientBassSecondCoefficientProjection.plusRight plusRight
  apply trans_eval _ _ _ _ n
      (fun y : (boundedFlatCoefficientBassStep P ((laurentUnderFunctor R).obj b)).space n ↦
      Path.toContinuousMap y s) id x (x.toContinuousMap s)
  · intro t
    rfl
  · intro t
    apply trans_eval _ _ _ _ n
      (fun y : (boundedFlatCoefficientBassStep P ((laurentUnderFunctor R).obj b)).space n ↦
      Path.toContinuousMap y s) id x (x.toContinuousMap s)
    · intro v
      exact naturalitySquare_native P u (laurentUnderCoefficient R) n v s x
    · intro v
      rfl

theorem minusLeft_native (n : ℕ) (r s : I)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    Path.toContinuousMap
      ((CoefficientBassSecondCoefficientProjection.minusLeft P u).level n (r, x)) s =
      (minusLeft P u).level n (r, Path.toContinuousMap x s) := by
  unfold CoefficientBassSecondCoefficientProjection.minusLeft minusLeft
  apply trans_eval _ _ _ _ n
      (fun y : (boundedFlatCoefficientBassStep P ((laurentUnderFunctor R).obj b)).space n ↦
      Path.toContinuousMap y s) id x (x.toContinuousMap s)
  · intro t
    exact naturalitySquare_native P u (underToLaurentInvert R) n t s
      ((boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a)).map n x)
  · intro t
    exact congrArg
      ((boundedFlatCoefficientBassConeMap P ((underToLaurentInvert R).app b)).map n)
      (naturalitySquare_native P u (polynomialUnderCoefficient R) n t s x)

theorem minusRight_native (n : ℕ) (r s : I)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    Path.toContinuousMap
      ((CoefficientBassSecondCoefficientProjection.minusRight P u).level n (r, x)) s =
      (minusRight P u).level n (r, Path.toContinuousMap x s) := by
  unfold CoefficientBassSecondCoefficientProjection.minusRight minusRight
  apply trans_eval _ _ _ _ n
      (fun y : (boundedFlatCoefficientBassStep P ((laurentUnderFunctor R).obj b)).space n ↦
      Path.toContinuousMap y s) id x (x.toContinuousMap s)
  · intro t
    rfl
  · intro t
    apply trans_eval _ _ _ _ n
      (fun y : (boundedFlatCoefficientBassStep P ((laurentUnderFunctor R).obj b)).space n ↦
      Path.toContinuousMap y s) id x (x.toContinuousMap s)
    · intro v
      exact naturalitySquare_native P u (laurentUnderCoefficient R) n v s x
    · intro v
      rfl

end Quillen.PerfectComplexes.CoefficientBassSecondConeProjectionRoutes
