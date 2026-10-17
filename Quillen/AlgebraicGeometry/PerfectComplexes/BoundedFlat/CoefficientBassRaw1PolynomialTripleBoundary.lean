/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleRoutes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleBottomEdges
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleSheet
public import Quillen.Topology.Realization.SimplexCubeFaces

/-! The six prescribed polynomial cap faces and their whole intersections. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleBoundary
open CoefficientBassRaw1PolynomialTripleRoutes CoefficientBassRaw1PolynomialTripleBottomEdges
open Quillen.SimplexCubeExtension
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The original left route has exactly the prescribed split-triple bottom. -/
theorem left_bottom (negative : Bool) (r : I) : left P p q w negative (r, 0) =
    CoefficientBassRaw1PolynomialTripleBottom.family P (chartChoice negative) p q w (0, r) := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover r
  · exact (ScalarRectangle.concatFirst_lower _ _ _ t 0).trans
      (family_zero_lower P (chartChoice negative) p q w t).symm
  · have h := ScalarRectangle.concatFirst_upper
      (CoefficientBassRaw1PolynomialRadialCaps.left P (chartChoice negative) p q w)
      (postCap P p q w negative) (left_join P p q w negative) t 0
    refine h.trans ?_
    cases negative
    · exact (family_zero_upper_plus P p q w t).symm
    · exact (family_zero_upper_minus P p q w t).symm

/-- The original right route has exactly the other prescribed split-triple bottom. -/
theorem right_bottom (negative : Bool) (r : I) : right P p q w negative (r, 0) =
    CoefficientBassRaw1PolynomialTripleBottom.family P (chartChoice negative) p q w (1, r) := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover r
  · exact (ScalarRectangle.concatFirst_lower _ _ _ t 0).trans
      (family_one_lower P (chartChoice negative) p q w t).symm
  · exact (ScalarRectangle.concatFirst_upper _ _ _ t 0).trans
      (family_one_upper P (chartChoice negative) p q w t).symm

namespace FaceGluing
variable {X : Type*} [TopologicalSpace X]

/-- Coordinates of the actual closed cube faces. -/
def faces (L R B : C(I × I, X)) (tip : X) (a : Fin 3 × Bool) : C(face a, X) :=
  if a.1 = 0 then
    ⟨fun z ↦ (if a.2 then R else L) (z.val.val 1, z.val.val 2),
      (if a.2 then R else L).continuous.comp
        (((continuous_apply 1).comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_apply 2).comp (continuous_subtype_val.comp continuous_subtype_val)))⟩
  else if a.1 = 1 then
    ⟨fun z ↦ L (endpoint a.2, z.val.val 2), L.continuous.comp
      (continuous_const.prodMk
        ((continuous_apply 2).comp (continuous_subtype_val.comp continuous_subtype_val)))⟩
  else if a.2 then ContinuousMap.const _ tip
  else ⟨fun z ↦ B (z.val.val 0, z.val.val 1), B.continuous.comp
    (((continuous_apply 0).comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
      ((continuous_apply 1).comp (continuous_subtype_val.comp continuous_subtype_val)))⟩

/-- The twelve edge equations suffice for this fixed six-face presentation. -/
theorem compatible (L R B : C(I × I, X)) (tip : X)
    (h0 : ∀ s, L (0, s) = R (0, s)) (h1 : ∀ s, L (1, s) = R (1, s))
    (hl : ∀ r, L (r, 0) = B (0, r)) (hr : ∀ r, R (r, 0) = B (1, r))
    (hlt : ∀ r, L (r, 1) = tip) (hrt : ∀ r, R (r, 1) = tip)
    (hs : ∀ r, L (0, 0) = B (r, 0)) (ht : ∀ r, L (1, 0) = B (r, 1)) :
    EdgeCompatible (fun a ↦ faces L R B tip a) := by
  intro i j hij a b x hi hj
  change x.val i = endpoint a at hi
  change x.val j = endpoint b at hj
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    cases a <;> cases b <;>
      simp only [endpoint, Bool.false_eq_true, ↓reduceIte] at hi hj
  all_goals
    dsimp [faces, endpoint]
    simp_all only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  all_goals first
    | rfl
    | exact (h0 _).symm
    | exact (h1 _).symm
    | exact hl _
    | exact hr _
    | exact hlt _
    | exact hrt _
    | exact hs _
    | exact ht _
end FaceGluing

/-- Six actual faces retain the old cap routes, whole endpoint words, Laurent bottom and tip. -/
def faces (negative : Bool) := FaceGluing.faces
  (left P p q w negative) (right P p q w negative)
  (CoefficientBassRaw1PolynomialTripleBottom.family P (chartChoice negative) p q w)
  (CoefficientBassRaw1PolynomialPostcomp.tip P p q w (chartChoice negative))

/-- Every geometric edge agrees on its complete original scalar values. -/
theorem compatible (negative : Bool) : EdgeCompatible (fun a ↦ faces P p q w negative a) := by
  apply FaceGluing.compatible
  · exact start P p q w negative
  · exact finish P p q w negative
  · exact left_bottom P p q w negative
  · exact right_bottom P p q w negative
  · exact left_top P p q w negative
  · exact right_top P p q w negative
  · intro r
    exact (left_bottom P p q w negative 0).trans
      ((CoefficientBassRaw1PolynomialTripleBottom.family_source
        P (chartChoice negative) p q w 0).trans
        (CoefficientBassRaw1PolynomialTripleBottom.family_source
          P (chartChoice negative) p q w r).symm)
  · intro r
    exact (left_bottom P p q w negative 1).trans
      ((CoefficientBassRaw1PolynomialTripleBottom.family_target
        P (chartChoice negative) p q w 0).trans
        (CoefficientBassRaw1PolynomialTripleBottom.family_target
          P (chartChoice negative) p q w r).symm)

/-- Closed-cover gluing changes no point of any prescribed face. -/
def boundary (negative : Bool) : C(Quillen.SimplexCubeExtension.boundary,
    CoefficientBassRaw1PolynomialPostcomp.carrier P p q w (chartChoice negative)) :=
  glueClosedCover face isClosed_face faces_cover (faces P p q w negative)
    (edgeCompatible_pairwise _ (compatible P p q w negative))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleBoundary
