/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBassBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalUnitProjection

/-!
# The actual unit section of the original global Bass boundary

For every qcqs base the original global Phi coordinates retain the unchanged native
Mayer–Vietoris boundary. The original forward and inverse unit computations supply the literal
inverse-unit section in every connective degree, retaining the actual forward inversion sign.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Waldhausen.Additivity.KCommGroup
variable (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj]

/-- The original forward-unit boundary is inversion, retaining the raw seed's actual sign. -/
theorem positiveBassBoundary_comp_forwardUnit (n : ℕ) :
    (positiveBassBoundary X n).comp
      (originalKSelfTrackOperation (perfectWaldhausen X.obj)
        (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
        (perfectFlatUnitHomotopy (Relative.laurentProjection.app X).hom (laurentGlobalUnit X)) n) =
      invMonoidHom := by
  ext a
  have h := DFunLike.congr_fun
    (projectiveConnecting_comp_forwardProjection_allDegrees X n) a
  change projectiveConnecting X n
    (originalKSelfTrackOperation (perfectWaldhausen X.obj)
      (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
      (perfectFlatUnitHomotopy (Relative.laurentProjection.app X).hom (laurentGlobalUnit X)) n a) =
      nativeTwoSummandKMap X n (a⁻¹, a) at h
  change ((nativeGlobalTwoSummandKEquiv X n).symm
    (projectiveConnecting X n _)).1 = a⁻¹
  rw [h]
  exact congrArg Prod.fst ((nativeGlobalTwoSummandKEquiv X n).symm_apply_apply (a⁻¹, a))

/-- The literal inverse-Laurent-unit section in every original connective degree. -/
def positiveBassUnitSection (n : ℕ) :
    PerfectK X.obj n →* PerfectK (Relative.laurentFunctor.obj X).obj (n + 1) :=
  originalKSelfTrackOperation (perfectWaldhausen X.obj)
    (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
    (perfectFlatUnitHomotopy (Relative.laurentProjection.app X).hom (laurentGlobalUnit X)⁻¹) n

/-- The actual inverse unit is a right inverse of the unchanged original Bass boundary. -/
theorem positiveBassBoundary_comp_unitSection (n : ℕ) :
    (positiveBassBoundary X n).comp (positiveBassUnitSection X n) =
      MonoidHom.id (PerfectK X.obj n) := by
  ext a
  have h := DFunLike.congr_fun
    (projectiveConnecting_comp_inverseProjection_allDegrees X n) a
  change projectiveConnecting X n (positiveBassUnitSection X n a) =
    nativeTwoSummandKMap X n (a, a⁻¹) at h
  change ((nativeGlobalTwoSummandKEquiv X n).symm
    (projectiveConnecting X n (positiveBassUnitSection X n a))).1 = a
  rw [h]
  exact congrArg Prod.fst ((nativeGlobalTwoSummandKEquiv X n).symm_apply_apply (a, a⁻¹))

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
