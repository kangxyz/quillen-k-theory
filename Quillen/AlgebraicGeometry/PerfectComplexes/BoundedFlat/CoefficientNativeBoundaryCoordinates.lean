/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientNativeUnitOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalUnitProjection

/-!
# Global boundary coordinates of the actual coefficient Laurent operations

The chosen Laurent-fiber inverse and the actual bounded-flat inclusion transport the original
projective boundary back to the original coefficient K-group. Both original Laurent operations
have their global Phi coordinates in every nonnegative degree on every qcqs coefficient row.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.ProjectiveLine Quillen.PerfectComplexes.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.NativeBass
universe u
namespace Quillen.PerfectComplexes

attribute [local instance] Waldhausen.Additivity.KCommGroup

private theorem boundedFlatPullback_inv_hom {Y Z : Scheme.{u}} (e : Y ≅ Z) (n : ℕ)
    (x : BoundedFlatPerfectK Z n) :
    boundedFlatPerfectKPullback e.inv n (boundedFlatPerfectKPullback e.hom n x) = x := by
  have h := congrArg (fun f => boundedFlatPerfectKPullback f n) e.inv_hom_id
  exact DFunLike.congr_fun ((boundedFlatPerfectKPullback_comp e.inv e.hom n).symm.trans
    (h.trans (boundedFlatPerfectKPullback_id Z n))) x

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left] (a : Under R)
local notation "X" => Opposite.unop (Functor.obj (boundedFlatCoefficientQuasiCompactRow P) a)
local instance coefficientBoundary_quasiSeparated : QuasiSeparatedSpace (X).obj :=
  quasiSeparatedSpace_space (op P, a)

/-- The unchanged global projective boundary on the actual chosen coefficient Laurent group. -/
def boundedFlatCoefficientNativeProjectiveBoundary (n : ℕ) :
    BoundedFlatPerfectK (space (op P, (laurentUnderFunctor R).obj a)) (n + 1) →*
      PerfectK (nativeLineFunctor.obj X).obj n :=
  (projectiveConnecting X n).comp
    ((boundedFlatPerfectToPerfectKMap (Relative.laurentFunctor.obj X).obj (n + 1)).comp
      (boundedFlatPerfectKPullback (laurentIso P a).inv (n + 1)))

/-- The complete original forward coefficient operation has the actual inverse/identity pair. -/
theorem boundedFlatCoefficientNativeBoundary_comp_forward (n : ℕ) :
    (boundedFlatCoefficientNativeProjectiveBoundary P a n).comp
      (boundedFlatCoefficientLaurentKOperation P a n) =
      ((nativeTwoSummandKMap X n).comp
        (invMonoidHom.prod (MonoidHom.id (PerfectK (X).obj n)))).comp
          (boundedFlatPerfectToPerfectKMap (space (op P, a)) n) := by
  ext x
  let z := originalKSelfTrackOperation (boundedFlatPerfectWaldhausen (X).obj)
    (boundedFlatPerfectWaldhausen (Relative.laurentFunctor.obj X).obj)
    (boundedFlatPerfectUnitHomotopy (Relative.laurentProjection.app X).hom
      (laurentGlobalUnit X)) n x
  have hu := DFunLike.congr_fun (boundedFlatCoefficientLaurentKOperation_native P a n) x
  have ht : boundedFlatPerfectKPullback (laurentIso P a).inv (n + 1)
      (boundedFlatCoefficientLaurentKOperation P a n x) = z :=
    (congrArg (boundedFlatPerfectKPullback (laurentIso P a).inv (n + 1)) hu).symm.trans
      (boundedFlatPullback_inv_hom (laurentIso P a) (n + 1) z)
  exact (congrArg (fun y => projectiveConnecting X n
    (boundedFlatPerfectToPerfectKMap (Relative.laurentFunctor.obj X).obj
      (n + 1) y)) ht).trans
    (DFunLike.congr_fun (projectiveConnecting_comp_boundedFlatForwardProjection_allDegrees X n) x)

/-- The complete original inverse coefficient operation has the actual identity/inverse pair. -/
theorem boundedFlatCoefficientNativeBoundary_comp_inverse (n : ℕ) :
    (boundedFlatCoefficientNativeProjectiveBoundary P a n).comp
      (boundedFlatCoefficientInverseLaurentKOperation P a n) =
      ((nativeTwoSummandKMap X n).comp
        ((MonoidHom.id (PerfectK (X).obj n)).prod invMonoidHom)).comp
          (boundedFlatPerfectToPerfectKMap (space (op P, a)) n) := by
  ext x
  let z := originalKSelfTrackOperation (boundedFlatPerfectWaldhausen (X).obj)
    (boundedFlatPerfectWaldhausen (Relative.laurentFunctor.obj X).obj)
    (boundedFlatPerfectUnitHomotopy (Relative.laurentProjection.app X).hom
      (laurentGlobalUnit X)⁻¹) n x
  have hu := DFunLike.congr_fun
    (boundedFlatCoefficientInverseLaurentKOperation_native P a n) x
  have ht : boundedFlatPerfectKPullback (laurentIso P a).inv (n + 1)
      (boundedFlatCoefficientInverseLaurentKOperation P a n x) = z :=
    (congrArg (boundedFlatPerfectKPullback (laurentIso P a).inv (n + 1)) hu).symm.trans
      (boundedFlatPullback_inv_hom (laurentIso P a) (n + 1) z)
  exact (congrArg (fun y => projectiveConnecting X n
    (boundedFlatPerfectToPerfectKMap (Relative.laurentFunctor.obj X).obj
      (n + 1) y)) ht).trans
    (DFunLike.congr_fun (projectiveConnecting_comp_boundedFlatInverseProjection_allDegrees X n) x)

end Quillen.PerfectComplexes
