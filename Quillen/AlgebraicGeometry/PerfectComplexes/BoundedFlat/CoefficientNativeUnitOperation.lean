/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentKOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeOverlapUnitBoundary

/-!
# Original unit operations under the native coefficient/product comparison

The original chosen Laurent-fiber isomorphism preserves both the actual projection and the
literal integral-coordinate unit. The original unit postcomposition law therefore transports
both forward and inverse operations, without equating the chosen geometric pullbacks.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (a : Under R)
local notation "X" => Opposite.unop (Functor.obj (boundedFlatCoefficientQuasiCompactRow P) a)

/-- The actual Laurent product comparison carries the original forward unit operation. -/
theorem boundedFlatCoefficientLaurentKOperation_native (n : ℕ) :
    (boundedFlatPerfectKPullback (laurentIso P a).hom (n + 1)).comp
      (originalKSelfTrackOperation (boundedFlatPerfectWaldhausen (X).obj)
        (boundedFlatPerfectWaldhausen (Relative.laurentFunctor.obj X).obj)
        (boundedFlatPerfectUnitHomotopy (Relative.laurentProjection.app X).hom
          (ProjectiveLine.NativeBass.laurentGlobalUnit X)) n) =
      boundedFlatCoefficientLaurentKOperation P a n := by
  unfold boundedFlatCoefficientLaurentKOperation boundedFlatCoefficientLaurentUnitHomotopy
  refine (boundedFlatPerfectUnitHomotopy_originalKOperation_postcomp
    (laurentIso P a).hom (Relative.laurentProjection.app X).hom
    (ProjectiveLine.NativeBass.laurentGlobalUnit X) n).trans ?_
  have hp : (laurentIso P a).hom ≫
      (Relative.laurentProjection.app X).hom = laurentProjection P a :=
    laurentIso_hom_fst P a
  have hu : Units.map (laurentIso P a).hom.appTop.hom.toMonoidHom
      (ProjectiveLine.NativeBass.laurentGlobalUnit X) =
        boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
          (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right) :=
    laurentIso_globalUnit P a
  exact congrArg₂ (fun f q => originalKSelfTrackOperation
    (boundedFlatPerfectWaldhausen (space (op P, a)))
    (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a)))
    (boundedFlatPerfectUnitHomotopy f q) n) hp hu

/-- The same actual product comparison also preserves the literal inverse-unit operation. -/
theorem boundedFlatCoefficientInverseLaurentKOperation_native (n : ℕ) :
    (boundedFlatPerfectKPullback (laurentIso P a).hom (n + 1)).comp
      (originalKSelfTrackOperation (boundedFlatPerfectWaldhausen (X).obj)
        (boundedFlatPerfectWaldhausen (Relative.laurentFunctor.obj X).obj)
        (boundedFlatPerfectUnitHomotopy (Relative.laurentProjection.app X).hom
          (ProjectiveLine.NativeBass.laurentGlobalUnit X)⁻¹) n) =
      boundedFlatCoefficientInverseLaurentKOperation P a n := by
  unfold boundedFlatCoefficientInverseLaurentKOperation
  refine (boundedFlatPerfectUnitHomotopy_originalKOperation_postcomp
    (laurentIso P a).hom (Relative.laurentProjection.app X).hom
    (ProjectiveLine.NativeBass.laurentGlobalUnit X)⁻¹ n).trans ?_
  have hp : (laurentIso P a).hom ≫
      (Relative.laurentProjection.app X).hom = laurentProjection P a :=
    laurentIso_hom_fst P a
  have hu : Units.map (laurentIso P a).hom.appTop.hom.toMonoidHom
      (ProjectiveLine.NativeBass.laurentGlobalUnit X) =
        boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
          (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right) :=
    laurentIso_globalUnit P a
  exact congrArg₂ (fun f q => originalKSelfTrackOperation
    (boundedFlatPerfectWaldhausen (space (op P, a)))
    (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a)))
    (boundedFlatPerfectUnitHomotopy f q) n) hp ((map_inv _ _).trans (congrArg Inv.inv hu))

end Quillen.PerfectComplexes
