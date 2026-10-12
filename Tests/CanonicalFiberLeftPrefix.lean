/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.CofiberPrismLeftPrefix
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberPrism
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-! # Original fiber-prefix and specified component-translation consumers -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry unitInterval
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine Quillen.Scheme.PolynomialLaurent
open scoped Topology
universe u v
namespace Quillen.Tests.CanonicalFiberLeftPrefix

section General
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The prescribed transpose retains the actual fine object loop, without changing its class. -/
theorem original_fine_projection (X : AcyclicCategory N) :
    (canonicalFiberObjectLoopTranspose N X).val.1 = V.kZeroObjectLoop X.obj :=
  canonicalFiberObjectLoopTranspose_source N X

/-- Both original canonical-fiber coordinates survive the exact loop/fiber transpose. -/
theorem original_fiber_coordinates (X : AcyclicCategory N) (s t : unitInterval) :
    (canonicalFiberObjectLoopTranspose N X).val.2 s t =
      (canonicalFiberObjectLoop N X t).val.2 s :=
  canonicalFiberObjectLoopTranspose_path N X s t

/-- The component normalization uses the prescribed suffix track and literal reversed loop time. -/
theorem original_suffix_track (A : C) (s t : unitInterval) :
    loopRightUnitPath (V.kZeroObjectLoop A) s t =
      loopLeftUnitPath (V.kZeroObjectLoop A).symm s (unitInterval.symm t) :=
  loopRightUnitPath_apply _ _ _

/-- The unchanged localization map preserves the actual original object loop. -/
theorem original_changeWeak_objectLoop (A : C) :
    basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N) (V.kZeroObjectLoop A) =
      N.coarse.kZeroObjectLoop A :=
  deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A

/-- Degree-one component translation is natural for the actual original localization map. -/
theorem original_component_naturality (A : C)
    (a : HomotopyGroup.Pi 1 (Path V.kBasepoint V.kBasepoint) (Path.refl V.kBasepoint)) :
    loopLeftComponentHomotopyEquiv
        (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N) (V.kZeroObjectLoop A)) 1
        (homotopyGroupMap (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
          (basedLoopMap_refl _ _) a) =
      homotopyGroupMap (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)) rfl
        (loopLeftComponentHomotopyEquiv (V.kZeroObjectLoop A) 1 a) :=
  loopLeftComponentHomotopyEquiv_naturality _ _ _ _ _

end General

/-- The actual polynomial cofiber-prism prefix is this exact translated canonical-fiber path. -/
theorem original_polynomial_prefix (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) (s t : unitInterval) :
    loopLeftTranslationEquiv ((perfectOpenNested (laurentPlus R)).coarse.kZeroObjectLoop K)
        ((canonicalFiberObjectLoopTranspose (perfectOpenNested (laurentPlus R))
          (perfectOpenScalarCofiberAcyclic (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)).val.2 s) t =
      perfectOpenScalarCofiberCompositionCube (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K
        (0, unitInterval.symm s, t) :=
  cofiberPrismCompositionCube_zero_leftPrefix (perfectOpenNested (laurentPlus R))
    (perfectScalarInclusion _ (polynomialGlobalCoordinate R) K)
    ((ExtensionCategory.quotient (perfectWaldhausen (Spec (.of (Polynomial R))))).app
      (perfectScalarExtension _ (polynomialGlobalCoordinate R) K))
    (perfectScalarInclusion_openCof (laurentPlus R) (polynomialGlobalCoordinate R) K)
    (perfectScalarInclusion_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
      (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)
    (perfectScalarCofiber_isPushout (laurentPlus R) (polynomialGlobalCoordinate R) K) s t

end Quillen.Tests.CanonicalFiberLeftPrefix
