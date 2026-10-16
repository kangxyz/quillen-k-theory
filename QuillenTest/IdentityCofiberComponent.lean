/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.IdentityCofiberComponent
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberPrism
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-! # The actual identity-cofiber component path in the polynomial boundary prism -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.PerfectComplexes
open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes.Affine
open Quillen.Waldhausen.Fibration AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped Topology
universe u
namespace QuillenTest.IdentityCofiberComponent

open Quillen
variable (R : CommRingCat.{u}) (K : Perfect (Spec (.of (Polynomial R))))

/-- The prescribed source is the original object loop with its literal constant suffix. -/
theorem original_suffix_source (t : unitInterval) :
    (perfectWaldhausen (Spec (.of (Polynomial R)))).identityCofiberSuffixPath K 0 t =
      (((perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop K).trans
        (Path.refl (perfectWaldhausen (Spec (.of (Polynomial R)))).kBasepoint)) t :=
  congrArg (fun p ↦ p t)
    ((perfectWaldhausen (Spec (.of (Polynomial R)))).identityCofiberSuffixPath K).source

/-- Its endpoint is the unchanged original source object loop. -/
theorem original_suffix_target (t : unitInterval) :
    (perfectWaldhausen (Spec (.of (Polynomial R)))).identityCofiberSuffixPath K 1 t =
      (perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop K t :=
  congrArg (fun p ↦ p t)
    ((perfectWaldhausen (Spec (.of (Polynomial R)))).identityCofiberSuffixPath K).target

/-- Localization preserves both original identity-triangle coordinates. -/
theorem original_suffix_image (s t : unitInterval) :
    changeWeakMap (perfectOpenNested (laurentPlus R))
        ((perfectWaldhausen (Spec (.of (Polynomial R)))).identityCofiberSuffixPath K s t) =
      (perfectOpenNested (laurentPlus R)).coarse.identityCofiberSuffixPath K s t :=
  identityCofiberSuffixPath_changeWeak _ _ _ _

/-- The actual polynomial prism has exactly this specified identity-triangle source face. -/
theorem original_prism_source_face (s t : unitInterval) :
    perfectOpenScalarCofiberCompositionCube (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (s, 0, t) =
      (perfectOpenNested (laurentPlus R)).coarse.identityCofiberSuffixPath K s t := by
  unfold perfectOpenScalarCofiberCompositionCube
  rw [Structure.cofiberPrismCompositionCube_nerve_zero]
  rfl

/-- The prism-matched degree-one translation uses the unchanged localization map. -/
theorem original_component_naturality
    (a : HomotopyGroup.Pi 1
      (Path (perfectWaldhausen (Spec (.of (Polynomial R)))).kBasepoint
        (perfectWaldhausen (Spec (.of (Polynomial R)))).kBasepoint)
      (Path.refl (perfectWaldhausen (Spec (.of (Polynomial R)))).kBasepoint)) :
    (perfectOpenNested (laurentPlus R)).coarse.identityCofiberComponentEquiv K 1
        (Quillen.homotopyGroupMap
          (Quillen.basedLoopMap (changeWeakMap (perfectOpenNested (laurentPlus R)))
            (changeWeakMap_basepoint _)) (Quillen.basedLoopMap_refl _ _) a) =
      Quillen.homotopyGroupMap
        (Quillen.basedLoopMap (changeWeakMap (perfectOpenNested (laurentPlus R)))
          (changeWeakMap_basepoint _))
        (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested (laurentPlus R)))
          (perfectOpenNested (laurentPlus R)).zero_eq.symm K)
        ((perfectWaldhausen (Spec (.of (Polynomial R)))).identityCofiberComponentEquiv K 1 a) :=
  identityCofiberComponentEquiv_naturality _ _ _ _

end QuillenTest.IdentityCofiberComponent
