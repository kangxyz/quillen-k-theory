/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberFiberBoundaryPath
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Coordinates
public import Quillen.Topology.HomotopyGroups.Loop.InverseComponentTranslation
public import Quillen.Topology.HomotopyGroups.PathTransportFundamentalGroup
public import Quillen.Waldhausen.Fibration.IdentityCofiberNormalization

/-!
# Constant-component normalization of the original scalar-cofiber boundary

Left concatenation with the inverse of the original object loop is a genuine homotopy
equivalence. Its value at that object loop has a specified cancellation path to the constant
loop. These two operations, followed by the original loop-degree shift, put both the existing
scalar-cofiber boundary and the independently specified forward scalar square in the actual
coarse K-one group. The boundary class is the inverse of the forward-square class.
The normalization also agrees with the inverse of the original identity-cofiber component
equivalence on the first homotopy group.

No path from the original object loop to the constant loop is assumed. The specified Laurent
automorphism class, its comparison with this forward-square class, and the supported zero-section
boundary formula remain separate interfaces.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.Fibration
open scoped Topology
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (K : Perfect X)

/-- The inverse object-loop prefix has its specified standard cancellation to the constant loop.
This path starts at the translated loop, not at the original object loop. -/
def perfectOpenObjectLoopCancellation :
    Path (((perfectOpenNested j).coarse.kZeroObjectLoop K).symm.trans
      ((perfectOpenNested j).coarse.kZeroObjectLoop K))
      (Path.refl (perfectOpenNested j).coarse.kBasepoint) where
  toFun s := ((Path.Homotopy.reflSymmTrans
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)).symm).eval s
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (Path.Homotopy.reflSymmTrans
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)).symm.continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

/-- The original object component is translated by its inverse prefix, then aligned with the
constant component by the displayed cancellation. The last equivalence is the actual loop shift.
-/
def perfectOpenObjectLoopKOneNormalization :
    FundamentalGroup
      (Path (perfectOpenNested j).coarse.kBasepoint (perfectOpenNested j).coarse.kBasepoint)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K) ≃* (perfectOpenNested j).coarse.K 1 :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
    ((MulEquiv.ofBijective
      (piMap 0
        (loopLeftTranslationEquiv ((perfectOpenNested j).coarse.kZeroObjectLoop K).symm).toFun
        (loopLeftTranslationEquiv_apply _ _))
      (homotopyGroupMap_bijective_of_homotopyEquiv
        (loopLeftTranslationEquiv ((perfectOpenNested j).coarse.kZeroObjectLoop K).symm)
        (loopLeftTranslationEquiv_apply _ _) 1)).trans
      ((pathTransportMulEquiv (perfectOpenObjectLoopCancellation j K) 0).trans
        (loopShiftMulEquiv 0).symm))

/-- The whole normalized loop retains the inverse prefix and both original cancellation paths.
-/
def perfectOpenObjectLoopNormalizedPath
    (α : Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    Path (Path.refl (perfectOpenNested j).coarse.kBasepoint)
      (Path.refl (perfectOpenNested j).coarse.kBasepoint) :=
  (perfectOpenObjectLoopCancellation j K).symm.trans
    (((α.map
      (loopLeftTranslationEquiv ((perfectOpenNested j).coarse.kZeroObjectLoop K).symm).continuous
      ).cast (loopLeftTranslationEquiv_apply _ _).symm
        (loopLeftTranslationEquiv_apply _ _).symm).trans
      (perfectOpenObjectLoopCancellation j K))

/-- The component equivalence sends each actual loop to exactly the displayed normalized loop
class, so its specified translation and both cancellation paths are retained. -/
theorem perfectOpenObjectLoopKOneNormalization_path
    (α : Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
      (loopShiftMulEquiv 0 (perfectOpenObjectLoopKOneNormalization j K ⟦α⟧)) =
        ⟦perfectOpenObjectLoopNormalizedPath j K α⟧ := by
  simp only [perfectOpenObjectLoopKOneNormalization, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (pathTransport (perfectOpenObjectLoopCancellation j K) 1
      (piMap 0
        (loopLeftTranslationEquiv ((perfectOpenNested j).coarse.kZeroObjectLoop K).symm).toFun
        (loopLeftTranslationEquiv_apply _ _)
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm ⟦α⟧))) = _
  rw [piOneEquivFundamentalGroup_pathTransport, piOneEquivFundamentalGroup_naturality,
    MulEquiv.apply_symm_apply, FundamentalGroup.mapOfEq_apply]
  rfl

/-- The explicit inverse prefix agrees with the inverse of the existing identity-cofiber
component equivalence, with the actual loop-degree shift and fundamental-group comparison. -/
theorem perfectOpenObjectLoopKOneNormalization_component
    (a : FundamentalGroup
      (Path (perfectOpenNested j).coarse.kBasepoint (perfectOpenNested j).coarse.kBasepoint)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    perfectOpenObjectLoopKOneNormalization j K a =
      (loopShiftMulEquiv 0).symm
        (((perfectOpenNested j).coarse.identityCofiberComponentEquiv K 1).symm
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)) := by
  change (loopShiftMulEquiv 0).symm
    (loopInversePrefixHomotopyEquiv ((perfectOpenNested j).coarse.kZeroObjectLoop K) 1
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)) = _
  rw [loopInversePrefixHomotopyEquiv_eq, Structure.identityCofiberComponentEquiv_eq]

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The actual original scalar-cofiber loop, normalized to the specified coarse K-one group. -/
def perfectScalarCofiberBoundaryKOneClass : (perfectOpenNested j).coarse.K 1 :=
  perfectOpenObjectLoopKOneNormalization j K
    ⟦perfectScalarCofiberBoundaryLoop j r q hq K⟧

/-- The independent forward scalar square, normalized by the very same component translation. -/
def perfectScalarForwardKOneClass : (perfectOpenNested j).coarse.K 1 :=
  perfectOpenObjectLoopKOneNormalization j K ⟦perfectScalarWeakLoop j r q hq K⟧

/-- The original scalar boundary is the inverse of the independently specified forward square
after the actual inverse-prefix translation, cancellation, and loop-degree shift. -/
theorem perfectScalarCofiberBoundaryKOneClass_eq_inv :
    perfectScalarCofiberBoundaryKOneClass j K r q hq =
      (perfectScalarForwardKOneClass j K r q hq)⁻¹ := by
  have h : (⟦perfectScalarCofiberBoundaryLoop j r q hq K⟧ :
      FundamentalGroup _ ((perfectOpenNested j).coarse.kZeroObjectLoop K)) =
        ⟦(perfectScalarWeakLoop j r q hq K).symm⟧ :=
    Quotient.sound ⟨perfectScalarCofiberBoundaryOrientation j r q hq K⟩
  change perfectOpenObjectLoopKOneNormalization j K _ = _
  rw [h]
  let a : FundamentalGroup
      (Path (perfectOpenNested j).coarse.kBasepoint (perfectOpenNested j).coarse.kBasepoint)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K) := ⟦perfectScalarWeakLoop j r q hq K⟧
  have hi : a⁻¹ =
      ⟦(perfectScalarWeakLoop j r q hq K).symm⟧ := rfl
  rw [← hi]
  exact (perfectOpenObjectLoopKOneNormalization j K).map_inv a

open AlgebraicGeometry.Scheme.PolynomialLaurent in
/-- The actual polynomial-coordinate boundary has the same inverse orientation on the original
Laurent open. This specializes the normalized coarse classes; it does not identify them with an
independently prescribed Laurent automorphism class in the open perfect K-group. -/
theorem polynomialScalarCofiberBoundaryKOneClass_eq_inv (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    perfectScalarCofiberBoundaryKOneClass (laurentPlus R) K
        (polynomialGlobalCoordinate R) (laurentGlobalUnit R)
        (polynomialGlobalCoordinate_laurentPlus R) =
      (perfectScalarForwardKOneClass (laurentPlus R) K
        (polynomialGlobalCoordinate R) (laurentGlobalUnit R)
        (polynomialGlobalCoordinate_laurentPlus R))⁻¹ :=
  perfectScalarCofiberBoundaryKOneClass_eq_inv _ _ _ _ _

end Quillen.PerfectComplexes
