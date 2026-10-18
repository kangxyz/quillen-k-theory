/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Automorphism.Cube
public import Quillen.Topology.HomotopyGroups.PathTransportFundamentalGroup
public import Quillen.Topology.HomotopyGroups.Loop.KOneNormalization
public import Quillen.Topology.HomotopyGroups.Loop.Reversal

/-!
# The positive capped cube as an actual loop-valued map

Right translation by the inverse base loop, its specified cancellation cap,
and one inner-loop reversal represent the class of the literal transposed
automorphism cube. Every loop-space component has abelian fundamental group, so a genuine
homotopy from a candidate map preserves its induced class with that candidate’s
original correction path; pointwise agreement of correction paths is unnecessary.

The current consumer is the native completion-to-Q marking problem. OPEN:
the required homotopy from that actual localized-completion map to this
displayed positive map has not been constructed. The conditional comparison
criterion retains its homotopy as an explicit input and proves no marked
field determinant without that input.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory
open scoped Topology
namespace Quillen.Automorphism
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Every actual loop-space component has commutative fundamental group, via its second
homotopy group. -/
lemma loopComponent_piOne_mul_comm (p : Path x x)
    (a b : HomotopyGroup.Pi 1 (Path x x) p) : a * b = b * a := by
  let e := HomotopyGroup.pi1MulEquivFundamentalGroup.trans (loopKOneNormalization p)
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

private lemma fundamentalGroup_transport_symm {p q : Path x x} (γ : Path p q) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath γ.symm =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm := by
  apply MulEquiv.ext
  intro a
  change CategoryTheory.Groupoid.inv (CategoryTheory.Groupoid.inv
    (Path.Homotopic.Quotient.mk γ)) ≫ a ≫
      CategoryTheory.Groupoid.inv (Path.Homotopic.Quotient.mk γ) =
    Path.Homotopic.Quotient.mk γ ≫ a ≫
      CategoryTheory.Groupoid.inv (Path.Homotopic.Quotient.mk γ)
  simp only [Groupoid.inv_eq_inv, CategoryTheory.IsIso.inv_inv]

variable {Z : Type v} [TopologicalSpace Z] (f : C(Z, Path x x)) (z : Z)

/-- Postcompose the displayed loop-valued map with right translation by its base loop’s inverse. -/
def rightNormalizedLoopMap : C(Z, Path x x) := (rightTranslate (f z)).comp f

/-- The original cancellation cap, in the direction from the translated image to the
constant loop. -/
def rightNormalizationPath : Path (rightNormalizedLoopMap f z z) (Path.refl x) :=
  (cancellationPath (f z)).symm

/-- Right translation and the specified cap induce exactly the original capped-class
homomorphism. -/
theorem rightNormalization_formula (a : HomotopyGroup.Pi 1 Z z) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv (rightNormalizationPath f z) 0
        (piMap 0 (rightNormalizedLoopMap f z) rfl a)) =
      loopComponentToPiTwo (f z)
        (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)) := by
  apply (loopShiftMulEquiv 0).injective
  simp only [loopComponentToPiTwo, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  change pathTransport (rightNormalizationPath f z) 1
    (homotopyGroupMap (rightNormalizedLoopMap f z) rfl a) =
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath (cancellationPath (f z))).symm
          (FundamentalGroup.map (rightTranslate (f z)) (f z)
            (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a))))
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [piOneEquivFundamentalGroup_pathTransport, MulEquiv.apply_symm_apply]
  erw [piOneEquivFundamentalGroup_naturality]
  have hm (b : FundamentalGroup Z z) :
      FundamentalGroup.mapOfEq (rightNormalizedLoopMap f z) rfl b =
        FundamentalGroup.map (rightTranslate (f z)) (f z) (FundamentalGroup.map f z b) := by
    obtain ⟨α, rfl⟩ := Path.Homotopic.Quotient.mk_surjective b
    rw [FundamentalGroup.mapOfEq_apply]
    rfl
  rw [hm]
  exact DFunLike.congr_fun (fundamentalGroup_transport_symm (cancellationPath (f z))) _

/-- Reverse the inner loop after the original right translation, with no other normalization. -/
def positiveNormalizedLoopMap : C(Z, Path x x) :=
  loopReversal.comp (rightNormalizedLoopMap f z)

/-- Reverse the inner loops of the original cancellation track while retaining its outer
direction. -/
def positiveNormalizationPath : Path (positiveNormalizedLoopMap f z z) (Path.refl x) :=
  loopReversalPath (rightNormalizationPath f z)

/-- The displayed right normalization and single reversal represent the inverse original
capped class. -/
theorem positiveNormalization_formula (a : HomotopyGroup.Pi 1 Z z) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv (positiveNormalizationPath f z) 0
        (piMap 0 (positiveNormalizedLoopMap f z) rfl a)) =
      (loopComponentToPiTwo (f z)
        (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)))⁻¹ := by
  have ht : pathTransport (positiveNormalizationPath f z) 1
      (homotopyGroupMap (positiveNormalizedLoopMap f z) rfl a) =
    homotopyGroupMap loopReversal loopReversal_refl
      (pathTransport (rightNormalizationPath f z) 1
        (homotopyGroupMap (rightNormalizedLoopMap f z) rfl a)) := by
    exact (congrArg (pathTransport (positiveNormalizationPath f z) 1)
      (homotopyGroupMap_comp (rightNormalizedLoopMap f z) rfl loopReversal rfl a)).trans
      (pathTransport_naturality_of_track loopReversal (rightNormalizationPath f z)
        (positiveNormalizationPath f z) rfl loopReversal_refl (fun _ => rfl) 1 _)
  change (loopShiftMulEquiv 0).symm (pathTransport _ 1 (homotopyGroupMap _ _ a)) = _
  rw [ht]
  exact (loopShiftEquiv_symm_loopReversal 1 _).trans
    (congrArg (fun a => a⁻¹) (rightNormalization_formula f z a))

/-- A genuine map homotopy suffices with the candidate’s actual prescribed correction path. -/
theorem positiveNormalization_of_homotopy {k : C(Z, Path x x)}
    (H : k.Homotopy (positiveNormalizedLoopMap f z))
    (γ : Path (k z) (Path.refl x)) (a : HomotopyGroup.Pi 1 Z z) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv γ 0 (piMap 0 k rfl a)) =
      (loopComponentToPiTwo (f z)
        (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)))⁻¹ := by
  have h := DFunLike.congr_fun (piOne_homotopy_corrected H γ
    (positiveNormalizationPath f z) (loopComponent_piOne_mul_comm (Path.refl x))) a
  exact (congrArg (loopShiftMulEquiv 0).symm h).trans (positiveNormalization_formula f z a)

end Quillen.Automorphism

namespace Quillen.Automorphism
open CategoryTheory.Limits CategoryTheory.ExactCategory Functoriality
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (A : C)

/-- The original core Q-loop map on the actual one-object automorphism diagram. -/
def automorphismLoopMap : C(ClassifyingSpace (AutIndex A), Path E.kBasepoint E.kBasepoint) :=
  (coreLoopMap E).comp (classifyingSpaceMap (autCore A)).hom

/-- The actual realized automorphism edge, regarded in the first homotopy group. -/
def automorphismPiOne (g : Aut A) :
    HomotopyGroup.Pi 1 (ClassifyingSpace (AutIndex A)) (classifyingSpacePoint (autVertex A)) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    (Path.Homotopic.Quotient.mk (classifyingSpacePath
      (C := AutIndex A) (c := autVertex A) (d := autVertex A) g))

/-- The displayed positive loop map represents the literal coordinate-transposed
automorphism cube. -/
theorem normalizedPositiveMap_cube (g : Aut A) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv
        (positiveNormalizationPath (automorphismLoopMap E A)
          (classifyingSpacePoint (autVertex A))) 0
        (piMap 0 (positiveNormalizedLoopMap (automorphismLoopMap E A)
          (classifyingSpacePoint (autVertex A))) rfl (automorphismPiOne A g))) =
      (Quotient.mk' (Cube.automorphismFirstCube E A g) : E.K 1) := by
  rw [positiveNormalization_formula, Cube.automorphismFirstCube_class]
  apply congrArg (fun a => a⁻¹)
  rw [automorphismClass_eq]
  let α := classifyingSpacePath (C := AutIndex A) (c := autVertex A) (d := autVertex A) g
  have hp : automorphismLoopMap E A (classifyingSpacePoint (autVertex A)) =
      coreLoopMap E (classifyingSpacePoint (Core.mk A)) := by
    change coreLoopMap E (classifyingSpaceMap (autCore A)
      (classifyingSpacePoint (autVertex A))) = _
    rw [classifyingSpaceMap_point]
    rfl
  change loopComponentToPiTwo _ (FundamentalGroup.map _ _
    (HomotopyGroup.pi1MulEquivFundamentalGroup
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm (Path.Homotopic.Quotient.mk α)))) = _
  rw [MulEquiv.apply_symm_apply]
  apply componentToPiTwo_congr hp
  intro t
  change coreLoopMap E (classifyingSpaceMap (autCore A) (α t)) = _
  rw [classifyingSpacePath_naturality]
  rfl

end Quillen.Automorphism
