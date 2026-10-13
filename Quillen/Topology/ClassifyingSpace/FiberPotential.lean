/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.PathPotential
public import Quillen.Topology.HomotopyFiber.PathClass

/-!
# An actual fiber inverse is determined by its path potential

For a contractible classifying-space source, a genuine natural potential on
original arrows computes the unchanged inverse loop comparison. The proof
uses its actual inverse homotopy and actual continuous source paths.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w z
open CategoryTheory
open scoped Topology
namespace Quillen
variable {C : Type u} [Category.{v} C] {Y : Type w} [TopologicalSpace Y]
  [ContractibleSpace (ClassifyingSpace C)]

/-- The exact original inverse has source label divided by target label. -/
theorem loopInverse_classifyingSpace_potential
    (f : C(ClassifyingSpace C, Y)) (y : Y)
    (τ : classifyingFundamentalGroupoidFunctor C ⋙ FundamentalGroupoid.map f ⟶
      (Functor.const C).obj (FundamentalGroupoid.mk y))
    {G : Type z} [CommGroup G] (L : G →* FundamentalGroup Y y)
    (c d : C) (a b : G)
    (γ : Path (f (classifyingSpacePoint c)) y)
    (δ : Path (f (classifyingSpacePoint d)) y)
    (hc : τ.app c = (Path.Homotopic.Quotient.mk γ :
      FundamentalGroupoid.mk (f (classifyingSpacePoint c)) ⟶ FundamentalGroupoid.mk y) ≫ L a)
    (hd : τ.app d = (Path.Homotopic.Quotient.mk δ :
      FundamentalGroupoid.mk (f (classifyingSpacePoint d)) ⟶ FundamentalGroupoid.mk y) ≫ L b) :
    Path.Homotopic.Quotient.mk
      ((HomotopyFiber.loopEquivOfContractibleSourcePath f (classifyingSpacePoint c) y γ).invFun
        (HomotopyFiber.pointWithPath f (classifyingSpacePoint d) y δ)) = L (a / b) := by
  let p := PathConnectedSpace.somePath (classifyingSpacePoint c) (classifyingSpacePoint d)
  rw [HomotopyFiber.loopInverse_pathClass f y _ γ _ p]
  have h := classifyingSpacePath_potential f (FundamentalGroupoid.mk y) τ p
  rw [hc, hd] at h
  apply (cancel_epi (C := FundamentalGroupoid Y) (Path.Homotopic.Quotient.mk γ :
    FundamentalGroupoid.mk (f (classifyingSpacePoint c)) ⟶ FundamentalGroupoid.mk y)).1
  apply (cancel_mono (C := FundamentalGroupoid Y) (L b)).1
  have hl : L (a / b) ≫ L b = L a := by
    change L b * L (a / b) = L a
    rw [← map_mul]
    exact congrArg L (by simp [div_eq_mul_inv, mul_left_comm])
  dsimp only [HomotopyFiber.toPath, HomotopyFiber.pointWithPath]
  simp only [Category.assoc]
  erw [hl]
  simp only [FundamentalGroupoid.comp_eq, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
  convert h using 1
  · rfl
  · exact Path.Homotopic.Quotient.trans_assoc _ _ _

end Quillen
