/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedSingleAcyclicity
public import Quillen.Algebra.Homology.DerivedCategory.PlusSingleTriangle
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedPushforwardSection

/-!
# The actual derived triangle of a short exact sequence with acyclic last terms

The differential is the literal ordinary pushforward of the original arrow.
The comparison preserves the original derived connecting morphism.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Pretriangulated AlgebraicGeometry
namespace Quillen.SchemeSheaf
/-- Use the standard derived category of actual module sheaves. -/
local instance acyclicTriangleStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {S : ShortComplex X.Modules} (hS : S.ShortExact)
  [IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X S.X₂))]
  [IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X S.X₃))]
/-- The actual derived image of a short exact sequence with acyclic last two terms. -/
def acyclicShortExactTriangle : Triangle (DerivedCategory.Plus Y.Modules) :=
  let T := (derivedPushforwardPlus f).mapTriangle.obj hS.singleTrianglePlus
  Triangle.mk (T.mor₁ ≫ (derivedPushforwardPlusSingleIso f S.X₂).hom)
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map ((Scheme.Modules.pushforward f).map S.g))
    ((derivedPushforwardPlusSingleIso f S.X₃).inv ≫ T.mor₃)
/-- The computed triangle retains the original derived short-exact triangle and connecting map. -/
def acyclicShortExactTriangleIso :
    acyclicShortExactTriangle f hS ≅
      (derivedPushforwardPlus f).mapTriangle.obj hS.singleTrianglePlus := by
  refine Triangle.isoMk _ _ (Iso.refl _)
    (derivedPushforwardPlusSingleIso f S.X₂).symm
    (derivedPushforwardPlusSingleIso f S.X₃).symm ?_ ?_ ?_
  · dsimp [acyclicShortExactTriangle]
    simp
  · dsimp only [acyclicShortExactTriangle, Triangle.mk_mor₂, Triangle.mk_obj₂,
      Triangle.mk_obj₃, Iso.symm_hom]
    apply (cancel_mono (derivedPushforwardPlusSingleIso f S.X₃).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change _ = (derivedPushforwardPlusSingleIso f S.X₂).inv ≫
      (derivedPushforwardPlus f).map ((DerivedCategory.Plus.singleFunctor X.Modules 0).map S.g) ≫
      (derivedPushforwardPlusSingleIso f S.X₃).hom
    rw [derivedPushforwardPlusSingleIso_naturality f S.g]
    simp
  · dsimp [acyclicShortExactTriangle]
    simp
/-- The computed short-exact direct-image triangle is genuinely distinguished. -/
theorem acyclicShortExactTriangle_distinguished :
    acyclicShortExactTriangle f hS ∈ distTriang (DerivedCategory.Plus Y.Modules) :=
  isomorphic_distinguished _
    ((derivedPushforwardPlus f).map_distinguished _ hS.singleTrianglePlus_distinguished) _
    (acyclicShortExactTriangleIso f hS)
end Quillen.SchemeSheaf
end
