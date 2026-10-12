/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremA.ReplacementHomology
public import Quillen.CategoryTheory.TheoremA.InitialReplacement

/-! # Original full replacement comparison and exact initial-entry consumers -/
@[expose] public section
noncomputable section
open CategoryTheory Limits Quillen.LocalCoefficients Quillen.TheoremA
open scoped Simplicial Topology
universe u
namespace Quillen.Tests
variable {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}}

/-- The full original realized replacement map, with a possibly nonconstant abelian system. -/
example (η : H ⟶ K)
    (hη : ∀ (d : D) (A : System.{u, u} |K.obj d|), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app d)).hom A))
    (A : System.{u, u} |replacementDiagonal K|) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap
      (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom A) :=
  replacementRealization_abelian_quasiIso η hη A hA

/-- The canonical constant-to-diagram comparison retains the original initial entry. -/
example (i : D) (hi : IsInitial i) :
    replacementEntry ((Functor.const D).obj (H.obj i)) i ≫
        diagonalMap (simplicialReplacementMap (initialReplacementComparison H i hi)) =
      replacementEntry H i :=
  initialReplacementComparison_entry H i hi

end Quillen.Tests
