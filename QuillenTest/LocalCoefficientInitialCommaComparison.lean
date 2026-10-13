/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.TheoremA.InitialHomology

/-! # Original initial-comma entry and projection comparison consumers -/
@[expose] public section
noncomputable section
open CategoryTheory Limits Quillen.LocalCoefficients Quillen.TheoremA
open scoped Simplicial Topology
universe u
namespace QuillenTest

open Quillen
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (F : C ⥤ D) (i : D) (hi : IsInitial i)
  (htrans : ∀ (d : D) (B : System.{u, u} |(commaNerveDiagram F).obj d|),
    AbelianMonodromy B → QuasiIso (pushforwardChainMap
      (SSet.toTop.map ((commaNerveDiagram F).map (hi.to d))).hom B))

/-- The actual entry into the canonical strict comma replacement. -/
example (A : System.{u, u} |replacementDiagonal (commaNerveDiagram F)|)
    (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap
      (SSet.toTop.map (replacementEntry (commaNerveDiagram F) i)).hom A) :=
  commaInitialReplacementEntry_abelian_quasiIso F i hi htrans A hA

/-- The original comma projection, without an assumed homology-fibration comparison. -/
example (A : System.{u, u} (ClassifyingSpace C)) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap
      (SSet.toTop.map (nerveMap (CostructuredArrow.proj F i))).hom A) :=
  commaInitialProjection_abelian_quasiIso F i hi htrans A hA

/-- Every degree, including zero, uses the original induced local homology map. -/
example (A : System.{u, u} (ClassifyingSpace C)) (hA : AbelianMonodromy A) (n : ℕ) :
    IsIso (pushforwardHomologyMap
      (SSet.toTop.map (nerveMap (CostructuredArrow.proj F i))).hom A n) := by
  have := commaInitialProjection_abelian_quasiIso F i hi htrans A hA
  change IsIso (HomologicalComplex.homologyMap _ n)
  infer_instance

end QuillenTest
