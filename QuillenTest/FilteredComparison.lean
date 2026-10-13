/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.FilteredComparison
public import Quillen.Topology.LocalCoefficients.HomotopyEquivalence

/-! # Consumers of original filtered local-coefficient comparison maps -/

@[expose] public section
noncomputable section
open CategoryTheory Limits HomologicalComplex
open scoped Simplicial
universe u
namespace QuillenTest.FilteredComparison
open Quillen.LocalCoefficients

/-- Actual stage homotopy equivalences imply the original sequential comparison
for every local system on the original target colimit. -/
theorem sequential_original_stage_homotopyEquiv
    (F G : ℕ ⥤ SSet.{u}) (c : Cocone F) (d : Cocone G)
    (η : F ⟶ G) (f : c.pt ⟶ d.pt)
    (w : ∀ n, c.ι.app n ≫ f = η.app n ≫ d.ι.app n)
    (hc : IsColimit c) (hd : IsColimit d)
    (e : ∀ n, ContinuousMap.HomotopyEquiv |F.obj n| |G.obj n|)
    (he : ∀ n, (e n).toFun = (SSet.toTop.map (η.app n)).hom)
    (A : System.{u, u} |d.pt|) :
    QuasiIso (pushforwardChainMap (SSet.toTop.map f).hom A) := by
  apply sequentialComparison_pushforwardChainMap_quasiIso F G c d η f w hc hd A
  intro n
  rw [← he n]
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_pushforwardHomologyMap_of_homotopyEquiv (e n) _ k

/-- The genuinely filtered criterion controls the actual induced homology map
in every degree, without assuming injective transition maps. -/
theorem filtered_original_homology_map {J : Type u} [SmallCategory J] [IsFiltered J]
    (F G : J ⥤ SSet.{u}) (c : Cocone F) (d : Cocone G)
    (η : F ⟶ G) (f : c.pt ⟶ d.pt)
    (w : ∀ j, c.ι.app j ≫ f = η.app j ≫ d.ι.app j)
    (hc : IsColimit c) (hd : IsColimit d) (A : System.{u, u} |d.pt|)
    (hη : ∀ j, QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app j)).hom
      (pullback (SSet.toTop.map (d.ι.app j)).hom A))) (n : ℕ) :
    IsIso (pushforwardHomologyMap (SSet.toTop.map f).hom A n) := by
  let := filteredComparison_pushforwardChainMap_quasiIso F G c d η f w hc hd A hη
  change IsIso (HomologicalComplex.homologyMap _ n)
  infer_instance

end QuillenTest.FilteredComparison
