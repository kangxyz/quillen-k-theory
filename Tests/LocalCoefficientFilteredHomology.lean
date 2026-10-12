/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.FilteredHomology
public import Tests.LocalCoefficientChains

/-!
# Consumers of filtered local homology and cofinality

The canonical comparison retains the original maps for the regular path-class
system, including after any cofinal change of indexing category.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace Quillen.Tests.LocalCoefficientFilteredHomology

open LocalCoefficients

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)

/-- The comparison on regular-system homology retains each original spatial map. -/
theorem regular_homology_original_arrow (b : |c.pt|) (V : ModuleCat.{u} ℤ)
    (n : ℕ) (j : J) :
    colimit.ι (filteredHomologyDiagram F c (LocalCoefficientChains.regularSystem b V) n) j ≫
        (filteredHomologyColimitIso F c hc (LocalCoefficientChains.regularSystem b V) n).hom =
      pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom
        (LocalCoefficientChains.regularSystem b V) n :=
  filteredHomologyColimitIso_ι_hom F c hc _ n j

/-- A cofinal reindexing gives the same regular-system homology via the original arrows. -/
theorem regular_homology_cofinal_arrow (b : |c.pt|) (V : ModuleCat.{u} ℤ)
    (n : ℕ) {I : Type u} [SmallCategory I] (G : I ⥤ J) [G.Final] (i : I) :
    colimit.ι (G ⋙ filteredHomologyDiagram F c (LocalCoefficientChains.regularSystem b V) n) i ≫
        (cofinalFilteredHomologyIso F c hc (LocalCoefficientChains.regularSystem b V) n G).hom =
      pushforwardHomologyMap (SSet.toTop.map (c.ι.app (G.obj i))).hom
        (LocalCoefficientChains.regularSystem b V) n :=
  cofinalFilteredHomologyIso_ι_hom F c hc _ n G i

end Quillen.Tests.LocalCoefficientFilteredHomology
