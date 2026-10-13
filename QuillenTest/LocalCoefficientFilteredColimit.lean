/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.FilteredColimit
public import QuillenTest.LocalCoefficientChains

/-!
# Consumers of the actual filtered local-chain colimit

The comparison is checked with the regular path-class coefficient system and
with its original spatial arrows. No injectivity of the stage maps is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace QuillenTest.LocalCoefficientFilteredColimit

open Quillen

open LocalCoefficients

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)

/-- The actual chain colimit comparison works for the regular path-class system. -/
def regular_chain_colimit (b : |c.pt|) (V : ModuleCat.{u} ℤ) :
    colimit (filteredChainDiagram F c (LocalCoefficientChains.regularSystem b V)) ≅
      singularChainComplex (LocalCoefficientChains.regularSystem b V) :=
  filteredChainColimitIso F c hc _

/-- Each original stage arrow is retained, rather than an unrelated isomorphism. -/
theorem regular_chain_colimit_original_arrow (b : |c.pt|) (V : ModuleCat.{u} ℤ) (j : J) :
    colimit.ι (filteredChainDiagram F c (LocalCoefficientChains.regularSystem b V)) j ≫
        (regular_chain_colimit F c hc b V).hom =
      pushforwardChainMap (SSet.toTop.map (c.ι.app j)).hom
        (LocalCoefficientChains.regularSystem b V) :=
  filteredChainColimitIso_ι_hom F c hc _ j

end QuillenTest.LocalCoefficientFilteredColimit
