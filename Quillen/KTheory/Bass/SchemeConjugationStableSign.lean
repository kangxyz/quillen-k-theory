/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeConjugationLowStages
public import Quillen.Topology.Prespectrum.LoopTransposeStableSign

/-!
# The signed second conjugation

The actual second conjugation induces the negative of its geometric
two-cone word in every stable degree. The geometric word and its equality
transports remain present, so this does not assert cancellation of the sign.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum Quillen.LoopPrespectrum.FiniteLoopWords
open Quillen.KTheory.Bass.GeometricConeFixedWords

universe u w

namespace Quillen.KTheory.Bass.SchemeNaturalSeed

private theorem neg_id_comp {C : Type*} [Category C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) : (-𝟙 X) ≫ f = -f := by
  rw [Preadditive.neg_comp, Category.id_comp]

/-- The second original conjugation has its actual transpose sign, retaining the geometric map. -/
theorem conjugatingIso_two_stable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    (stableHomotopyFunctor d).map ((conjugatingIso 2 F).hom.app X) =
      -((stableHomotopyFunctor d).map ((loopMap 2
        (eqToHom (power_obj 2 F).symm ≫
          (GeometricConeInterchange.permutationNatIso F).hom ≫
            eqToHom (power_obj 2 F))).app X)) := by
  rw [congrArg (fun η => η.app X) (conjugatingIso_two_hom F)]
  change (stableHomotopyFunctor d).map
      (LoopTranspose.transpose ((FiniteConeTopology.iterate squareFunctor 2 F).obj X) ≫ _) = _
  rw [CategoryTheory.Functor.map_comp, LoopTranspose.stableHomotopyFunctor_map_transpose]
  exact neg_id_comp _

end Quillen.KTheory.Bass.SchemeNaturalSeed
