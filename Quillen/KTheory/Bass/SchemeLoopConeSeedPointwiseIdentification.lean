/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeLoopConeSeedIdentification
public import Quillen.KTheory.Bass.SchemeSeedObjectIdentification
public import Quillen.KTheory.Bass.SchemeSeedEndpointIdentification
public import Quillen.KTheory.Bass.SchemeBassFunctorIdentification

/-! # Pointwise identification of the original looped cone seed -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteParameterLooping
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.SchemeIteratedSeedTransition
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
open FiniteConeTopology
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- Every component retains the same original looped-cone and geometric-cospan seed. -/
theorem seed_loopCone_app_heq_bassSeed (A : Track laurent.op coefficient F)
    (X : Scheme.{u}ᵒᵖ) :
    HEq ((seed ((coneTrack A 1).loop)).app X)
      ((WholeSeedCospan.seed
        (GeometricSquareInterchange.geometricSquare
          ((strictDiagramFunctor squareFunctor).obj F))
        (bassTrack F A.homotopy A.naturality)
        (bassTrack_naturality F A.homotopy A.naturality)).app X) := by
  have hseed := seed_loopCone_heq_bassSeed A
  dsimp only [geometricSquare_source_eq, geometricSquare_coneDiagram_eq,
    bassFunctor_obj_eq, iterate] at hseed ⊢
  have he := eq_of_heq hseed
  exact heq_of_eq (NatTrans.congr_app he X)

end Quillen.KTheory.Bass.SchemeIteratedSeedTransition
