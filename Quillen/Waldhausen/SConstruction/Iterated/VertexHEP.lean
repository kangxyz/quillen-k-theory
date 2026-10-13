/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.VertexHEP
public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum

/-!
# Well-based positive levels of the original iterated-S spectrum

Each positive original level is the realization of its actual simplicial stage, with the literal
chosen zero vertex. Its singleton inclusion has HEP by the genuine realized-vertex theorem.
-/
@[expose] public section
noncomputable section

open CategoryTheory
universe u v
namespace Quillen.Waldhausen.IteratedS

/-- The chosen point of each actual positive S-spectrum level has a genuine HEP inclusion. -/
theorem originalPrespectrum_positivePoint_homotopyExtensionProperty
    {C : Type u} [Category.{v} C] (W : Structure C) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{max u v + 1} ((originalPrespectrum W).point (n + 1)))) :=
  Realization.homotopyExtensionProperty_vertex (stageVertex n (modelOf W))

end Quillen.Waldhausen.IteratedS
