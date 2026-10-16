/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnit


public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.Scalar.GlobalUnit
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopy
public import Quillen.Waldhausen.SConstruction.Iterated.ExactCoherence
public import Quillen.Topology.Prespectrum.HomotopyLoop

/-!
The literal sheaf scalar acts termwise on original perfect complexes and gives a whole coherent
spectrum homotopy for genuine flat pullback. Original normalized composition homotopies are
retained.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum

/-- The actual normalized spectrum map of a genuinely flat geometric morphism. -/
def perfectFlatPrespectrumMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    originalPrespectrum (perfectWaldhausen Y) ⟶ originalPrespectrum (perfectWaldhausen X) :=
  exactOriginalPrespectrumMap _ _ (perfectFlatPullback_waldhausenExact f)

/-- An original global unit gives the full structure-compatible self-homotopy of flat pullback. -/
def perfectFlatUnitHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (r : (Γ(X, ⊤))ˣ) :
    LoopPrespectrum.Homotopy (perfectFlatPrespectrumMap f) (perfectFlatPrespectrumMap f) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (perfectFlatPullback_waldhausenExact f)
    (perfectFlatPullback_waldhausenExact f) (perfectFlatPullbackUnitIso f r)

/-- The actual flat geometric composition comparison, including canonical spectrum normalization. -/
def perfectFlatPrespectrumCompHomotopy {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Flat f] [Flat g] :
    Homotopy (perfectFlatPrespectrumMap (f ≫ g))
      (perfectFlatPrespectrumMap g ≫ perfectFlatPrespectrumMap f) :=
  (exactOriginalPrespectrumIsoHomotopy _ _ (perfectFlatPullback_waldhausenExact (f ≫ g))
    ((perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f))
    (perfectFlatPullbackCompIso f g)).trans
      (exactOriginalPrespectrumMapCompHomotopy _ _ _
        (perfectFlatPullback_waldhausenExact g) (perfectFlatPullback_waldhausenExact f))


end Quillen.PerfectComplexes
