/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Path.PointHEP
public import Quillen.Topology.Prespectrum.ParameterLooping

/-!
# Well-based points of actual parameter-correct looping

At each original level, a closed chosen point with HEP remains well-based under
the unchanged compact-open parameter-looping construction. The independent
structure parameter and the actual loop-space basepoint are untouched.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum

/-- Original closed point HEP is preserved at each actual parameter-looping level. -/
theorem parameterLooping_point_homotopyExtensionProperty (E : LoopPrespectrum.{u}) (n : ℕ)
    (hc : IsClosed ({E.point n} : Set (E.space n)))
    (h : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n)))) :
    Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((parameterLooping E).point n))) :=
  path_refl_homotopyExtensionProperty hc h

end Quillen.LoopPrespectrum
