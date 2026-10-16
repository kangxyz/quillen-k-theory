/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackHomotopyNaturality

/-! Original source and target maps are retained by the finite operation homomorphism. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackHomotopyNaturality

/-- Target naturality uses the actual supplied prespectrum map at the unchanged level. -/
theorem original_target_naturality {E F G : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (j : F ⟶ G) (n m : ℕ) :
    (H.postcomp j).homotopyClassOperationHom n m =
      (piMap (m + 2) (j.map n) (j.map_point n)).comp (H.homotopyClassOperationHom n m) :=
  H.homotopyClassOperationHom_postcomp j n m

/-- Source naturality uses the actual supplied prespectrum map on the original sphere. -/
theorem original_source_naturality {D E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (i : D ⟶ E) (n m : ℕ) :
    (H.precomp i).homotopyClassOperationHom n m =
      (H.homotopyClassOperationHom n m).comp (piMap (m + 1) (i.map n) (i.map_point n)) :=
  H.homotopyClassOperationHom_precomp i n m

end QuillenTest.SelfTrackHomotopyNaturality
