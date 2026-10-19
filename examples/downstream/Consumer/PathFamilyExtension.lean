/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.HELP.PathCubeExtension
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCubeExtension

/-!
# Fixed-endpoint path families in the actual common-reference carrier

The all-dimensional scalar producer supplies the only extension input. This consumer assumes
an actual continuous boundary family in the carrier; it does not lift a native K-theory family.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Simplicial Topology unitInterval

universe u

namespace Consumer.PathFamilyExtension

open Quillen.Waldhausen.IteratedS

/-- The existing common-reference producer extends every actual fixed-endpoint boundary family. -/
theorem common_reference_paths {V W : Model.{u}} (F : V ⟶ W) (n : ℕ)
    (a b : |nerve (Codiscrete (CommonReferenceNerve.Node F))|)
    (p : C({z : Fin n → I // z ∈ Cube.boundary (Fin n)}, Path a b)) :
    ∃ P : C(Fin n → I, Path a b), P.restrict (Cube.boundary (Fin n)) = p :=
  Quillen.CubicalTests.exists_extend_path_unlifted_boundary n
    (CommonReferenceNerve.exists_cube_extension F (n + 1)) p

/-- The entire original side is recovered with the boundary parameter and path time independent. -/
theorem common_reference_paths_apply {V W : Model.{u}} (F : V ⟶ W) (n : ℕ)
    (a b : |nerve (Codiscrete (CommonReferenceNerve.Node F))|)
    (p : C({z : Fin n → I // z ∈ Cube.boundary (Fin n)}, Path a b)) :
    ∃ P : C(Fin n → I, Path a b),
      ∀ (z : {z : Fin n → I // z ∈ Cube.boundary (Fin n)}) (t : I), P z.val t = p z t := by
  obtain ⟨P, hP⟩ := common_reference_paths F n a b p
  exact ⟨P, fun z t ↦ congrArg (fun q : Path a b ↦ q t) (DFunLike.congr_fun hP z)⟩

end Consumer.PathFamilyExtension
