/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.StableSelfTrack
public import Quillen.Topology.Prespectrum.ConeLoopSeparation
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDeficit
public import Quillen.Waldhausen.SConstruction.Iterated.Separation

/-!
# Original sphere and deficit consumers of self-track vanishing

These retain the actual sphere, original cone inclusion and prescribed cone cylinder.
The geometric consumer discharges the positive stable obstruction using the accepted original
coarse-to-full-open deficit under its exact qcqs/qc hypotheses. Identification with the inherited
Laurent seed awaits its original full-open coefficient and whole seed comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.Tests.StableSelfTrack

/-- The original prespectrum track evaluates on precisely the displayed sphere. -/
theorem original_sphere_track {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ) (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n))
    (s : unitInterval) (z : Fin (m + 1) → unitInterval) :
    H.genLoopPath n p s z = H.level n (s, p z) := rfl

/-- The genuine second homotopy fixes the complete spatial boundary and both original times. -/
theorem original_relative_boundary {X : Type u} [TopologicalSpace X] {x : X}
    (m : ℕ) (p : GenLoop (Fin (m + 1)) X x)
    (H : p.val.HomotopyRel p.val (Cube.boundary (Fin (m + 1))))
    (K : (genLoopPathOfHomotopyRel H).Homotopy (Path.refl p))
    (r s : unitInterval) (z : Fin (m + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (m + 1))) :
    genLoopSelfTrackContraction H K (r, (s, z)) = x :=
  ((genLoopSelfTrackContraction H K).eq_fst r (Or.inr (Or.inr hz))).trans
    ((H.eq_fst s hz).trans (p.property z hz))

/-- The unchanged original cone transition induces zero in stable degree zero. -/
theorem original_cone_transition {E F : LoopPrespectrum.{u}}
    [∀ n, T1Space (E.space n)] [∀ n, T1Space (F.space n)]
    (f : E ⟶ F) (H : Homotopy f f) (hF : Subsingleton (stableHomotopyGroup F 1)) :
    (stableHomotopyFunctor 0).map (mappingConeLoopTransition f H) = 0 :=
  H.nullLoopMap_stableMap_zero (mappingConeInclusion f) (mappingConeHomotopy f) hF

/-- For the actual original deficit, qcqs/qc cofinality discharges the one-higher obstruction.
This retains the original map into that cone and the prescribed second cone contraction. -/
theorem original_deficit_target_self_track {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    {E : LoopPrespectrum.{u + 1}} [∀ n, T1Space (E.space n)]
    (f : E ⟶ PerfectComplexes.perfectOpenDeficit j) (H : Homotopy f f) :
    (stableHomotopyFunctor 0).map (mappingConeLoopTransition f H) = 0 := by
  let (n : ℕ) : T1Space ((PerfectComplexes.perfectOpenDeficit j).space n) := by
    change T1Space ((mappingCone (PerfectComplexes.perfectOpenRestrictPrespectrumMap j)).space n)
    infer_instance
  exact original_cone_transition f H
    (PerfectComplexes.perfectOpenDeficit_stableHomotopyGroup_subsingleton j 1 (by decide))

end Quillen.Tests.StableSelfTrack
