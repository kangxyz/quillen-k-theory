/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberCubeReturn
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberInclusionDiagonal
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarUnitTrackOperation
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationLevelOne
public import Quillen.Topology.Prespectrum.SelfTrackRelativeHomotopy
public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackNaturality
public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackTimeOperations

/-!
# The original signed scalar return represents the actual scalar operation

The entire inclusion/projection loop is carried forward by the actual small-model homeomorphism.
Its source equality is derived at time zero and used at both endpoints. The existing original
prespectrum composition track then identifies its normalized class with the scalar operation,
with exactly the level-one inverse. The literal signed return has the opposite orientation,
so its class is the original operation, also in degree zero. A separate corollary retains the
actual raw-to-rebased normalization prefix; restriction uses the proved whole flat-unit track.

These comparisons do not construct the geometric Theta/null square or identify the normalized
fiber endpoint with the canonical acyclic cone. Those require their own whole-path hypotheses.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology Simplicial
universe u v
namespace Quillen

private theorem scalarReturnClass_endpointCast {Y : Type v} [TopologicalSpace Y] {y : Y}
    (n : ℕ) {a b : GenLoop (Fin (n + 1)) Y y} (h : b = a) (P : Path a a) :
    genLoopSelfTrackClass n b (P.cast h h) = genLoopSelfTrackClass n a P := by
  subst b
  rfl

namespace PerfectComplexes
local instance scalarReturnClassCoproducts (X : Scheme.{u}) : HasBinaryCoproducts (Perfect X) :=
  Additivity.hasBinaryCoproducts (perfectWaldhausen X)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
    (subdivisionBasepoint (perfectWaldhausen X)))
local notation "V" => perfectWaldhausen X
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "af" => scalarFineAdditivitySourceCube X (𝟙 (𝟭 (Perfect X)))
  (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X)) n p
local notation "b" => perfectOpenScalarCubeChangeWeak j n af
local notation "pSmall" => genLoopPostcomp
  (ContinuousMap.HomotopyEquiv.toFun (Homeomorph.toHomotopyEquiv
    (Structure.smallModelDeloopingHomeomorph (perfectWaldhausen X))))
  (Structure.smallModelDeloopingHomeomorph_basepoint (perfectWaldhausen X))
  (perfectScalarProjectionInputCube n p)

/-- The entire cast inclusion edge is the original ordinary inclusion cylinder. -/
theorem perfectOpenScalarFineCubeInclusionPath_ordinary (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarFineCubeInclusionPath j r q hq n p t z =
      perfectOpenScalarInclusionRealizationHomotopy j r q hq
        (t, separatedFirstDeloopingMap V (p z)) := by
  change perfectOpenScalarCofiberCubeSquare j r q hq n p (t, 0) z = _
  rw [perfectOpenScalarCofiberCubeSquare_additivity_zero]
  exact perfectOpenScalarInclusionDiagonalRealization j r q hq t
    (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) (p z))

/-- Forward transport preserves every inclusion time and every original cube coordinate. -/
theorem perfectOpenScalarFineCubeInclusionPath_smallModel_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    (perfectOpenScalarInclusionHomotopy j r q hq).genLoopPath 1 pSmall t z =
      (W).smallModelDeloopingHomeomorph
        (perfectOpenScalarFineCubeInclusionPath j r q hq n p t z) := by
  rw [perfectOpenScalarFineCubeInclusionPath_ordinary]
  exact perfectOpenScalarInclusionHomotopy_level_one j r q hq t
    (separatedFirstDeloopingMap V (p z))

/-- The same-rebase fine projection has its literal coarse image under forward transport. -/
theorem perfectOpenScalarFineProjectionCubePath_smallModel_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    (perfectOpenScalarProjectionHomotopy j r).genLoopPath 1 pSmall t z =
      (W).smallModelDeloopingHomeomorph
        (perfectOpenScalarCubeChangeWeak j n
          (perfectOpenScalarFineProjectionCubePath j r n p t) z) := by
  rw [perfectOpenScalarFineProjectionCubePath_changeWeak]
  exact perfectOpenScalarProjectionHomotopy_level_one j r t
    (separatedFirstDeloopingMap V (p z))

/-- The literal coarse loop uses the entire original inclusion and mapped fine projection. -/
def perfectOpenScalarCubeCompositionPath : Path b b :=
  (perfectOpenScalarFineCubeInclusionPath j r q hq n p).trans
    ((perfectOpenScalarFineProjectionCubePath j r n p).map
      (perfectOpenScalarCubeChangeWeak j n).continuous)

/-- Forward transport keeps exactly the two original concatenation halves. -/
theorem perfectOpenScalarCubeCompositionPath_smallModel_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    ((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).genLoopPath 1 pSmall t z =
      (W).smallModelDeloopingHomeomorph
        (perfectOpenScalarCubeCompositionPath j r q hq n p t z) := by
  rw [Homotopy.genLoopPath_trans]
  unfold perfectOpenScalarCubeCompositionPath
  simp only [Path.trans_apply]
  split_ifs
  · exact perfectOpenScalarFineCubeInclusionPath_smallModel_apply j r q hq n p _ z
  · exact perfectOpenScalarFineProjectionCubePath_smallModel_apply j r n p _ z

include r q hq in
/-- The source comparison is derived from time zero of the same entire composition loop. -/
theorem perfectOpenScalarCubeCompositionPath_smallModel_endpoint :
    genLoopPostcomp (W).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        (W).smallModelDeloopingHomeomorph_basepoint b =
      genLoopPostcomp
        ((exactOriginalPrespectrumMap V W (changeWeak_exact (perfectOpenNested j))).map 1)
        ((exactOriginalPrespectrumMap V W (changeWeak_exact (perfectOpenNested j))).map_point 1)
        pSmall := by
  apply GenLoop.ext
  intro z
  have hs := congrArg (fun a => a z)
    (perfectOpenScalarCubeCompositionPath j r q hq n p).source
  have ht := perfectOpenScalarCubeCompositionPath_smallModel_apply j r q hq n p 0 z
  have hH := congrArg (fun a => a z)
    (((perfectOpenScalarInclusionHomotopy j r q hq).trans
      (perfectOpenScalarProjectionHomotopy j r)).genLoopPath 1 pSmall).source
  exact (congrArg (W).smallModelDeloopingHomeomorph hs).symm.trans (ht.symm.trans hH)

/-- The full mapped loop uses the symmetric source equality at both endpoints. -/
theorem perfectOpenScalarCubeCompositionPath_smallModel :
    ((perfectOpenScalarCubeCompositionPath j r q hq n p).map
      (genLoopPostcompContinuousMap (W).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        (W).smallModelDeloopingHomeomorph_basepoint).continuous).cast
          (perfectOpenScalarCubeCompositionPath_smallModel_endpoint j r q hq n p).symm
          (perfectOpenScalarCubeCompositionPath_smallModel_endpoint j r q hq n p).symm =
      ((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).genLoopPath 1 pSmall := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro z
  exact (perfectOpenScalarCubeCompositionPath_smallModel_apply j r q hq n p t z).symm

/-- The existing original prespectrum triangle evaluates on the unchanged transported cube. -/
def perfectOpenScalarCompositionCubeHomotopy :
    ((perfectOpenScalarPrespectrumHomotopy j r q hq).genLoopPath 1 pSmall).Homotopy
      (((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).genLoopPath 1 pSmall) :=
  (perfectOpenScalarProjectionCompositionTrack j r q hq).genLoopPathHomotopy 1 n pSmall

/-- The entire original triangle evaluation retains the exact old relative-homotopy data. -/
theorem perfectOpenScalarCompositionCubeHomotopy_eq :
    perfectOpenScalarCompositionCubeHomotopy j r q hq n p =
      (perfectOpenScalarProjectionCompositionTrack j r q hq).genLoopPathHomotopy 1 n pSmall :=
  rfl

/-- Evaluating the entire original homotopy keeps both independent times and spatial coordinates. -/
theorem perfectOpenScalarCompositionCubeHomotopy_data_apply (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCompositionCubeHomotopy j r q hq n p (a, t) z =
      Homotopy.RelHomotopy.genLoopPathHomotopy
        (perfectOpenScalarProjectionCompositionTrack j r q hq) 1 n pSmall (a, t) z :=
  congrArg (fun Q => Q (a, t) z)
    (perfectOpenScalarCompositionCubeHomotopy_eq j r q hq n p)

/-- The original normalized scalar operation is the inverse class of the whole composition loop. -/
theorem perfectOpenScalarKOperation_compositionCube :
    originalKSelfTrackOperation V W (perfectOpenScalarPrespectrumHomotopy j r q hq) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) =
      (genLoopSelfTrackClass n b (perfectOpenScalarCubeCompositionPath j r q hq n p))⁻¹ := by
  let H := perfectOpenScalarPrespectrumHomotopy j r q hq
  let T := (perfectOpenScalarInclusionHomotopy j r q hq).trans
    (perfectOpenScalarProjectionHomotopy j r)
  let L := (W).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
  let P := perfectOpenScalarCubeCompositionPath j r q hq n p
  have hc : genLoopSelfTrackClass n _ (T.genLoopPath 1 pSmall) =
      (W).smallModelKEquiv (n + 1) (genLoopSelfTrackClass n b P) := by
    rw [← perfectOpenScalarCubeCompositionPath_smallModel j r q hq n p,
      scalarReturnClass_endpointCast]
    exact (genLoopSelfTrackClass_naturality L
      (W).smallModelDeloopingHomeomorph_basepoint n b P).symm
  apply ((W).smallModelKEquiv (n + 1)).injective
  calc
    (W).smallModelKEquiv (n + 1)
        (originalKSelfTrackOperation V W H n ⟦perfectScalarProjectionInputCube n p⟧) =
        (H.homotopyClassOperation 1 n
          ((V).smallModelKEquiv n ⟦perfectScalarProjectionInputCube n p⟧))⁻¹ :=
      originalKSelfTrackOperation_levelOne V W H n ⟦perfectScalarProjectionInputCube n p⟧
    _ = (T.homotopyClassOperation 1 n
          ((V).smallModelKEquiv n ⟦perfectScalarProjectionInputCube n p⟧))⁻¹ :=
      congrArg Inv.inv (Homotopy.RelHomotopy.homotopyClassOperation_eq
        (perfectOpenScalarProjectionCompositionTrack j r q hq) 1 n _)
    _ = (genLoopSelfTrackClass n _ (T.genLoopPath 1 pSmall))⁻¹ := rfl
    _ = ((W).smallModelKEquiv (n + 1) (genLoopSelfTrackClass n b P))⁻¹ :=
      congrArg Inv.inv hc
    _ = (W).smallModelKEquiv (n + 1) (genLoopSelfTrackClass n b P)⁻¹ :=
      (map_inv ((W).smallModelKEquiv (n + 1)) _).symm

/-- The literal signed return represents the original normalized operation,
including degree zero. -/
theorem perfectOpenScalarCubeReturn_class :
    genLoopSelfTrackClass n b
        (((perfectOpenScalarFineCubeReturn j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).trans
            (perfectOpenScalarFineCubeTerminalWord j r q hq n p)) =
      originalKSelfTrackOperation V W (perfectOpenScalarPrespectrumHomotopy j r q hq) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) := by
  calc
    _ = genLoopSelfTrackClass n b
        (perfectOpenScalarCubeCompositionPath j r q hq n p).symm :=
      (genLoopSelfTrackClass_eq_iff n b _ _).mpr
        ⟨perfectOpenScalarCubeReturnHomotopy j r q hq n p⟩
    _ = (genLoopSelfTrackClass n b
        (perfectOpenScalarCubeCompositionPath j r q hq n p))⁻¹ :=
      genLoopSelfTrackClass_symm n b _
    _ = _ := (perfectOpenScalarKOperation_compositionCube j r q hq n p).symm

/-- The raw scalar corollary retains the actual normalization prefix and whole intertwining. -/
theorem perfectOpenScalarCubeReturn_originalClass :
    genLoopSelfTrackClass n b
        (((perfectOpenScalarFineCubeReturn j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).trans
            (perfectOpenScalarFineCubeTerminalWord j r q hq n p)) =
      originalKSelfTrackOperation V W (perfectOpenScalarOriginalHomotopy j r q hq) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) := by
  rw [perfectOpenScalarCubeReturn_class]
  exact congrArg (fun f => f (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n))
    (originalKSelfTrackOperation_intertwine V W
      (perfectOpenScalarOriginalHomotopy j r q hq)
      (perfectOpenScalarPrespectrumHomotopy j r q hq)
      (perfectOpenChangeWeakNormalizationHomotopy j)
      (perfectOpenScalarNormalizationTrack j r q hq) n).symm

/-- Restriction gives the actual flat-unit operation through its proved whole track comparison. -/
theorem perfectOpenScalarCubeReturn_class_restrict :
    KMap (perfectOpenRestrict_waldhausenExact j) (n + 1)
        (genLoopSelfTrackClass n b
          (((perfectOpenScalarFineCubeReturn j r n p).map
            (perfectOpenScalarCubeChangeWeak j n).continuous).trans
              (perfectOpenScalarFineCubeTerminalWord j r q hq n p))) =
      originalKSelfTrackOperation V (perfectWaldhausen U) (perfectFlatUnitHomotopy j q) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) := by
  rw [perfectOpenScalarCubeReturn_class]
  exact congrArg (fun f => f (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n))
    (perfectOpenScalarKOperation_restrict j r q hq n)

end PerfectComplexes
end Quillen
