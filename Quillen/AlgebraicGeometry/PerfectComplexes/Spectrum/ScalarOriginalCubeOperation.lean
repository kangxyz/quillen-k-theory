/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarUnitTrackTransport
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationLevelOne
public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackNaturality

/-!
# The original scalar cube represents its actual K-operation

The literal raw scalar cylinder on every original based cube is transported through the actual
small-model homeomorphism, with both endpoint casts explicit. The original K-operation is the
inverse normalized class of that same track, including degree zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
open scoped Topology
universe u v
namespace Quillen

private theorem genLoopSelfTrackClass_endpointCast {Y : Type v} [TopologicalSpace Y] {y : Y}
    (n : ℕ) {a b : GenLoop (Fin (n + 1)) Y y} (h : b = a) (P : Path a a) :
    genLoopSelfTrackClass n b (P.cast h h) = genLoopSelfTrackClass n a P := by
  subst b
  rfl

namespace PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    (perfectWaldhausen X).Delooping (perfectWaldhausen X).kBasepoint)

/-- The actual raw scalar realization cylinder evaluated on the entire original based cube. -/
def perfectOpenScalarCubePath :
    Path (genLoopPostcomp (changeWeakMap (perfectOpenNested j))
      (changeWeakMap_basepoint (perfectOpenNested j)) p)
      (genLoopPostcomp (changeWeakMap (perfectOpenNested j))
        (changeWeakMap_basepoint (perfectOpenNested j)) p) :=
  genLoopPathOfHomotopyRel (genLoopPostcompHomotopy
    (changeWeakMap_basepoint (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j))
    (weakNaturalTransformationRealizationHomotopy (perfectWaldhausen X)
      (perfectOpenWeakWaldhausen j) (changeWeak_exact (perfectOpenNested j))
      (changeWeak_exact (perfectOpenNested j)) (perfectGlobalScalar X r)
      (perfectGlobalScalar_openWeak j r q hq))
    (weakNaturalTransformationRealizationHomotopy_fixed_zero (perfectWaldhausen X)
      (perfectOpenWeakWaldhausen j) (changeWeak_exact (perfectOpenNested j))
      (changeWeak_exact (perfectOpenNested j)) (perfectGlobalScalar X r)
      (perfectGlobalScalar_openWeak j r q hq) (perfectOpenNested j).zero_eq.symm
      (perfectOpenNested j).zero_eq.symm) p)

/-- Neither the scalar time nor any original spatial coordinate is changed. -/
@[simp] theorem perfectOpenScalarCubePath_apply (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCubePath j r q hq n p s z =
      weakNaturalTransformationRealizationHomotopy (perfectWaldhausen X)
        (perfectOpenWeakWaldhausen j) (changeWeak_exact (perfectOpenNested j))
        (changeWeak_exact (perfectOpenNested j)) (perfectGlobalScalar X r)
        (perfectGlobalScalar_openWeak j r q hq) (s, p z) := rfl

/-- The entire original scalar path agrees with the actual level-one track after transport. -/
theorem perfectOpenScalarCubePath_smallModel_apply (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    (perfectOpenScalarOriginalHomotopy j r q hq).genLoopPath 1
        (genLoopPostcomp (perfectWaldhausen X).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
          (perfectWaldhausen X).smallModelDeloopingHomeomorph_basepoint p) s z =
      (perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph
        (perfectOpenScalarCubePath j r q hq n p s z) :=
  perfectOpenScalarOriginalHomotopy_level_one j r q hq s (p z)

include r q hq in
/-- The two source endpoints coincide by the time-zero equation of the same actual track. -/
theorem perfectOpenScalarCubePath_smallModel_endpoint :
    genLoopPostcomp
        (perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        (perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph_basepoint
        (genLoopPostcomp (changeWeakMap (perfectOpenNested j))
          (changeWeakMap_basepoint (perfectOpenNested j)) p) =
      genLoopPostcomp ((changeWeakPrespectrumMap (perfectOpenNested j)).map 1)
        ((changeWeakPrespectrumMap (perfectOpenNested j)).map_point 1)
        (genLoopPostcomp (perfectWaldhausen X).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
          (perfectWaldhausen X).smallModelDeloopingHomeomorph_basepoint p) := by
  apply GenLoop.ext
  intro z
  have hs := congrArg (fun a => a z) (perfectOpenScalarCubePath j r q hq n p).source
  have ht := perfectOpenScalarCubePath_smallModel_apply j r q hq n p 0 z
  have hH := congrArg (fun a => a z)
    ((perfectOpenScalarOriginalHomotopy j r q hq).genLoopPath 1
      (genLoopPostcomp (perfectWaldhausen X).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        (perfectWaldhausen X).smallModelDeloopingHomeomorph_basepoint p)).source
  exact (congrArg (perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph hs).symm.trans
    (ht.symm.trans hH)

/-- Both endpoint casts retain the literal whole path and its actual source equality. -/
theorem perfectOpenScalarCubePath_smallModel :
    ((perfectOpenScalarCubePath j r q hq n p).map
      (genLoopPostcompContinuousMap
        (perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        (perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph_basepoint).continuous).cast
          (perfectOpenScalarCubePath_smallModel_endpoint j r q hq n p).symm
          (perfectOpenScalarCubePath_smallModel_endpoint j r q hq n p).symm =
      (perfectOpenScalarOriginalHomotopy j r q hq).genLoopPath 1
        (genLoopPostcomp (perfectWaldhausen X).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
          (perfectWaldhausen X).smallModelDeloopingHomeomorph_basepoint p) := by
  apply Path.ext
  funext s
  apply GenLoop.ext
  intro z
  exact (perfectOpenScalarCubePath_smallModel_apply j r q hq n p s z).symm

/-- The actual raw K-operation is the inverse class of this original scalar cube in every degree. -/
theorem perfectOpenScalarOriginalKOperation_cube :
    originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) n
        (⟦p⟧ : (perfectWaldhausen X).K n) =
      (genLoopSelfTrackClass n
        (genLoopPostcomp (changeWeakMap (perfectOpenNested j))
          (changeWeakMap_basepoint (perfectOpenNested j)) p)
        (perfectOpenScalarCubePath j r q hq n p))⁻¹ := by
  let W := perfectWaldhausen X
  let V := perfectOpenWeakWaldhausen j
  let H := perfectOpenScalarOriginalHomotopy j r q hq
  let L := V.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
  let a := genLoopPostcomp (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j)) p
  let P := perfectOpenScalarCubePath j r q hq n p
  let p' := genLoopPostcomp W.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
    W.smallModelDeloopingHomeomorph_basepoint p
  have hc : genLoopSelfTrackClass n _ (H.genLoopPath 1 p') =
      V.smallModelKEquiv (n + 1) (genLoopSelfTrackClass n a P) := by
    rw [← perfectOpenScalarCubePath_smallModel j r q hq n p,
      genLoopSelfTrackClass_endpointCast]
    exact (genLoopSelfTrackClass_naturality L
      V.smallModelDeloopingHomeomorph_basepoint n a P).symm
  apply (V.smallModelKEquiv (n + 1)).injective
  calc
    V.smallModelKEquiv (n + 1) (originalKSelfTrackOperation W V H n ⟦p⟧) =
        (H.homotopyClassOperation 1 n (W.smallModelKEquiv n ⟦p⟧))⁻¹ :=
      originalKSelfTrackOperation_levelOne W V H n ⟦p⟧
    _ = (genLoopSelfTrackClass n _ (H.genLoopPath 1 p'))⁻¹ := rfl
    _ = (V.smallModelKEquiv (n + 1) (genLoopSelfTrackClass n a P))⁻¹ :=
      congrArg Inv.inv hc
    _ = V.smallModelKEquiv (n + 1) (genLoopSelfTrackClass n a P)⁻¹ :=
      (map_inv (V.smallModelKEquiv (n + 1)) _).symm

end PerfectComplexes
end Quillen
