/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopPrefixNullCoherence
public import Quillen.Waldhausen.Additivity.CompactCoproductSpatial

/-! Original degree-one, whole-path naturality and complete spatial-boundary consumers. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Quillen
open scoped Topology unitInterval
universe u v
namespace QuillenTest.GenLoopPrefixNullCoherence
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- One original spatial coordinate already supports the exact supplied-null homotopy. -/
def actual_degree_one_null (rho q c : GenLoop (Fin 1) X x)
    (N : Path c GenLoop.const) (nu : Path (GenLoop.transAt 0 rho q) GenLoop.const) :
    ((((N.map (GenLoopPrefix.prefixMap 0 q).continuous).trans (GenLoopPrefix.rightUnit 0 q)).map
      (GenLoopPrefix.prefixMap 0 rho).continuous).trans nu).Homotopy
      ((GenLoopPrefix.tail 0 rho q c nu).trans N) :=
  GenLoopPrefix.nullCoherence 0 rho q c N nu

/-- The generic suffix removal is exactly the accepted original compact-family suffix removal. -/
theorem original_compact_right_unit (n : ℕ) (q : GenLoop (Fin (n + 1)) X x) :
    GenLoopPrefix.rightUnit n q = genLoopRightUnitPath n q := rfl

/-- The full coordinate-zero associator is the image of the original path associator. -/
theorem original_associator (n : ℕ) (p q r : GenLoop (Fin (n + 1)) X x)
    (t : unitInterval) :
    GenLoopPrefix.associator n p q r t =
      GenLoop.fromLoop 0 ((Path.Homotopy.transAssoc (GenLoop.toLoop 0 p)
        (GenLoop.toLoop 0 q) (GenLoop.toLoop 0 r)).eval t) := rfl

/-- Both original unit tracks keep their actual common endpoints before any cancellation. -/
theorem actual_constant_unit_endpoints (n : ℕ) :
    (GenLoopPrefix.rightUnit n (GenLoop.const : GenLoop (Fin (n + 1)) X x) :
      Path (GenLoop.transAt (0 : Fin (n + 1))
        (GenLoop.const : GenLoop (Fin (n + 1)) X x) GenLoop.const) GenLoop.const) =
      GenLoopPrefix.leftUnit n GenLoop.const :=
  GenLoopPrefix.unit_const n

/-- The entire null path is still the final segment at the final homotopy time. -/
theorem actual_entire_supplied_null (n : ℕ) (rho q c : GenLoop (Fin (n + 1)) X x)
    (N : Path c GenLoop.const) (nu : Path (GenLoop.transAt 0 rho q) GenLoop.const)
    (t : unitInterval) :
    GenLoopPrefix.nullCoherence n rho q c N nu (1, t) =
      ((GenLoopPrefix.tail n rho q c nu).trans N) t :=
  (GenLoopPrefix.nullCoherence n rho q c N nu).apply_one t

/-- Every intermediate homotopy and path time retains the whole original cube boundary. -/
theorem entire_spatial_boundary (n : ℕ) (rho q c : GenLoop (Fin (n + 1)) X x)
    (N : Path c GenLoop.const) (nu : Path (GenLoop.transAt 0 rho q) GenLoop.const)
    (s t : unitInterval) (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    GenLoopPrefix.nullCoherence n rho q c N nu (s, t) z = x :=
  (GenLoopPrefix.nullCoherence n rho q c N nu (s, t)).property z hz

variable {Y : Type v} [TopologicalSpace Y] {y : Y}

/-- Whole cancellation naturality retains both displayed endpoint transports even in degree one. -/
theorem actual_degree_one_cancellation_naturality (f : C(X, Y)) (h : f x = y)
    (a : GenLoop (Fin 1) X x) :
    ((GenLoopPrefix.cancellation 0 a).map (genLoopPostcompContinuousMap f h).continuous).cast
      (GenLoopPrefix.inversePrefix_map 0 f h a a).symm (genLoopPostcomp_const f h).symm =
      GenLoopPrefix.cancellation 0 (genLoopPostcomp f h a) :=
  GenLoopPrefix.cancellation_map 0 f h a

/-- The entire supplied return and all spatial coordinates survive the actual mapped tail. -/
theorem actual_whole_tail_naturality (n : ℕ) (f : C(X, Y)) (h : f x = y)
    (rho q c : GenLoop (Fin (n + 1)) X x)
    (nu : Path (GenLoop.transAt 0 rho q) GenLoop.const) :
    ((GenLoopPrefix.tail n rho q c nu).map (genLoopPostcompContinuousMap f h).continuous).cast
      (GenLoopPrefix.tail_source_map n f h rho q c).symm rfl =
      GenLoopPrefix.tail n (genLoopPostcomp f h rho) (genLoopPostcomp f h q)
        (genLoopPostcomp f h c) (GenLoopPrefix.mappedReturn n f h rho q nu) :=
  GenLoopPrefix.tail_map n f h rho q c nu

end QuillenTest.GenLoopPrefixNullCoherence
