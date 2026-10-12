/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberSourcePath
public import Quillen.Waldhausen.Fibration.CanonicalFiberObjectPrefixTransport

/-!
# The actual scalar-cofiber point in the iterated localization fiber

The source path is the prescribed fine cofiber triangle followed by the original fine weak
projection square. The target path is the original reversed canonical-fiber coordinate after
literal left prefix and identity-cofiber suffix. The existing iterated-fiber construction
therefore exposes the exact loop, including reversal of the mapped source path. Identification
with the Laurent-unit loop and the final boundary sign remain separate obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Topology
universe u
namespace Quillen.PerfectComplexes

/-- Curry the prescribed fine triangle-plus-projection track into its actual loop-space path. -/
def perfectScalarCofiberSourceLoopPath (X : Scheme.{u}) (r : Γ(X, ⊤)) (K : Perfect X) :
    Path (((perfectWaldhausen X).kZeroObjectLoop K).trans
      ((perfectWaldhausen X).kZeroObjectLoop
        ((ExtensionCategory.cofiber (perfectWaldhausen X)).obj (perfectScalarExtension X r K))))
      ((perfectWaldhausen X).kZeroObjectLoop K) where
  toFun s := (perfectScalarCofiberSourceTrack X r K).eval s
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (perfectScalarCofiberSourceTrack X r K).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

/-- Both coordinates are unchanged by currying the original fine track. -/
theorem perfectScalarCofiberSourceLoopPath_apply
    (X : Scheme.{u}) (r : Γ(X, ⊤)) (K : Perfect X) (s t : unitInterval) :
    perfectScalarCofiberSourceLoopPath X r K s t =
      perfectScalarCofiberSourceTrack X r K (s, t) := rfl

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (K : Perfect X)

/-- The unchanged canonical-fiber point carries the prescribed fine return path. -/
def perfectScalarCofiberIteratedFiber :
    HomotopyFiber.IteratedFiber
      (basedLoopMap (changeWeakMap (perfectOpenNested j)) (changeWeakMap_basepoint _))
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectWaldhausen X).kZeroObjectLoop K) := by
  refine ⟨(canonicalFiberObjectPrefixTransport (perfectOpenNested j) K
    (perfectOpenScalarCofiberAcyclic j r q hq K),
      (perfectScalarCofiberSourceLoopPath X r K).toContinuousMap), ?_, ?_⟩
  · exact (perfectScalarCofiberSourceLoopPath X r K).source
  · exact (perfectScalarCofiberSourceLoopPath X r K).target

/-- Apply the existing original iterated-fiber loop map to that exact displayed point. -/
def perfectScalarCofiberBoundaryLoop :
    Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K) :=
  HomotopyFiber.iteratedToLoops
    (basedLoopMap (changeWeakMap (perfectOpenNested j)) (changeWeakMap_basepoint _))
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    ((perfectWaldhausen X).kZeroObjectLoop K)
    (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
      (perfectOpenNested j).zero_eq.symm K)
    (perfectScalarCofiberIteratedFiber j r q hq K)

/-- The exact loop reverses the mapped fine source path before the original transported path. -/
theorem perfectScalarCofiberBoundaryLoop_eq :
    perfectScalarCofiberBoundaryLoop j r q hq K =
      (((perfectScalarCofiberSourceLoopPath X r K).map
        (basedLoopMap (changeWeakMap (perfectOpenNested j))
          (changeWeakMap_basepoint _)).continuous).symm.cast
        (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
          (perfectOpenNested j).zero_eq.symm K).symm rfl).trans
        (HomotopyFiber.toPath
          (basedLoopMap (changeWeakMap (perfectOpenNested j)) (changeWeakMap_basepoint _))
          ((perfectOpenNested j).coarse.kZeroObjectLoop K)
          (canonicalFiberObjectPrefixTransport (perfectOpenNested j) K
            (perfectOpenScalarCofiberAcyclic j r q hq K))) := rfl

end Quillen.PerfectComplexes
