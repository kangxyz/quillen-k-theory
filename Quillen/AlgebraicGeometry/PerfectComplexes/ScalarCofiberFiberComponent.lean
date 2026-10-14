/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyFiber.LoopComponentTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberKOneNormalization

/-! # Actual scalar-cofiber component transport

The original fine identity-cofiber suffix supplies the component equivalence.
Its whole image is the original coarse suffix. The unchanged canonical fiber
point is exactly the image of its original constant-component transpose.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.PerfectComplexes
open scoped Topology
universe u
namespace Quillen.BassLaurentUnitBoundary

private theorem transport_map_cast {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y z : Y} (h : f x = y) (p : Path y z) (n : ℕ)
    (a : HomotopyGroup.Pi n X x) :
    pathTransport (p.cast h rfl) n (homotopyGroupMap f rfl a) =
      pathTransport p n (homotopyGroupMap f h a) := by
  cases h
  rfl

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (K : Perfect X)

/-- The genuine equivalence uses the original object loops and fine identity-cofiber suffix. -/
def scalarFiberComponentEquiv :=
  fiberComponentEquiv (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j)) ((perfectWaldhausen X).kZeroObjectLoop K)
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
      (perfectOpenNested j).zero_eq.symm K)
    ((perfectWaldhausen X).identityCofiberSuffixPath K)

/-- The full image suffix is precisely the original coarse identity-cofiber suffix. -/
theorem scalar_imageSuffix :
    imageSuffix (changeWeakMap (perfectOpenNested j))
      (changeWeakMap_basepoint (perfectOpenNested j)) ((perfectWaldhausen X).kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
        (perfectOpenNested j).zero_eq.symm K)
      ((perfectWaldhausen X).identityCofiberSuffixPath K) =
    ((perfectOpenNested j).coarse.identityCofiberSuffixPath K).cast
      (loopLeftTranslationEquiv_apply _ _) rfl := by
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  exact identityCofiberSuffixPath_changeWeak (perfectOpenNested j) K s t

/-- The complete canonical fiber point is the actual translated original transpose. -/
theorem scalarFiberComponentEquiv_canonical (A : AcyclicCategory (perfectOpenNested j)) :
    scalarFiberComponentEquiv j K (canonicalFiberObjectLoopTranspose (perfectOpenNested j) A) =
      canonicalFiberObjectPrefixTransport (perfectOpenNested j) K A := by
  apply Subtype.ext
  apply Prod.ext
  · change (fiberComponentEquiv _ _ _ _ _ _ _).val.1 = _
    rw [fiberComponentEquiv_source, canonicalFiberObjectLoopTranspose_source]
    rfl
  · change (fiberComponentEquiv _ _ _ _ _ _ _).val.2 = _
    rw [fiberComponentEquiv_path, scalar_imageSuffix,
      canonicalFiberObjectPrefixTransport_path]
    rfl

/-- The original translated double loop, with the actual coarse suffix retained. -/
def scalarComponentLoop
    (β : Path (Path.refl (perfectOpenNested j).coarse.kBasepoint)
      (Path.refl (perfectOpenNested j).coarse.kBasepoint)) :=
  componentLoop (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j)) ((perfectWaldhausen X).kZeroObjectLoop K)
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
      (perfectOpenNested j).zero_eq.symm K)
    ((perfectWaldhausen X).identityCofiberSuffixPath K) β

/-- The actual component loop has exactly the preexisting identity-cofiber equivalence class. -/
theorem scalarComponentLoop_class
    (β : Path (Path.refl (perfectOpenNested j).coarse.kBasepoint)
      (Path.refl (perfectOpenNested j).coarse.kBasepoint)) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
      ((perfectOpenNested j).coarse.identityCofiberComponentEquiv K 1
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm ⟦β⟧)) =
      ⟦scalarComponentLoop j K β⟧ := by
  have hc := componentLoop_class (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j)) ((perfectWaldhausen X).kZeroObjectLoop K)
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
      (perfectOpenNested j).zero_eq.symm K)
    ((perfectWaldhausen X).identityCofiberSuffixPath K) β
  rw [scalar_imageSuffix, transport_map_cast] at hc
  exact hc

end Quillen.BassLaurentUnitBoundary
