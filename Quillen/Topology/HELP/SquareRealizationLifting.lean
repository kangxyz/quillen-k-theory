/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HELP.FiberwiseRealizationLifting
public import Quillen.Topology.HomotopyFiber.WeakSquareTransport

/-! # Realized-inclusion lifting for original normalized strict squares

The actual mapping-path comparison is a map of genuine endpoint fibrations.
Its strict-fiber map is the original square's full path-space fiber map under
literal fiber homeomorphisms. Full compact fiber HELP therefore supplies
realized-monomorphism lifting for its actual mapping-path endpoint.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial Topology
universe u
namespace Quillen.MappingPath
variable {E F B B' : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace B] [TopologicalSpace B']
    {p : C(E, B)} {q : C(F, B')} (f : C(E, F)) (v : C(B, B')) (w : q.comp f = v.comp p)

/-- The actual normalized strict-fiber map inherits HELP from the original
square's fiber map. All entire original paths are retained. -/
theorem strictComparison_fiber_compactHELP (b : B)
    (hf : CompactHomotopyExtensionLiftingProperty (HomotopyFiber.map f v w.symm b)) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (endpoint p)
        (HomotopyPullback.strictBaseProjection (endpoint q) v)
        (strictComparison f v w) rfl b) := by
  let e₁ := endpointFiberHomeomorph p b
  let e₂ := (HomotopyPullback.strictPullbackFiberHomeomorph (endpoint q) v b).trans
    (endpointFiberHomeomorph q (v b))
  have hj₁ := compactHELP_of_homotopyEquiv e₁.toHomotopyEquiv
  have hj₂ := compactHELP_of_homotopyEquiv e₂.toHomotopyEquiv
  have hh : CompactHomotopyExtensionLiftingProperty
      (e₂.toHomotopyEquiv.toFun.comp
        (HomotopyFiber.strictMapOver (endpoint p)
          (HomotopyPullback.strictBaseProjection (endpoint q) v)
          (strictComparison f v w) rfl b)) := hf.comp hj₁
  exact hh.cancel_second hj₂

/-- Full HELP on every original square fiber yields actual RLP on all
realized simplicial inclusions for the normalized comparison's endpoint.
The underlying two original maps need not be fibrations. -/
theorem strictComparison_endpoint_realization_mono
    (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty (HomotopyFiber.map f v w.symm b))
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i)
      (TopCat.ofHom (endpoint (strictComparison f v w))) :=
  endpoint_realization_mono_of_fiberHELP (endpoint p)
    (HomotopyPullback.strictBaseProjection (endpoint q) v) (strictComparison f v w) rfl
    (endpoint_homotopyLiftingProperty p)
    (HomotopyLiftingProperty.baseChange (endpoint q) v (endpoint_homotopyLiftingProperty q))
    (fun b ↦ strictComparison_fiber_compactHELP f v w b (hf b)) i

end Quillen.MappingPath
