/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HELP.ContractibleTestFull
public import Quillen.Topology.HELP.PairLifting
public import Quillen.Topology.HELP.CompactRealizationLifting
public import Quillen.Topology.ClassifyingSpace.Equivalence

/-! # Actual realized-inclusion lifting from compact HELP on genuine fibers

The displayed strict-fiber premise solves every compact contracted simplex
test, preserving the full boundary homotopy. Actual relative skeleta then
supply endpoint lifting against all realized simplicial monomorphisms. No
inverse family on an arbitrary path-space pullback is chosen or assumed.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.MappingPath
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- The actual mapping-path endpoint lifts against every realized simplicial
mono, from genuine fibration structure and compact HELP on its original
strict-fiber maps. The test realization need not be compact. -/
theorem endpoint_realization_mono_of_fiberHELP
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq b))
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i) (TopCat.ofHom (endpoint f)) := by
  apply hasLiftingProperty_realization_mono
  intro n
  have : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
  let : ContractibleSpace |(Δ[n] : SSet.{u})| := by
    let : ContractibleSpace |nerve (ULift.{u} (Fin (n+1)))| := by
      change ContractibleSpace (ClassifyingSpace (ULift.{u} (Fin (n+1))))
      infer_instance
    exact (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.isoNerve n))).contractibleSpace
  obtain ⟨d, ⟨HD⟩⟩ := id_nullhomotopic |(Δ[n] : SSet.{u})|
  apply endpoint_hasLiftingProperty_of_pairHELP f
  intro a b H
  exact fullHELP_on_contracted_test p q f sq hp hq hf _ _ _
    (Quillen.Realization.homotopyExtensionProperty_realizationBoundary n) d HD a b H

end Quillen.MappingPath
