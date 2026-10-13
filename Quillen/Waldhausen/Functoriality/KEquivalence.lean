/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Functoriality.KMap
public import Quillen.Topology.HomotopyGroups.Equivalence
public import Quillen.Topology.HomotopyFiber.SourceEquivalence

/-! # Canonical K-equivalences from actual realization equivalences

The input identifies the forward realization map of the original exact
functor with a genuine homotopy equivalence. Its canonical zero rebasing is
homotopic to that actual map, so the existing original `KMap` is bijective.
No pointed inverse or fixed inverse homotopy is required.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v

namespace Quillen.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {V : Structure C} {W : Structure D} {F : C ⥤ D}
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (e : ContinuousMap.HomotopyEquiv V.Delooping W.Delooping)
variable (he : e.toFun = (deloopingMap hF).hom)

/-- Actual canonical zero normalization retains the original realization
homotopy equivalence by its concrete natural-isomorphism homotopy. -/
def rebasedRealizationHomotopyEquiv : ContinuousMap.HomotopyEquiv V.Delooping W.Delooping := by
  have h : (deloopingMap hF.rebase).hom.Homotopic (deloopingMap hF).hom :=
    ⟨weakNaturalTransformationRealizationHomotopy V W hF.rebase hF
      (Quillen.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)).inv
      (fun _ ↦ W.weq_iso _ inferInstance)⟩
  rw [← he] at h
  exact HomotopyFiber.replaceForward e (deloopingMap hF.rebase).hom h

/-- The new forward map is exactly the canonical normalization used by KMap. -/
@[simp] theorem rebasedRealizationHomotopyEquiv_toFun :
    (rebasedRealizationHomotopyEquiv hF e he).toFun = (deloopingMap hF.rebase).hom := rfl

include e he in
/-- The original canonical based K-map of a genuine realization equivalence
is bijective, including degree zero. -/
theorem KMap_bijective_of_realizationHomotopyEquiv (n : ℕ) : Function.Bijective (KMap hF n) := by
  rw [KMap_eq_piMap hF n]
  exact Quillen.piMap_bijective_of_homotopyEquiv
    (rebasedRealizationHomotopyEquiv hF e he) (KMap_basepoint hF) n

/-- The actual canonical K-map, packaged as a group equivalence. -/
def KEquivOfRealization (n : ℕ) : V.K n ≃* W.K n :=
  MulEquiv.ofBijective (KMap hF n) (KMap_bijective_of_realizationHomotopyEquiv hF e he n)

/-- The forward homomorphism is definitionally the unchanged original K-map. -/
@[simp] theorem KEquivOfRealization_coe (n : ℕ) :
    (↑(KEquivOfRealization hF e he n) : V.K n →* W.K n) = KMap hF n := rfl


end Quillen.Waldhausen
