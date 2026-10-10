/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.Loop
public import Quillen.Topology.HomotopyGroups.WeakEquivalenceProperty
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Sequential Omega-spectra with original structure maps

The all-level Omega property requires that every actual adjoint structure map be a complete
weak homotopy equivalence, including its component condition. The corresponding full
subcategory retains exactly the original prespectrum morphisms. Construction of a particular
object must prove this property; the definition supplies no such proof.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum

/-- The actual adjoint structure maps are complete weak homotopy equivalences at every level. -/
def IsOmega (E : LoopPrespectrum.{u}) : Prop :=
  ∀ n, IsWeakHomotopyEquivalence (E.structureMap n)

/-- Sequential Omega-spectra are the full subcategory on the proved all-level property. -/
abbrev OmegaSpectrum := ObjectProperty.FullSubcategory (IsOmega : ObjectProperty
    LoopPrespectrum.{u})


end Quillen.LoopPrespectrum
