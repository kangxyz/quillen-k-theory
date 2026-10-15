/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.AffineTransport
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian

/-!
# Public locally noetherian scheme G-theory interface

Global G-theory is the K-theory of actual coherent sheaves in `Type (u + 1)`.
Its open-restriction homomorphism comes from geometric sheaf restriction.
The support group here is defined, without claiming a global localization LES.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme

/-- Genuine coherent G-theory in the explicit global small universe `u + 1`. -/
abbrev G (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    Type (u + 1) := AlgebraicGeometry.Scheme.Modules.Coherent.G X n

/-- The canonical G-map of actual geometric open restriction. -/
def restrictG {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) : G X n →* G U n :=
  AlgebraicGeometry.Scheme.Modules.Coherent.restrictionGMap j n

/-- The public restriction map retains the original exact-functor construction. -/
@[simp] theorem restrictG_eq_smallKMap {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    restrictG j n = (AlgebraicGeometry.Scheme.Modules.Coherent.coherentRestrictionExact j).smallKMap
      n := rfl

/-- G-theory of actual coherent sheaves supported outside the chosen open. -/
abbrev SupportedG {U X : AlgebraicGeometry.Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) : Type (u + 1) :=
  AlgebraicGeometry.Scheme.Modules.Coherent.SupportedG j n

end AlgebraicGeometry.Scheme
