/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.Point
public import Quillen.Topology.Prespectrum.HomotopyPushout
public import Quillen.Topology.Prespectrum.MappingCone
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# The original point-leg pushout and literal reduced cone

The reduced homotopy pushout of f and the actual map to the singleton prespectrum is isomorphic
to the unchanged mapping cone of f. Both original B inclusions and every A-cylinder value are
retained. The singleton endpoint maps to the actual cone point, with no replacement of either
quotient topology or any structure loop.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped unitInterval
universe u
namespace Quillen.LoopPrespectrum.HomotopyPushout
variable {A B : LoopPrespectrum.{u}} (f : A ⟶ B)

/-- The original cone cylinder supplies the point-leg pushout descent track. -/
def pointConeTrack : Homotopy (f ≫ mappingConeInclusion f)
    (zeroHom A pointPrespectrum ≫ zeroHom pointPrespectrum (mappingCone f)) :=
  (mappingConeHomotopy f).cast rfl rfl

/-- Send the actual point-leg pushout to the unchanged cone, with its full cylinder intact. -/
def pointConeMap : prespectrum f (zeroHom A pointPrespectrum) ⟶ mappingCone f :=
  desc f (zeroHom A pointPrespectrum) (mappingConeInclusion f)
    (zeroHom pointPrespectrum (mappingCone f)) (pointConeTrack f)

/-- The original point-leg pushout cylinder is based-null at its literal singleton endpoint. -/
def pointConeInvTrack :
    Homotopy (f ≫ inl f (zeroHom A pointPrespectrum))
      (zeroHom A (prespectrum f (zeroHom A pointPrespectrum))) :=
  (glue f (zeroHom A pointPrespectrum)).cast rfl
    (by
      apply Hom.ext
      funext n
      ext x
      exact right_point f (zeroHom A pointPrespectrum) n)

/-- Send the original cone into the actual point-leg pushout without changing its cylinder. -/
def pointConeInv : mappingCone f ⟶ prespectrum f (zeroHom A pointPrespectrum) :=
  mappingConeDesc f (inl f (zeroHom A pointPrespectrum)) (pointConeInvTrack f)

/-- The two actual descents are strict inverses on the original point-leg pushout. -/
theorem pointCone_hom_inv : pointConeMap f ≫ pointConeInv f =
    𝟙 (prespectrum f (zeroHom A pointPrespectrum)) := by
  apply hom_ext
  · apply Hom.ext; funext n; ext x; rfl
  · apply Hom.ext
    funext n
    ext x
    exact (right_point f (zeroHom A pointPrespectrum) n).symm
  · intro n s x; rfl

/-- The two actual descents are strict inverses on the original cone. -/
theorem pointCone_inv_hom : pointConeInv f ≫ pointConeMap f = 𝟙 (mappingCone f) := by
  apply mappingCone_hom_ext
  · apply Hom.ext; funext n; ext x; rfl
  · intro n s x; rfl

/-- The unchanged point-leg reduced pushout is literally isomorphic to the original cone. -/
def pointConeIso : prespectrum f (zeroHom A pointPrespectrum) ≅ mappingCone f where
  hom := pointConeMap f
  inv := pointConeInv f
  hom_inv_id := pointCone_hom_inv f
  inv_hom_id := pointCone_inv_hom f

end Quillen.LoopPrespectrum.HomotopyPushout
