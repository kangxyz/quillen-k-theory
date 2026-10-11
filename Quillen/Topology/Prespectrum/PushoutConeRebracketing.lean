/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.HomotopyPushout
public import Quillen.Topology.Prespectrum.MappingCone
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# Literal rebracketing of the original pushout's right-inclusion cone

The unchanged cone of C→HPO(f,g) is isomorphic to the actual reduced pushout of f and
A→C→cone(id_C). The two original cylinders are kept separately with their full parameters.
The inverse maps are proved on all original quotient generators; no homotopy or point-set
assumption enters this strict comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped unitInterval
universe u
namespace Quillen.LoopPrespectrum.HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- The actual map inserting the right endpoint into its original identity cone. -/
def intoRightCone : prespectrum f g ⟶ prespectrum f (g ≫ mappingConeInclusion (𝟙 C)) :=
  map f g f (g ≫ mappingConeInclusion (𝟙 C)) (𝟙 A) (𝟙 B)
    (mappingConeInclusion (𝟙 C)) (by simp) (by simp)

/-- The whole original C-cylinder gives the nullhomotopy after right-cone insertion. -/
def intoRightConeNull :
    Homotopy (inr f g ≫ intoRightCone f g)
      (zeroHom C (prespectrum f (g ≫ mappingConeInclusion (𝟙 C)))) :=
  ((mappingConeHomotopy (𝟙 C)).postcomp (inr f (g ≫ mappingConeInclusion (𝟙 C)))).cast
    (by apply Hom.ext; funext n; ext x; rfl)
    (by apply Hom.ext; funext n; ext x; exact (inr f _).map_point n)

/-- Rebracket the original two-cylinder quotient, retaining both cylinder parameters. -/
def rightConeRebracket : mappingCone (inr f g) ⟶
    prespectrum f (g ≫ mappingConeInclusion (𝟙 C)) :=
  mappingConeDesc (inr f g) (intoRightCone f g) (intoRightConeNull f g)

/-- The original C-cone maps to the actual cone on the original C inclusion. -/
def rightConeIntoCone : mappingCone (𝟙 C) ⟶ mappingCone (inr f g) :=
  mappingConeMap (Arrow.homMk (f := Arrow.mk (𝟙 C)) (g := Arrow.mk (inr f g))
    (𝟙 C) (inr f g) (by simp))

/-- The original overlap cylinder gives the full reverse rebracketing track. -/
def rightConeRebracketInvTrack :
    Homotopy (f ≫ (inl f g ≫ mappingConeInclusion (inr f g)))
      ((g ≫ mappingConeInclusion (𝟙 C)) ≫ rightConeIntoCone f g) :=
  ((glue f g).postcomp (mappingConeInclusion (inr f g))).cast
    (by rfl) (by apply Hom.ext; funext n; ext x; rfl)

/-- Reassemble the unchanged quotient from its two original separate cylinders. -/
def rightConeRebracketInv : prespectrum f (g ≫ mappingConeInclusion (𝟙 C)) ⟶
    mappingCone (inr f g) :=
  desc f (g ≫ mappingConeInclusion (𝟙 C)) (inl f g ≫ mappingConeInclusion (inr f g))
    (rightConeIntoCone f g) (rightConeRebracketInvTrack f g)

/-- The actual forward and reverse quotient descents are strict inverses on the original cone. -/
theorem rightConeRebracket_hom_inv :
    rightConeRebracket f g ≫ rightConeRebracketInv f g = 𝟙 (mappingCone (inr f g)) := by
  apply mappingCone_hom_ext
  · apply hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · intro n s x; rfl

/-- The same two descents are strict inverses on the actual rebracketed pushout. -/
theorem rightConeRebracket_inv_hom :
    rightConeRebracketInv f g ≫ rightConeRebracket f g =
      𝟙 (prespectrum f (g ≫ mappingConeInclusion (𝟙 C))) := by
  apply hom_ext
  · apply Hom.ext; funext n; ext x; rfl
  · apply mappingCone_hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · intro n s x; rfl

/-- The literal original right-inclusion cone is the rebracketed actual reduced pushout. -/
def rightConeRebracketIso : mappingCone (inr f g) ≅
    prespectrum f (g ≫ mappingConeInclusion (𝟙 C)) where
  hom := rightConeRebracket f g
  inv := rightConeRebracketInv f g
  hom_inv_id := rightConeRebracket_hom_inv f g
  inv_hom_id := rightConeRebracket_inv_hom f g

end Quillen.LoopPrespectrum.HomotopyPushout
