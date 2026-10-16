/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit
public import Aglib.AlgebraicGeometry.Modules.Restriction.Sections

/-!
# Unit-sheaf maps from actual top sections

The original section construction, top-section extensionality, scalar equation and actual
restriction formula preserve their sheaf maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
/-- A section on the whole scheme, with all of its actual restrictions. -/
def moduleTopSection {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk (fun U =>
    (M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom s) (by
      intro U V f
      change (M.presheaf.map f).hom
        ((M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom s) = _
      rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp]
      rfl)

/-- The actual map from the unit module determined by a global section. -/
def unitMapOfTopSection {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf) ⟶ M :=
  M.unitHomEquiv.symm (moduleTopSection M s)

/-- The unit map acts by the original scalar action on restricted sections. -/
theorem unitMapOfTopSection_app {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤))
    (U : X.Opens) (r : Γ(X, U)) :
    Scheme.Modules.Hom.app (unitMapOfTopSection M s) U r =
      r • (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom s := rfl

/-- Maps from the actual unit sheaf are determined by their original global section. -/
theorem unit_hom_ext_top {X : Scheme.{u}} {M : X.Modules}
    {f g : (SheafOfModules.unit X.ringCatSheaf) ⟶ M}
    (h : Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤)) =
      Scheme.Modules.Hom.app g ⊤ (1 : Γ(X, ⊤))) : f = g := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  have hf := PresheafOfModules.sections_property (M.unitHomEquiv f)
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  have hg := PresheafOfModules.sections_property (M.unitHomEquiv g)
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  rw [← hf, ← hg]
  exact congrArg (fun x => (M.presheaf.map (homOfLE le_top).op).hom x) h

/-- Scalar multiplication of a section is literal precomposition with the
original structure-module scalar map. -/
theorem unitMapOfTopSection_smul {X : Scheme.{u}} (M : X.Modules)
    (r : Γ(X, ⊤)) (s : Γ(M, ⊤)) :
    unitMapOfTopSection M (r • s) = unitMul X r ≫ unitMapOfTopSection M s := by
  apply unit_hom_ext_top
  change Scheme.Modules.Hom.app (unitMapOfTopSection M (r • s)) ⊤ (1 : Γ(X, ⊤)) =
    Scheme.Modules.Hom.app (unitMapOfTopSection M s) ⊤
      (Scheme.Modules.Hom.app (unitMul X r) ⊤ (1 : Γ(X, ⊤)))
  simp [unitMapOfTopSection_app, unitMul_app]

/-- The original restriction of a global module section to the image of an open immersion. -/
def restrictedTopSection {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (s : Γ(M, ⊤)) : Γ(M.restrict j, ⊤) :=
  (M.presheaf.map (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op).hom s

/-- The original unit-restriction comparison carries the section map to the
map defined by its actual restricted global section. -/
theorem unitMapOfTopSection_restrict {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (s : Γ(M, ⊤)) :
    (Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map (unitMapOfTopSection M s) =
      unitMapOfTopSection (M.restrict j) (restrictedTopSection j M s) := by
  apply unit_hom_ext_top
  change Scheme.Modules.Hom.app (unitMapOfTopSection M s) (j ''ᵁ ⊤)
      ((j.appIso ⊤).inv.hom (1 : Γ(X, ⊤))) =
    Scheme.Modules.Hom.app (unitMapOfTopSection (M.restrict j)
      (restrictedTopSection j M s)) ⊤ (1 : Γ(X, ⊤))
  simp [unitMapOfTopSection_app, restrictedTopSection]

/-- Recover an arbitrary unit-sheaf map from its actual value at the global unit section. -/
theorem unitMapOfTopSection_of_map {X : Scheme.{u}} {M : X.Modules}
    (f : (SheafOfModules.unit X.ringCatSheaf) ⟶ M) :
    unitMapOfTopSection M (Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤))) = f := by
  apply unit_hom_ext_top
  simp [unitMapOfTopSection_app]


end Quillen.PerfectComplexes.ProjectiveLine
end
end
