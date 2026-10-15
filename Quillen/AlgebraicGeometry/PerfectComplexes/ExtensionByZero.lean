/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ExtensionByZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.Restriction
public import Mathlib.Algebra.Homology.Homotopy

/-! # Actual extension-by-zero adjunction on original sheaf complexes -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Apply genuine module-sheaf extension by zero in each original cochain degree. -/
def extensionByZero : Complex U ⥤ Complex X :=
  (AlgebraicGeometry.Scheme.Modules.extensionByZero j).mapHomologicalComplex (.up ℤ)

instance extensionByZero_additive : (extensionByZero j).Additive := by
  unfold extensionByZero
  infer_instance

/-- The actual chain-level adjunction, with original module unit and counit in every degree. -/
def extensionByZeroAdjunction : extensionByZero j ⊣ restrict j where
  unit := {
    app K := {
      f n := (AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction j).unit.app (K.X n)
      comm' p q _ := ((AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction
        j).unit.naturality (K.d p
        q)).symm }
    naturality {K L} f := by
      ext n : 1
      exact (AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction j).unit.naturality
        (f.f n) }
  counit := {
    app K := {
      f n := (AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction j).counit.app (K.X
        n)
      comm' p q _ := ((AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction
        j).counit.naturality (K.d p
        q)).symm }
    naturality {K L} f := by
      ext n : 1
      exact (AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction j).counit.naturality
        (f.f n) }
  left_triangle_components K := by
    ext n : 1
    exact (AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction
      j).left_triangle_components (K.X n)
  right_triangle_components K := by
    ext n : 1
    exact (AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction
      j).right_triangle_components (K.X n)

instance extensionByZero_unit_app_isIso (K : Complex U) :
    IsIso ((extensionByZeroAdjunction j).unit.app K) := by
  let : ∀ n, IsIso (((extensionByZeroAdjunction j).unit.app K).f n) := fun n =>
    inferInstanceAs (IsIso ((AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction
      j).unit.app (K.X n)))
  exact _root_.HomologicalComplex.Hom.isIso_of_components _

instance extensionByZero_unit_isIso : IsIso (extensionByZeroAdjunction j).unit := by
  exact NatIso.isIso_of_isIso_app _

/-- Restriction of the original extended complex is isomorphic to the original complex. -/
def extensionByZeroRestrictIso : extensionByZero j ⋙ restrict j ≅ 𝟭 _ :=
  (asIso (extensionByZeroAdjunction j).unit).symm

/-- A local chain map gives its actual global adjoint chain map. -/
def extensionByZeroMap {K : Complex U} {L : Complex X} (f : K ⟶ (restrict j).obj L) :
    (extensionByZero j).obj K ⟶ L :=
  ((extensionByZeroAdjunction j).homEquiv K L).symm f

/-- The adjoint uses precisely the original mapped arrow followed by the original counit. -/
theorem extensionByZeroMap_eq {K : Complex U} {L : Complex X}
    (f : K ⟶ (restrict j).obj L) : extensionByZeroMap j f =
      (extensionByZero j).map f ≫ (extensionByZeroAdjunction j).counit.app L := rfl

/-- Adjoint maps retain original source precomposition exactly. -/
@[reassoc]
theorem extensionByZeroMap_precomp {K K' : Complex U} {L : Complex X}
    (a : K' ⟶ K) (f : K ⟶ (restrict j).obj L) :
    (extensionByZero j).map a ≫ extensionByZeroMap j f = extensionByZeroMap j (a ≫ f) :=
  ((extensionByZeroAdjunction j).homEquiv_naturality_left_symm a f).symm

/-- Adjoint maps retain original target postcomposition exactly. -/
@[reassoc]
theorem extensionByZeroMap_postcomp {K : Complex U} {L L' : Complex X}
    (f : K ⟶ (restrict j).obj L) (b : L ⟶ L') :
    extensionByZeroMap j f ≫ b = extensionByZeroMap j (f ≫ (restrict j).map b) :=
  ((extensionByZeroAdjunction j).homEquiv_naturality_right_symm f b).symm

/-- The original local map is recovered by the actual unit and restricted adjoint. -/
@[reassoc (attr := simp)]
theorem extensionByZeroMap_restrict {K : Complex U} {L : Complex X}
    (f : K ⟶ (restrict j).obj L) :
    (extensionByZeroAdjunction j).unit.app K ≫ (restrict j).map (extensionByZeroMap j f) = f :=
  ((extensionByZeroAdjunction j).homEquiv K L).apply_symm_apply f

/-- Restricting the actual counit gives an isomorphism of original complexes. -/
instance restrict_extensionByZero_counit_isIso (L : Complex X) :
    IsIso ((restrict j).map ((extensionByZeroAdjunction j).counit.app L)) := by
  let : ∀ n, IsIso (((restrict j).map ((extensionByZeroAdjunction j).counit.app L)).f n) := fun n =>
    inferInstanceAs (IsIso ((Scheme.Modules.restrictFunctor j).map
      ((AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction j).counit.app (L.X n))))
  exact _root_.HomologicalComplex.Hom.isIso_of_components _

/-- Actual extension by zero preserves all quasi-isomorphisms of sheaf complexes. -/
instance extensionByZero_quasiIso {K L : Complex U} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((extensionByZero j).map f) := by
  let : (AlgebraicGeometry.Scheme.Modules.extensionByZero j).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  unfold extensionByZero
  infer_instance

/-- Specified local homotopies give genuine global homotopies of the actual adjoint maps. -/
def extensionByZeroMapHomotopy {K : Complex U} {L : Complex X}
    {f g : K ⟶ (restrict j).obj L} (H : Homotopy f g) :
    Homotopy (extensionByZeroMap j f) (extensionByZeroMap j g) :=
  ((AlgebraicGeometry.Scheme.Modules.extensionByZero j).mapHomotopy H).compRight
    ((extensionByZeroAdjunction j).counit.app L)

end Quillen.PerfectComplexes
