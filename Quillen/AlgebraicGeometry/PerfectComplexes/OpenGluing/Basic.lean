/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ExtensionByZeroBaseChange
public import Quillen.Algebra.Homology.HomotopyPushoutMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalDescent

/-! # Actual two-open sheaf-complex homotopy gluing -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenHomotopyGluing
open Quillen.CochainComplex
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : a ≫ j = b ≫ k)
  {K : Complex W} {A : Complex U} {B : Complex V}
  (α : K ⟶ (restrict a).obj A) (β : K ⟶ (restrict b).obj B)

/-- The original left overlap map between actual extended complexes. -/
def left : (extensionByZero j).obj ((extensionByZero a).obj K) ⟶
    (extensionByZero j).obj A :=
  (extensionByZero j).map (extensionByZeroMap a α)

/-- The original right overlap map, adjoint to the genuine base-change mate. -/
def right : (extensionByZero j).obj ((extensionByZero a).obj K) ⟶
    (extensionByZero k).obj B :=
  extensionByZeroMap j ((extensionByZero a).map β ≫
    (extensionByZeroBaseChange b a k j h.symm).app B)

/-- Actual global cone complex; the individual extended terms need not be perfect. -/
def glued : Complex X := homotopyPushout (left a j α) (right a b j k h β)

/-- Actual local first comparison into the restriction of the original global cone. -/
def first : A ⟶ (restrict j).obj (glued a b j k h α β) :=
  (extensionByZeroAdjunction j).unit.app A ≫
    (restrict j).map (homotopyPushoutInl (left a j α) (right a b j k h β))

/-- Actual local second comparison into the restriction of the original global cone. -/
def second : B ⟶ (restrict k).obj (glued a b j k h α β) :=
  (extensionByZeroAdjunction k).unit.app B ≫
    (restrict k).map (homotopyPushoutInr (left a j α) (right a b j k h β))

/-- On the first open, the original right overlap map is weak by the actual unit square. -/
theorem right_restrict_quasiIso
    (hc : ∀ x : U, j x ∈ Set.range k → x ∈ Set.range a) [QuasiIso β] :
    QuasiIso ((restrict j).map (right a b j k h β)) := by
  have : IsIso ((extensionByZeroBaseChange b a k j h.symm).app B) :=
    inferInstanceAs (IsIso ((extensionByZeroBaseChangeIso b a k j h.symm hc).hom.app B))
  have he := extensionByZeroMap_restrict j ((extensionByZero a).map β ≫
    (extensionByZeroBaseChange b a k j h.symm).app B)
  have : QuasiIso ((extensionByZeroAdjunction j).unit.app ((extensionByZero a).obj K) ≫
      (restrict j).map (right a b j k h β)) := by
    change QuasiIso (_ ≫ (restrict j).map (extensionByZeroMap j _))
    rw [he]
    infer_instance
  exact (quasiIso_iff_comp_left _ _).mp this

include h in
/-- On the second open, original base-change naturality identifies the left overlap map. -/
theorem left_restrict_quasiIso
    (hc : ∀ x : V, k x ∈ Set.range j → x ∈ Set.range b) [QuasiIso α] :
    QuasiIso ((restrict k).map (left a j α)) := by
  let e := extensionByZeroBaseChangeIso a b j k h hc
  let s := (extensionByZero b).map ((extensionByZeroAdjunction a).unit.app K) ≫
    e.hom.app ((extensionByZero a).obj K)
  have : IsIso s := by dsimp [s]; infer_instance
  have he : s ≫ (restrict k).map (left a j α) =
      (extensionByZero b).map α ≫ e.hom.app A := by
    dsimp only [s, left]
    rw [Category.assoc]
    change (extensionByZero b).map ((extensionByZeroAdjunction a).unit.app K) ≫
      (e.hom.app _ ≫ (extensionByZero j ⋙ restrict k).map (extensionByZeroMap a α)) = _
    rw [← e.hom.naturality (extensionByZeroMap a α)]
    change (extensionByZero b).map ((extensionByZeroAdjunction a).unit.app K) ≫
      (extensionByZero b).map ((restrict a).map (extensionByZeroMap a α)) ≫ e.hom.app A = _
    rw [← Category.assoc, ← (extensionByZero b).map_comp, extensionByZeroMap_restrict]
  have : QuasiIso (s ≫ (restrict k).map (left a j α)) := by
    rw [he]
    infer_instance
  exact (quasiIso_iff_comp_left _ _).mp this

/-- The original first restriction recovers the given local complex up to an actual
  quasi-isomorphism. -/
theorem first_quasiIso
    (hc : ∀ x : U, j x ∈ Set.range k → x ∈ Set.range a) [QuasiIso β] :
    QuasiIso (first a b j k h α β) := by
  let : QuasiIso (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map
      (right a b j k h β)) := right_restrict_quasiIso a b j k h β hc
  let : QuasiIso ((restrict j).map (homotopyPushoutInl (left a j α) (right a b j k h β))) :=
    quasiIso_map_homotopyPushoutInl (Scheme.Modules.restrictFunctor j)
      (left a j α) (right a b j k h β)
  exact inferInstanceAs (QuasiIso ((extensionByZeroAdjunction j).unit.app A ≫
    (restrict j).map (homotopyPushoutInl (left a j α) (right a b j k h β))))

/-- The original second restriction recovers the other given local complex. -/
theorem second_quasiIso
    (hc : ∀ x : V, k x ∈ Set.range j → x ∈ Set.range b) [QuasiIso α] :
    QuasiIso (second a b j k h α β) := by
  let : QuasiIso (((Scheme.Modules.restrictFunctor k).mapHomologicalComplex (.up ℤ)).map
      (left a j α)) := left_restrict_quasiIso a b j k h α hc
  let : QuasiIso ((restrict k).map (homotopyPushoutInr (left a j α) (right a b j k h β))) :=
    quasiIso_map_homotopyPushoutInr (Scheme.Modules.restrictFunctor k)
      (left a j α) (right a b j k h β)
  exact inferInstanceAs (QuasiIso ((extensionByZeroAdjunction k).unit.app B ≫
    (restrict k).map (homotopyPushoutInr (left a j α) (right a b j k h β))))

end Quillen.PerfectComplexes.OpenHomotopyGluing
