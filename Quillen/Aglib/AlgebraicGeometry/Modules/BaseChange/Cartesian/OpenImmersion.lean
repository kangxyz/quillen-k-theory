/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian

/-! # Comparison of original pullback and open-restriction base-change mates -/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

/-- The original ordinary pullback mate agrees with the original open-restriction mate. -/

theorem cartesianBaseChangeMap_restrict (M : U.Modules) :
    (restrictFunctorIsoPullback j).hom.app ((pushforward f).obj M) ≫
        (cartesianBaseChangeMap a b f j h).app M =
      (cartesianOpenBaseChange a b f j h).hom.app M ≫
        (pushforward b).map ((restrictFunctorIsoPullback a).hom.app M) := by
  apply ((restrictAdjunction j).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hj := Adjunction.unit_leftAdjointUniq_hom_app
    (restrictAdjunction j) (pullbackPushforwardAdjunction j) ((pushforward f).obj M)
  erw [reassoc_of% hj]
  erw [← cartesianBaseChangeMap_unit a b f j h M]
  erw [← reassoc_of% cartesianOpenBaseChange_unit a b f j h M]
  have hn := (cartesianPushforwardSquare a b f j h).hom.naturality
    ((restrictFunctorIsoPullback a).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [← hn]
  have ha := Adjunction.unit_leftAdjointUniq_hom_app
    (restrictAdjunction a) (pullbackPushforwardAdjunction a) M
  have he := congrArg (fun t => (pushforward f).map t ≫
    (cartesianPushforwardSquare a b f j h).hom.app ((Scheme.Modules.pullback a).obj M)) ha
  simpa only [Functor.map_comp, Category.assoc, Functor.comp_obj, Functor.id_obj,
    restrictFunctorIsoPullback] using he.symm

/-- The actual ordinary geometric mate is invertible under open base change. -/

theorem isIso_cartesianBaseChangeMap_of_open : IsIso (cartesianBaseChangeMap a b f j h) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hc : IsIso ((restrictFunctorIsoPullback j).hom.app ((pushforward f).obj M) ≫
      (cartesianBaseChangeMap a b f j h).app M) := by
    rw [cartesianBaseChangeMap_restrict a b f j h M]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hc

end AlgebraicGeometry.Scheme.Modules
