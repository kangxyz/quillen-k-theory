/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnit
public import Quillen.Aglib.AlgebraicGeometry.Modules.Scalar.Pullback

/-! Original bounded-flat pullback preserves the actual global-unit automorphism. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes

/-- Original geometric pullback carries the original global-unit action to the pulled-back unit. -/
lemma boundedFlatPerfectPullback_map_globalUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(Y, ⊤))ˣ) (K : BoundedFlatPerfect Y) :
    (boundedFlatPerfectPullback f).map ((boundedFlatPerfectGlobalUnitIso Y r).hom.app K) =
      (boundedFlatPerfectGlobalUnitIso X
        (Units.map f.appTop.hom.toMonoidHom r)).hom.app ((boundedFlatPerfectPullback f).obj K) := by
  apply (boundedFlatPerfect X).ι.map_injective
  change (AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map
    ((boundedFlatPerfect Y).ι.map ((boundedFlatPerfectGlobalUnitIso Y r).hom.app K)) = _
  rw [boundedFlatPerfectGlobalUnitIso_hom_original,
    boundedFlatPerfectGlobalUnitIso_hom_original]
  apply HomologicalComplex.hom_ext
  intro n
  change (Scheme.Modules.pullback f).map (((complexGlobalUnitIso Y r).hom.app K.obj).f n) = _
  rw [complexGlobalUnitIso_original_terms, complexGlobalUnitIso_original_terms]
  exact AlgebraicGeometry.Scheme.Modules.pullback_map_globalScalar f (↑r) (K.obj.X n)

/-- The actual geometric composition comparison intertwines the original pulled-back unit. -/
lemma boundedFlatPerfectPullbackUnitIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(Y, ⊤))ˣ) :
    (boundedFlatPerfectPullbackCompIso f g).hom ≫
      Functor.whiskerRight (boundedFlatPerfectPullbackUnitIso g r).hom
        (boundedFlatPerfectPullback f) =
    (boundedFlatPerfectPullbackUnitIso (f ≫ g)
      (Units.map f.appTop.hom.toMonoidHom r)).hom ≫
        (boundedFlatPerfectPullbackCompIso f g).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, boundedFlatPerfectPullbackUnitIso, Iso.trans_hom,
    Iso.symm_hom, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  rw [boundedFlatPerfectPullback_map_globalUnit]
  exact (boundedFlatPerfectGlobalUnitIso X
    (Units.map f.appTop.hom.toMonoidHom r)).hom.naturality _

end Quillen.PerfectComplexes
