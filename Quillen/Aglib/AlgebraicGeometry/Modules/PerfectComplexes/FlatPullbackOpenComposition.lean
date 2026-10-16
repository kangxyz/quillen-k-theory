/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlatPullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnitRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnit

/-!
# Original open and flat pullback composition

The actual restriction/flat comparison and geometric composition isomorphism retain the original unit and its genuine pulled-back scalar.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen 
universe u
namespace Quillen.PerfectComplexes
variable {U X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (i : U ⟶ X) [IsOpenImmersion i]

/-- The original open/flat comparison followed by the inverse geometric composition iso. -/
def perfectFlatOpenCompositionIso :
    perfectFlatPullback f ⋙ perfectRestrict i ≅ perfectFlatPullback (i ≫ f) :=
  Functor.isoWhiskerLeft (perfectFlatPullback f) (perfectRestrictIsoFlatPullback i) ≪≫
    (perfectFlatPullbackCompIso i f).symm

variable (q : (Γ(X, ⊤))ˣ)

/-- The actual restricted unit commutes with the original geometric composition isomorphism. -/
theorem perfectFlatUnitOpenCompositionTransformation :
    Functor.whiskerRight (perfectFlatPullbackUnitIso f q).hom (perfectRestrict i) ≫
        (perfectFlatOpenCompositionIso f i).hom =
      (perfectFlatOpenCompositionIso f i).hom ≫
        (perfectFlatPullbackUnitIso (i ≫ f)
          (Units.map i.appTop.hom.toMonoidHom q)).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, perfectFlatPullbackUnitIso,
    Iso.trans_hom, Iso.symm_hom, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp]
  have hc := congrArg Iso.hom
    (perfectRestrict_globalUnitIso_app i q ((perfectFlatPullback f).obj K))
  change (perfectRestrict i).map ((perfectGlobalUnitIso X q).hom.app
    ((perfectFlatPullback f).obj K)) = _ at hc
  have hf : (perfectGlobalUnitIso X q).hom.app ((perfectFlatPullback f).obj K) ≫
      𝟙 ((perfectFlatPullback f).obj K) =
        (perfectGlobalUnitIso X q).hom.app ((perfectFlatPullback f).obj K) :=
    Category.comp_id _
  have hp : (perfectGlobalUnitIso U (Units.map i.appTop.hom.toMonoidHom q)).hom.app
      ((perfectFlatPullback (i ≫ f)).obj K) ≫ 𝟙 ((perfectFlatPullback (i ≫ f)).obj K) =
        (perfectGlobalUnitIso U (Units.map i.appTop.hom.toMonoidHom q)).hom.app
          ((perfectFlatPullback (i ≫ f)).obj K) := Category.comp_id _
  rw [hf, hp, hc]
  exact ((perfectGlobalUnitIso U (Units.map i.appTop.hom.toMonoidHom q)).hom.naturality
    ((perfectFlatOpenCompositionIso f i).hom.app K)).symm

end Quillen.PerfectComplexes

end

end
