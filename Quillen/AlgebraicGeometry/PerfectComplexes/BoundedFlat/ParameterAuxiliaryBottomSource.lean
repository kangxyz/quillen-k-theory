/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportNull
public import Quillen.Aglib.CategoryTheory.Functor.FullSubcategoryExt

/-!
# The original bottom-auxiliary source map is the literal open-set cast

For the inclusion of an actual open, the union with the bottom auxiliary open is
that same open. The original `toBasic` map equals transport through this precise
open-set equality. Equality is detected after the actual full-subcategory
inclusion on each parameter Model, before any K-theory functor is applied.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport

private theorem supported_eqToHom_forget {Q : Scheme.{u}} {U V : Q.Opens} (h : U = V) :
    eqToHom (congrArg (fun W : Q.Opens => ParameterModels.supported W.ι) h) ≫
      ParameterModels.forget V.ι = ParameterModels.forget U.ι := by
  subst V
  simp

/-- The union with the bottom auxiliary open is the original open itself. -/
theorem unionOpen_ι_bot {Q : Scheme.{u}} (U : Q.Opens) : unionOpen U.ι ⊥ = U := by
  simp [unionOpen]

/-- The original source comparison is exactly transport by the displayed open-set equality. -/
theorem toBasic_ι_bot_eqToHom {Q : Scheme.{u}} (U : Q.Opens)
    (h : unionOpen U.ι ⊥ = U := unionOpen_ι_bot U) :
    toBasic U.ι ⊥ =
      eqToHom (congrArg (fun V : Q.Opens => ParameterModels.supported V.ι) h) := by
  apply NatTrans.ext
  funext X
  apply Model.Hom.ext
  apply Quillen.Waldhausen.GilletWaldhausen.fullSubcategory_postcomp_injective
    (ParameterLaurentTrack.parameterSupported U.ι X)
  exact congrArg Model.Hom.functor (NatTrans.congr_app
    ((toBasic_forget U.ι ⊥).trans (supported_eqToHom_forget h).symm) X)

/-- The actual bottom-auxiliary source map is an isomorphism of the original Model diagrams. -/
instance toBasic_ι_bot_isIso {Q : Scheme.{u}} (U : Q.Opens) : IsIso (toBasic U.ι ⊥) := by
  rw [toBasic_ι_bot_eqToHom U]
  infer_instance

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
