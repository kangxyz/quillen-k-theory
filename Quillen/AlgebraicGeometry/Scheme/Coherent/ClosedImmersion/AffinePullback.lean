/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.AffinePushforward
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual affine sheaf pullback and extension of scalars

The comparison is obtained from the actual pushforward/global-sections
square by uniqueness of left adjoints. In particular it concerns the genuine
scheme-module pullback, including its adjunction unit.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Quillen.CoherentScheme.ClosedImmersion
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Actual affine sheaf pullback of an associated sheaf is associated to
ordinary extension of scalars. -/
def tildePullbackIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  (((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
        (pushforwardGlobalSectionsIso φ)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S)))

/-- The pullback of every actual affine quasicoherent sheaf is quasicoherent. -/
theorem isQuasicoherent_pullback (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent := by
  let e := (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ).symm ≪≫
    (tildePullbackIso φ).app (moduleSpecΓFunctor.obj M)
  apply (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso e.symm
  exact inferInstanceAs (tilde ((ModuleCat.extendScalars φ.hom).obj
    (moduleSpecΓFunctor.obj M))).IsQuasicoherent

/-- Finiteness of an associated affine sheaf survives arbitrary affine pullback. -/
theorem affineFiniteSheaf_pullback {M : (Spec R).Modules} (hM : affineFiniteSheaf R M) :
    affineFiniteSheaf S ((Scheme.Modules.pullback (Spec.map φ)).obj M) := by
  have : M.IsQuasicoherent := hM.1
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := hM.2
  let N := (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M)
  have : Module.Finite S N := by
    let := φ.hom.toAlgebra
    change Module.Finite S (S ⊗[R] (moduleSpecΓFunctor.obj M))
    infer_instance
  let e := (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ).symm ≪≫
    (tildePullbackIso φ).app (moduleSpecΓFunctor.obj M)
  apply (affineFiniteSheaf S).prop_of_iso e.symm
  refine ⟨inferInstanceAs (tilde N).IsQuasicoherent, ?_⟩
  let eΓ : N ≃ₗ[S] (moduleSpecΓFunctor.obj (tilde N)) :=
    ((tilde.toTildeΓNatIso (R := S)).app N).toLinearEquiv
  exact Module.Finite.equiv eΓ

end Quillen.CoherentScheme.ClosedImmersion
