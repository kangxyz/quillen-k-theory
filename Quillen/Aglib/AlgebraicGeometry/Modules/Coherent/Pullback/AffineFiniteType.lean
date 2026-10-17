/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Finiteness under actual affine sheaf pullback

Finite associated sheaves remain finite under arbitrary affine pullback.
The proof uses the generic extension-of-scalars comparison from the lower
module-sheaf owner.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

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
    (AlgebraicGeometry.Scheme.Modules.tildePullbackIso φ).app (moduleSpecΓFunctor.obj M)
  apply (affineFiniteSheaf S).prop_of_iso e.symm
  refine ⟨inferInstanceAs (tilde N).IsQuasicoherent, ?_⟩
  let eΓ : N ≃ₗ[S] (moduleSpecΓFunctor.obj (tilde N)) :=
    ((tilde.toTildeΓNatIso (R := S)).app N).toLinearEquiv
  exact Module.Finite.equiv eΓ

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
