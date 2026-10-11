/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffinePullback

/-!
# Original affine module-sheaf scalar-change comparisons

These consumers retain the actual pushforward, pullback, global sections, and
arbitrary coordinate-ring maps without finiteness or closedness hypotheses.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Quillen.Tests.AffineSheafScalarChange

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The original global-sections comparison is natural for an arbitrary sheaf arrow. -/
theorem original_global_sections_naturality {M N : (Spec S).Modules} (f : M ⟶ N) :
    (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor).map f ≫
        (SchemeSheaf.pushforwardGlobalSectionsIso φ).hom.app N =
      (SchemeSheaf.pushforwardGlobalSectionsIso φ).hom.app M ≫
        (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).map f :=
  (SchemeSheaf.pushforwardGlobalSectionsIso φ).hom.naturality f

/-- The associated-sheaf pushforward comparison retains the actual functor maps. -/
theorem original_pushforward_naturality {M N : ModuleCat S} (f : M ⟶ N) :
    (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)).map f ≫
        (SchemeSheaf.tildePushforwardIso φ).hom.app N =
      (SchemeSheaf.tildePushforwardIso φ).hom.app M ≫
        (ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R).map f :=
  (SchemeSheaf.tildePushforwardIso φ).hom.naturality f

/-- The actual pullback comparison retains extension of scalars on module arrows. -/
theorem original_pullback_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    (tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ)).map f ≫
        (SchemeSheaf.tildePullbackIso φ).hom.app N =
      (SchemeSheaf.tildePullbackIso φ).hom.app M ≫
        (ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).map f :=
  (SchemeSheaf.tildePullbackIso φ).hom.naturality f

/-- Arbitrary affine pushforward preserves actual quasicoherence. -/
theorem original_pushforward_quasicoherent (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj M).IsQuasicoherent :=
  SchemeSheaf.isQuasicoherent_pushforward φ M

/-- Arbitrary affine pullback preserves actual quasicoherence. -/
theorem original_pullback_quasicoherent (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent :=
  SchemeSheaf.isQuasicoherent_pullback φ M

end Quillen.Tests.AffineSheafScalarChange
