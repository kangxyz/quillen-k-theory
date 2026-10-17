/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.Algebra.Homology.QuasiIso

/-!
# Composites of actual quasi-isomorphism components

The original three natural-transformation components retain their exact chain composite.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
lemma quasiIso_triple_app {D : Type*} [Category D] (X : Scheme.{u})
    {F G H I : D ⥤ CochainComplex X.Modules ℤ} (f : F ⟶ G) (g : G ⟶ H) (h : H ⟶ I) (K : D)
    (hf : QuasiIso (f.app K)) (hg : QuasiIso (g.app K)) (hh : QuasiIso (h.app K)) :
    QuasiIso ((f ≫ g ≫ h).app K) := by
  let := hf
  let := hg
  let := hh
  change QuasiIso (f.app K ≫ g.app K ≫ h.app K)
  infer_instance


end Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
end
end
