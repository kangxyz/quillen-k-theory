/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Mathlib.Algebra.Homology.Single

/-!
# The actual single-complex restriction square

The supplied sheaf square and original single/restriction comparisons give the same literal
degree-zero chain square.-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine
theorem single_restriction_square {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N)
    {M' N' : U.Modules} (a : M.restrict j ≅ M') (b : N.restrict j ≅ N')
    (g : M' ⟶ N') (h : (Scheme.Modules.restrictFunctor j).map f ≫ b.hom = a.hom ≫ g) :
    (restrict j).map ((CochainComplex.singleFunctor X.Modules 0).map f) ≫
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.restrictFunctor j) (.up ℤ) 0).app N ≪≫
            (CochainComplex.singleFunctor U.Modules 0).mapIso b).hom =
      ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.restrictFunctor j) (.up ℤ) 0).app M ≪≫
            (CochainComplex.singleFunctor U.Modules 0).mapIso a).hom ≫
        (CochainComplex.singleFunctor U.Modules 0).map g := by
  let e := HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.restrictFunctor j) (.up ℤ) 0
  have hn := e.hom.naturality f
  change (restrict j).map ((CochainComplex.singleFunctor X.Modules 0).map f) ≫
      (e.app N).hom = (e.app M).hom ≫
        (CochainComplex.singleFunctor U.Modules 0).map
          ((Scheme.Modules.restrictFunctor j).map f) at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, h, Functor.map_comp]
  simp only [e, Category.assoc]


end Quillen.PerfectComplexes.ProjectiveLine
end
end
