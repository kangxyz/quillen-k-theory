/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarConeFunctor
/-! Named clients retain the actual scalar, support and original cone maps. -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.Waldhausen.Fibration
universe u
namespace QuillenTest.ScalarConeFunctor
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The original endomorphism's cone has exactly its old object after lifting. -/
theorem original_cone_object (K : Perfect X) :
    (perfectOpenScalarConeFunctor j r q hq).obj K = perfectOpenScalarCone j r q hq K :=
  perfectOpenScalarConeFunctor_obj j r q hq K

/-- Both maps in the actual cone square are the original coefficient chain map. -/
theorem original_cone_map {K L : Perfect X} (g : K ⟶ L) :
    (((perfectOpenScalarConeFunctor j r q hq).map g).hom).hom =
      CochainComplex.mappingCone.map ((complexGlobalScalar X r).app K.obj)
        ((complexGlobalScalar X r).app L.obj) g.hom g.hom
        ((complexGlobalScalar X r).naturality g.hom).symm := rfl

/-- Forgetting acyclicity preserves the entire original perfect cone functor. -/
theorem original_forgetful_functor :
    perfectOpenScalarConeFunctor j r q hq ⋙ acyclicInclusion (perfectOpenNested j) =
      perfectScalarConeFunctor X r := perfectOpenScalarConeFunctor_comp_inclusion j r q hq

end QuillenTest.ScalarConeFunctor
