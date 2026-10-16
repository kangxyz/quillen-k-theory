/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalScalar
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnit

/-!
# Scalars which become units on an open

The original restricted scalar is exactly the genuine unit automorphism. Its quasi-isomorphism statement unfolds only the original relative weak-equivalence wrapper.
-/
@[expose] public section



open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- A scalar which is a unit gives precisely the existing original unit automorphism. -/
theorem complexGlobalScalar_unit (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : CochainComplex X.Modules ℤ) :
    (complexGlobalScalar X (↑r)).app K = (complexGlobalUnitIso X r).hom.app K := by
  ext n : 1
  exact (complexGlobalUnitIso_original_terms X r K n).symm

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

include hq in
/-- Restriction of the original scalar is the exact preexisting unit automorphism. -/
theorem restrict_map_complexGlobalScalar_unit (K : CochainComplex X.Modules ℤ) :
    (restrict j).map ((complexGlobalScalar X r).app K) =
      (complexGlobalUnitIso U q).hom.app ((restrict j).obj K) := by
  rw [restrict_map_complexGlobalScalar, hq, complexGlobalScalar_unit]

include hq in
/-- The original endomorphism is genuinely weak after restriction to the specified open. -/
theorem perfectGlobalScalar_openWeak (K : Perfect X) :
    QuasiIso ((restrict j).map (((perfectGlobalScalar X r).app K).hom)) := by
  change QuasiIso ((restrict j).map ((complexGlobalScalar X r).app K.obj))
  rw [restrict_map_complexGlobalScalar, hq, complexGlobalScalar_unit]
  infer_instance

end Quillen.PerfectComplexes

end

end
