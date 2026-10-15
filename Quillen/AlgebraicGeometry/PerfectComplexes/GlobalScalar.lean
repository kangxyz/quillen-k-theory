/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Local
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GlobalScalarRestriction

/-! The actual global scalar acts termwise on the original ambient and perfect complexes. -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Original multiplication by a global scalar in each degree of the unchanged complex. -/
def complexGlobalScalar (X : Scheme.{u}) (r : Γ(X, ⊤)) : 𝟭 (Complex X) ⟶ 𝟭 (Complex X) where
  app K := {
    f n := (AlgebraicGeometry.Scheme.Modules.globalScalar X r).app (K.X n)
    comm' i j _ := ((AlgebraicGeometry.Scheme.Modules.globalScalar X r).naturality (K.d i j)).symm }
  naturality K L f := by
    ext n : 1
    exact (AlgebraicGeometry.Scheme.Modules.globalScalar X r).naturality (f.f n)

/-- The same original scalar endomorphism in the full locally-perfect category. -/
def perfectGlobalScalar (X : Scheme.{u}) (r : Γ(X, ⊤)) : 𝟭 (Perfect X) ⟶ 𝟭 (Perfect X) where
  app K := (locallyPerfect X).homMk ((complexGlobalScalar X r).app K.obj)
  naturality K L f := by
    apply (locallyPerfect X).ι.map_injective
    exact (complexGlobalScalar X r).naturality f.hom

/-- Faithful inclusion retains the original termwise scalar map. -/
theorem perfectGlobalScalar_original (X : Scheme.{u}) (r : Γ(X, ⊤)) (K : Perfect X) :
    (locallyPerfect X).ι.map ((perfectGlobalScalar X r).app K) =
      (complexGlobalScalar X r).app K.obj := rfl

/-- The original open restriction preserves the scalar in every original cochain degree. -/
theorem restrict_map_complexGlobalScalar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (r : Γ(X, ⊤)) (K : Complex X) :
    (restrict j).map ((complexGlobalScalar X r).app K) =
      (complexGlobalScalar U (j.appTop r)).app ((restrict j).obj K) := by
  ext n : 1
  exact AlgebraicGeometry.Scheme.Modules.restrict_map_globalScalar j r (K.X n)

end Quillen.PerfectComplexes
