/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlatPullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.Scalar.GlobalUnit

/-!
# Global units on original sheaf complexes

Literal degreewise multiplication by a global unit restricts to the original perfect category and
acts on actual flat pullback.-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes

/-- Actual degreewise multiplication by a global unit on the original ambient complexes. -/
def complexGlobalUnitIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    𝟭 (CochainComplex X.Modules ℤ) ≅ 𝟭 (CochainComplex X.Modules ℤ) :=
  (Functor.mapHomologicalComplexIdIso _ _).symm ≪≫
    NatIso.mapHomologicalComplex (AlgebraicGeometry.Scheme.Modules.globalUnitIso X r) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ _

/-- The same actual scalar automorphism on the original locally-perfect category. -/
def perfectGlobalUnitIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    𝟭 (Perfect X) ≅ 𝟭 (Perfect X) :=
  Functor.fullyFaithfulCancelRight (locallyPerfect X).ι
    (Functor.isoWhiskerLeft (locallyPerfect X).ι (complexGlobalUnitIso X r))

/-- The global unit acts on the actual geometric flat pullback functor. -/
def perfectFlatPullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (r : (Γ(X, ⊤))ˣ) : perfectFlatPullback f ≅ perfectFlatPullback f :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (perfectFlatPullback f) (perfectGlobalUnitIso X r) ≪≫
      Functor.rightUnitor _

lemma complexGlobalUnitIso_original_terms (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((complexGlobalUnitIso X r).hom.app K).f n =
      (AlgebraicGeometry.Scheme.Modules.globalUnitIso X r).hom.app (K.X n) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rfl

end Quillen.PerfectComplexes

end

end
