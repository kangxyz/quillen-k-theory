/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PullbackIsomorphisms
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnit

/-!
# Global units on bounded-flat perfect complexes

The actual degreewise global unit, its inverse, and the induced automorphism of geometric pullback
retain the original complex terms.-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes

/-- The actual termwise global unit restricted to bounded-flat perfect complexes. -/
def boundedFlatPerfectGlobalUnitIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    𝟭 (BoundedFlatPerfect X) ≅ 𝟭 (BoundedFlatPerfect X) :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfect X).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfect X).ι (complexGlobalUnitIso X r))

/-- The original unit acts on geometric bounded-flat pullback for every scheme map. -/
def boundedFlatPerfectPullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) : boundedFlatPerfectPullback f ≅ boundedFlatPerfectPullback f :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (boundedFlatPerfectPullback f) (boundedFlatPerfectGlobalUnitIso X r) ≪≫
      Functor.rightUnitor _

/-- Faithful inclusion retains the original ambient scalar automorphism. -/
lemma boundedFlatPerfectGlobalUnitIso_hom_original (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : BoundedFlatPerfect X) :
    (boundedFlatPerfect X).ι.map ((boundedFlatPerfectGlobalUnitIso X r).hom.app K) =
      (complexGlobalUnitIso X r).hom.app K.obj := by
  simp only [boundedFlatPerfectGlobalUnitIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    ObjectProperty.ι_obj]

/-- Faithful inclusion also retains the original inverse scalar automorphism. -/
lemma boundedFlatPerfectGlobalUnitIso_inv_original (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : BoundedFlatPerfect X) :
    (boundedFlatPerfect X).ι.map ((boundedFlatPerfectGlobalUnitIso X r).inv.app K) =
      (complexGlobalUnitIso X r).inv.app K.obj := by
  simp only [boundedFlatPerfectGlobalUnitIso, Functor.fullyFaithfulCancelRight_inv_app,
    Functor.map_preimage, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    ObjectProperty.ι_obj]

/-- On every actual term, the inverse is multiplication by the inverse global unit. -/
lemma boundedFlatPerfectGlobalUnitIso_inv_terms (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : BoundedFlatPerfect X) (n : ℤ) :
    ((boundedFlatPerfect X).ι.map
      ((boundedFlatPerfectGlobalUnitIso X r).inv.app K)).f n =
      (AlgebraicGeometry.Scheme.Modules.globalScalar X (↑r⁻¹)).app (K.obj.X n) := by
  rw [boundedFlatPerfectGlobalUnitIso_inv_original]
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
