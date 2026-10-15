/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GluingSubobjects

/-!
# Naturality of open-subobject obstructions

A commutative square of actual restricted inclusions induces the original cokernel map and its
direct image on the global obstruction.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.CoherentScheme


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules.Coherent

lemma subobjectObstruction_naturality {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} {A B : U.Modules} (i : A ⟶ M.restrict j) (k : B ⟶ N.restrict j)
    (p : A ⟶ B) (f : M ⟶ N)
    (w : i ≫ (Scheme.Modules.restrictFunctor j).map f = p ≫ k) :
    f ≫ subobjectObstruction j k = subobjectObstruction j i ≫
      (Scheme.Modules.pushforward j).map
        (cokernel.map i k p ((Scheme.Modules.restrictFunctor j).map f) w) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_restrict_map_eq_zero j _ ⟨_, ⟨Iso.refl _⟩⟩
  apply (cancel_mono ((Scheme.Modules.restrictAdjunction j).counit.app (cokernel k))).mp
  simp only [Functor.map_sub, Functor.map_comp, Preadditive.sub_comp,
    Category.assoc, zero_comp]
  rw [subobjectObstruction_counit]
  have hn := (Scheme.Modules.restrictAdjunction j).counit.naturality
    (cokernel.map i k p ((Scheme.Modules.restrictFunctor j).map f) w)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn, ← Category.assoc, subobjectObstruction_counit, cokernel.π_desc]
  exact sub_self _

end AlgebraicGeometry.Scheme.Modules.Coherent
