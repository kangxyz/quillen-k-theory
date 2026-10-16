/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Finite locally free sheaves over fields

Finite free modules give finite locally free associated sheaves. On a field spectrum, the actual coherent inclusion has an exact inverse preserving the underlying sheaf and morphisms.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.ExactCategory

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- A genuinely finite free module gives a finite locally free sheaf by
transporting its basis through the actual tilde/free-sheaf comparison. -/

theorem finiteLocallyFree_tilde_of_finite_free (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    IsFiniteLocallyFree (Spec R) (tilde M) := by
  let b := Module.Free.chooseBasis R M
  let e : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (Module.Free.ChooseBasisIndex R M) ≅ tilde M :=
    (tildeFinsupp (Module.Free.ChooseBasisIndex R M)).symm ≪≫
      (tilde.functor R).mapIso b.repr.symm.toModuleIso
  exact finiteLocallyFree_of_iso e

variable (k : Type u) [Field k]

/-- On the spectrum of a field, every actual coherent sheaf is finite
locally free. The proof chooses a finite basis of global sections. -/

theorem finiteLocallyFree_of_coherent_field
    (M : (Spec (CommRingCat.of k)).Modules)
    (hM : AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (Spec
      (CommRingCat.of k)) M) :
    IsFiniteLocallyFree (Spec (CommRingCat.of k)) M := by
  have h := (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_spec_iff
    (CommRingCat.of k) M).mp hM
  have : M.IsQuasicoherent := h.1
  have : Module.Finite k (moduleSpecΓFunctor.obj M) := h.2
  have : IsFiniteLocallyFree (Spec (CommRingCat.of k))
      (tilde (moduleSpecΓFunctor.obj M)) :=
    finiteLocallyFree_tilde_of_finite_free (CommRingCat.of k) _
  let e : tilde (moduleSpecΓFunctor.obj M) ≅ M := asIso M.fromTildeΓ
  exact finiteLocallyFree_of_iso e

/-- The inverse to the actual vector-bundle inclusion on a field spectrum.
It retains the sheaf and every sheaf morphism. -/

def coherentToVectorBundleField :
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves (Spec (CommRingCat.of k)) ⥤
      FiniteLocallyFree (Spec (CommRingCat.of k)) :=
  ObjectProperty.ιOfLE (fun M hM => finiteLocallyFree_of_coherent_field k M hM)

instance coherentToVectorBundleField_additive : (coherentToVectorBundleField k).Additive where
  map_add := by intros; rfl

/-- The inverse preserves actual short exact sheaf sequences. -/

def coherentToVectorBundleFieldExact :
    ExactFunctor (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure (Spec
      (CommRingCat.of k)))
      (vectorBundleExactStructure (Spec (CommRingCat.of k))) where
  toFunctor := coherentToVectorBundleField k
  map_conflation S hS :=
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherent_shortExact_iff (Spec (CommRingCat.of k))
      S).mp hS

/-- Inclusion followed by the field inverse keeps the same vector bundle. -/

def vectorBundleFieldUnitIso :
    ((vectorBundleToCoherentExact (Spec (CommRingCat.of k))).comp
      (coherentToVectorBundleFieldExact k)).toFunctor ≅
      (CategoryTheory.ExactCategory.ExactFunctor.id (vectorBundleExactStructure (Spec
        (CommRingCat.of k)))).toFunctor :=
  Iso.refl _

/-- The field inverse followed by inclusion keeps the same coherent sheaf. -/

def vectorBundleFieldCounitIso :
    ((coherentToVectorBundleFieldExact k).comp
      (vectorBundleToCoherentExact (Spec (CommRingCat.of k)))).toFunctor ≅
      (CategoryTheory.ExactCategory.ExactFunctor.id
        (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
        (Spec (CommRingCat.of k)))).toFunctor :=
  Iso.refl _

end AlgebraicGeometry.Scheme.Modules
