/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.PullbackRankOne
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Actual affine module-sheaf monomorphisms

The original global-section map detects monomorphisms between quasicoherent sheaves on
an affine scheme. A regular global scalar therefore gives a monomorphism of the original
structure module. An actual affine scheme identification transports this statement.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

open Quillen


noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules
/-- Injectivity on global sections detects a mono between actual quasicoherent affine sheaves. -/
theorem mono_of_mono_globalSections (R : CommRingCat.{u})
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Mono (moduleSpecΓFunctor.map f)] : Mono f := by
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  have h := Scheme.Modules.fromTildeΓNatTrans.naturality f
  change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at h
  have : Mono (M.fromTildeΓ ≫ f) := by
    rw [← h]
    infer_instance
  have he : f = inv M.fromTildeΓ ≫ (M.fromTildeΓ ≫ f) := by simp
  rw [he]
  infer_instance
/-- The original affine unit multiplier is monic when its actual global scalar is regular. -/
theorem mono_unitMul_of_regular (R : CommRingCat.{u}) (s : Γ(Spec R, ⊤))
    (hs : s ∈ nonZeroDivisors Γ(Spec R, ⊤)) : Mono (unitMul (Spec R) s) := by
  let e : SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit (Spec R).ringCatSheaf := coproductUniqueIso _
  have : (SheafOfModules.unit (Spec R).ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e (by infer_instance)
  have : Mono (moduleSpecΓFunctor.map (unitMul (Spec R) s)) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    intro x y h
    change Γ(Spec R, ⊤) at x y
    change x * s = y * s at h
    exact (isRegular_iff_mem_nonZeroDivisors.mpr hs).right h
  exact mono_of_mono_globalSections R (unitMul (Spec R) s)
/-- An actual affine scheme identification transports regular scalar monomorphisms. -/
theorem mono_unitMul_of_affineModel (R : CommRingCat.{u}) {X : Scheme.{u}}
    (e : Spec R ≅ X) (s : Γ(X, ⊤))
    (hs : e.hom.appTop.hom s ∈ nonZeroDivisors Γ(Spec R, ⊤)) : Mono (unitMul X s) := by
  let F := Scheme.Modules.pullback e.hom
  have : F.Faithful := Functor.Faithful.of_comp_iso
    (sectionPullbackIso e.inv e.hom e.inv_hom_id)
  have : Mono (unitMul (Spec R) (e.hom.appTop.hom s)) :=
    mono_unitMul_of_regular R _ hs
  have : Mono (F.map (unitMul X s) ≫ (pullbackUnitIso e.hom).hom) := by
    rw [unitMul_pullback]
    infer_instance
  have : Mono (F.map (unitMul X s)) := mono_of_mono _ (pullbackUnitIso e.hom).hom
  exact F.mono_of_mono_map inferInstance
end AlgebraicGeometry.Scheme.Modules
