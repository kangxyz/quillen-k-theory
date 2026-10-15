/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatPullback

/-!
# Consumers of ambient flat sheaf pullback

These consumers use arbitrary module sheaves, with no quasicoherence or
finiteness assumptions. The canonical geometric pullback functor is unchanged.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.FlatSheafPullback

/-- Stalk exactness does not require a quasicoherent sheaf. -/
theorem stalkShortExact {X : Scheme.{u}} (x : X) {S : ShortComplex X.Modules}
    (h : S.ShortExact) : (S.map (AlgebraicGeometry.Scheme.Modules.moduleStalk X x)).ShortExact :=
  h.map_of_exact _

/-- The scalar-extension description is the actual geometric pullback stalk. -/
def actualPullbackStalk {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (M : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.moduleStalk X x).obj ((Scheme.Modules.pullback f).obj M) ≅
      (ModuleCat.extendScalars (f.stalkMap x).hom).obj
        ((AlgebraicGeometry.Scheme.Modules.moduleStalk Y (f x)).obj M) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackModuleStalkIso f x).app M

/-- Flatness is sufficient for preservation of arbitrary sheaf monomorphisms. -/
theorem arbitraryMono {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {M N : Y.Modules} (s : M ⟶ N) [Mono s] : Mono ((Scheme.Modules.pullback f).map s) :=
  inferInstance

/-- All sheaf short exact sequences pull back along a flat morphism. -/
theorem arbitraryShortExact {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {S : ShortComplex Y.Modules} (h : S.ShortExact) :
    (S.map (Scheme.Modules.pullback f)).ShortExact := h.map_of_exact _

/-- Flat pullback preserves the actual kernel, without a QC hypothesis. -/
def actualKernel {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {M N : Y.Modules} (s : M ⟶ N) :
    (Scheme.Modules.pullback f).obj (kernel s) ≅ kernel ((Scheme.Modules.pullback f).map s) :=
  PreservesKernel.iso (Scheme.Modules.pullback f) s

end QuillenTest.FlatSheafPullback
