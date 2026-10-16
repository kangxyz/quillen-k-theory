/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.Affine
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction

/-!
# Kernel closure of genuine coherent vector bundles

An ambient short exact sequence of coherent sheaves restricts to an ambient
short exact sequence on each affine chart. Finite projective modules give
kernel closure there; locality of finite local freeness gives kernel closure
on the original scheme. No vector bundle is assumed globally projective in
the sheaf category.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- Kernels of admissible epimorphisms between coherent vector bundles are
actual finite locally free sheaves on any locally noetherian scheme. -/

instance coherentVectorBundle_kernelClosed (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).IsKernelClosed
      (coherentVectorBundle X) where
  prop_kernel {S} hS h₂ h₃ := by
    have : IsFiniteLocallyFree X S.X₂.obj := h₂
    have : IsFiniteLocallyFree X S.X₃.obj := h₃
    let U := X.affineOpenCover
    apply finiteLocallyFree_of_affineCharts S.X₁.obj U.X U.f
      (fun x => ⟨U.idx x, U.covers x⟩)
    intro i
    have : IsLocallyNoetherian (Spec (U.X i)) :=
      isLocallyNoetherian_of_isOpenImmersion (U.f i)
    have : IsNoetherianRing (U.X i) := isLocallyNoetherian_Spec.mp inferInstance
    let F := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesRestriction (U.f i)
    let T := S.map F
    have hT : T.ShortExact := hS.map_of_exact F
    have h₂' : coherentVectorBundle (Spec (U.X i)) T.X₂ :=
      finiteLocallyFree_restrict (U.f i) S.X₂.obj
    have h₃' : coherentVectorBundle (Spec (U.X i)) T.X₃ :=
      finiteLocallyFree_restrict (U.f i) S.X₃.obj
    exact CategoryTheory.ExactCategory.ExactStructure.IsKernelClosed.prop_kernel
      (E := AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure (Spec (U.X i))) hT h₂'
        h₃'

end AlgebraicGeometry.Scheme.Modules
