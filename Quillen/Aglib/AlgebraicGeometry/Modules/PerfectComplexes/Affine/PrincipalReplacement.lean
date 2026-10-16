/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.StrictModuleModel

/-!
# Geometric chain-map replacement on an affine principal open

An actual chain map on the principal open from a strict-perfect affine
sheaf complex to a termwise quasicoherent complex admits a numerator after
precomposing with a source endomorphism that becomes an isomorphism on the
open. This uses the existing geometric restriction functor and actual affine
reconstruction. It does not assert derived replacement for every locally
perfect object or any extension/cofinality theorem.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.PerfectComplexes.Affine

/-- The algebraic construction supplies actual source replacement for
geometric chain maps from affine strict-perfect to termwise quasicoherent complexes. -/
theorem geometric_strict_chain_replacement (R : CommRingCat.{u}) (r : R)
    {K L : CochainComplex (Spec R).Modules ℤ} (hK : strictPerfect (Spec R) K)
      (hL : ∀ i, (L.X i).IsQuasicoherent)
    (φ : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj K ⟶
      (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj L) :
    ∃ (s : K ⟶ K) (g : K ⟶ L),
      IsIso ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map s) ∧
      (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map s ≫ φ =
        (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map g := by
  let J := restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)
  let A := associatedComplex R
  let K₀ := (sectionsComplex R).obj K
  let L₀ := (sectionsComplex R).obj L
  let eK := associatedSectionsIso R hK
  let eL := associatedSectionsIsoOfQuasicoherent R L hL
  obtain ⟨n, g₀, hd, hg⟩ := exists_principal_chain_fraction R r
    (moduleStrictPerfect_sections R hK) (J.map eK.hom ≫ φ ≫ J.map eL.inv)
  let d₀ := A.map (r ^ n • 𝟙 K₀)
  let s := eK.inv ≫ d₀ ≫ eK.hom
  let g := eK.inv ≫ A.map g₀ ≫ eL.hom
  have : IsIso (J.map d₀) := hd
  refine ⟨s, g, ?_, ?_⟩
  · change IsIso (J.map (eK.inv ≫ d₀ ≫ eK.hom))
    rw [J.map_comp, J.map_comp]
    infer_instance
  · have hp := congrArg (fun t => J.map eK.inv ≫ t ≫ J.map eL.hom) hg
    simpa [s, g, d₀, J, A, K₀, Category.assoc, Functor.map_comp] using hp


end Quillen.PerfectComplexes.Affine
