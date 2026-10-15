/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.QuasicoherentExactSequence
public import Quillen.AlgebraicGeometry.PerfectComplexes.Homology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Quasicoherent homology of actual mapping cones

The original long exact homology sequence and genuine five-term sheaf closure
prove quasicoherence for arbitrary chain mapping cones. No quasicoherence of
terms, boundedness, noetherianity or global strict model is assumed. The
separate lower-bound statement records the exact shift in the cone convention.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
/-- The standard derived model used for original quasicoherent homology comparisons. -/
local instance qcHomologyDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The literal chain mapping cone has quasicoherent homology when both inputs do. -/
lemma quasicoherent_homology_mappingCone {X : Scheme.{u}} {K L : Complex X} (f : K ⟶ L)
    (hK : ∀ n, (K.homology n).IsQuasicoherent)
    (hL : ∀ n, (L.homology n).IsQuasicoherent) (n : ℤ) :
    ((CochainComplex.mappingCone f).homology n).IsQuasicoherent := by
  let T := CochainComplex.mappingCone.triangle f
  have hT := mappingConeTriangle_distinguished f
  let a := HomologicalComplex.homologyMap T.mor₁ n
  let b := HomologicalComplex.homologyMap T.mor₂ n
  let c := CochainComplex.homologyδOfTriangle T n (n+1)
  let d := HomologicalComplex.homologyMap T.mor₁ (n+1)
  have : (T.obj₁.homology n).IsQuasicoherent := hK n
  have : (T.obj₂.homology n).IsQuasicoherent := hL n
  have : (T.obj₁.homology (n+1)).IsQuasicoherent := hK (n+1)
  have : (T.obj₂.homology (n+1)).IsQuasicoherent := hL (n+1)
  exact AlgebraicGeometry.Scheme.Modules.quasicoherent_of_five_exact a b c d
    (CochainComplex.homologyMap_comp_eq_zero_of_distTriang T hT n)
    (CochainComplex.homologyMap_homologyδOfTriangle T hT n (n+1))
    (CochainComplex.homologyδOfTriangle_homologyMap T hT n (n+1))
    (CochainComplex.homologyMap_exact₂_of_distTriang T hT n)
    (CochainComplex.homologyMap_exact₃_of_distTriang T hT n (n+1))
    (CochainComplex.homologyMap_exact₁_of_distTriang T hT n (n+1))
/-- The actual cone retains the precise shifted lower cohomological bound. -/
lemma mappingCone_isGE {X : Scheme.{u}} {K L : Complex X} (f : K ⟶ L)
    (a b : ℤ) [K.IsGE a] [L.IsGE b] :
    (CochainComplex.mappingCone f).IsGE (min (a-1) b) := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  let T := CochainComplex.mappingCone.triangle f
  have hT := mappingConeTriangle_distinguished f
  apply (CochainComplex.homologyMap_exact₃_of_distTriang T hT n (n+1)).isZero_X₂
  · exact (L.exactAt_of_isGE b n (by omega)).isZero_homology.eq_of_src _ _
  · exact (K.exactAt_of_isGE a (n+1) (by omega)).isZero_homology.eq_of_tgt _ _

end Quillen.PerfectComplexes
