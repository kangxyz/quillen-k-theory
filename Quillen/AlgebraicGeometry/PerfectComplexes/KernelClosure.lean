/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.KernelClosure
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-!
# Actual kernels of epimorphisms of perfect complexes

On every scheme, the ambient categorical kernel of an epimorphism between
strict-perfect complexes is strict perfect; the corresponding assertion
holds for locally-perfect complexes. The proofs use actual termwise short
exact sequences and the original derived short-exact triangle. No
quasi-compactness, termwise splitting, or noetherianity is required.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes

/-- An actual ambient epi between strict-perfect complexes has a strict-perfect
categorical kernel, on every scheme. -/
lemma strictPerfect_kernel_of_epi {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    (hK : strictPerfect X K) (hL : strictPerfect X L) (f : K ⟶ L) [Epi f] :
    strictPerfect X (kernel f) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := {
    exact := S.exact_of_f_is_kernel (kernelIsKernel f)
    mono_f := inferInstance
    epi_g := inferInstance }
  have hs (i : ℤ) :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS i
  constructor
  · obtain ⟨a, b, hb⟩ := hK.1
    refine ⟨a, b, fun i hi => ?_⟩
    have : Mono ((kernel.ι f).f i) := (hs i).mono_f
    exact IsZero.of_mono ((kernel.ι f).f i) (hb i hi)
  · intro i
    exact @AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_kernel_of_shortExact X _ (hs i) (hK.2
      i) (hL.2 i)

/-- An actual ambient epi between locally-perfect complexes has a
locally-perfect categorical kernel, without any compactness hypothesis. -/
lemma locallyPerfect_kernel_of_epi {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    (hK : locallyPerfect X K) (hL : locallyPerfect X L) (f : K ⟶ L) [Epi f] :
    locallyPerfect X (kernel f) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := {
    exact := S.exact_of_f_is_kernel (kernelIsKernel f)
    mono_f := inferInstance
    epi_g := inferInstance }
  exact (Scheme.Modules.perfectDerivedObjects_toDerived_iff X (kernel f)).mp
    ((Scheme.Modules.perfectDerivedObjects X).ext_of_isTriangulatedClosed₁
      (DerivedCategory.triangleOfSES hS)
      (DerivedCategory.triangleOfSES_distinguished hS)
      ((Scheme.Modules.perfectDerivedObjects_toDerived_iff X K).mpr hK)
      ((Scheme.Modules.perfectDerivedObjects_toDerived_iff X L).mpr hL))

end Quillen.PerfectComplexes
