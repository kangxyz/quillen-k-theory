/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFibration
public import Quillen.AlgebraicGeometry.PerfectComplexes.PerfectSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.KernelClosure

/-!
# Actual shift and kernel closure for supported perfect complexes

Support is the original acyclicity after an arbitrary open restriction.
The original restriction functor preserves genuine quasi-isomorphisms and
commutes with shifts. Restricting the actual epi-kernel short exact sequence
proves support of the literal kernel. Strict/local perfection is supplied by
the separately proved geometric kernel theorems on every scheme.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

lemma restrictAcyclic_iff_of_quasiIso {K L : Complex X} (f : K ⟶ L) [QuasiIso f] :
    ((restrict j).obj K).Acyclic ↔ ((restrict j).obj L).Acyclic := by
  exact forall_congr' fun n => exactAt_iff_of_quasiIsoAt ((restrict j).map f) n

lemma restrictAcyclic_shift {K : Complex X} (hK : ((restrict j).obj K).Acyclic) (n : ℤ) :
    ((restrict j).obj (K⟦n⟧)).Acyclic := by
  intro i
  have hi : (((restrict j).obj K)⟦n⟧).ExactAt i := by
    rw [exactAt_iff_isZero_homology]
    exact ((exactAt_iff_isZero_homology _ _).mp (hK (n+i))).of_iso
      ((CochainComplex.ShiftSequence.shiftIso U.Modules n i (n+i) rfl).app
        ((restrict j).obj K))
  exact hi.of_iso (((restrict j).commShiftIso n).app K).symm

lemma strictSupported_shift {K : Complex X} (hK : strictSupported j K) (n : ℤ) :
    strictSupported j (K⟦n⟧) :=
  ⟨strictPerfect_shift hK.1 n, restrictAcyclic_shift j hK.2 n⟩

lemma perfectSupported_shift {K : Complex X} (hK : perfectSupported j K) (n : ℤ) :
    perfectSupported j (K⟦n⟧) :=
  ⟨locallyPerfect_shift hK.1 n, restrictAcyclic_shift j hK.2 n⟩

lemma restrictAcyclic_kernel_of_epi {K L : Complex X} (f : K ⟶ L) [Epi f]
    (hK : ((restrict j).obj K).Acyclic) (hL : ((restrict j).obj L).Acyclic) :
    ((restrict j).obj (kernel f)).Acyclic := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := {
    exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel f)
    mono_f := inferInstance
    epi_g := inferInstance }
  apply (hS.map_of_exact (restrict j)).acyclic_X₁
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt ((restrict j).map f) n (hK n)).mpr (hL n)

lemma strictSupported_kernel_of_epi {K L : Complex X} (hK : strictSupported j K)
    (hL : strictSupported j L) (f : K ⟶ L) [Epi f] : strictSupported j (kernel f) :=
  ⟨strictPerfect_kernel_of_epi hK.1 hL.1 f, restrictAcyclic_kernel_of_epi j f hK.2 hL.2⟩

lemma perfectSupported_kernel_of_epi {K L : Complex X} (hK : perfectSupported j K)
    (hL : perfectSupported j L) (f : K ⟶ L) [Epi f] : perfectSupported j (kernel f) :=
  ⟨locallyPerfect_kernel_of_epi hK.1 hL.1 f, restrictAcyclic_kernel_of_epi j f hK.2 hL.2⟩

end Quillen.PerfectComplexes
