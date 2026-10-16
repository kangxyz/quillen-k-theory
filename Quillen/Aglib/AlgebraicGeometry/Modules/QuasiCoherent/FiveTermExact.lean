/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Extensions

/-! # Quasicoherence in an original five-term exact sequence

Four quasicoherent outer terms force quasicoherence of the middle term.
The proof constructs the actual short exact sequence between the cokernel of
its first arrow and the kernel of its last arrow. It does not claim arbitrary
subobjects of quasicoherent sheaves are quasicoherent.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Original ambient exactness and four quasicoherent ends detect the middle sheaf. -/

lemma quasicoherent_of_five_exact {X : Scheme.{u}}
    {A B C D E : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E)
    (wfg : f ≫ g = 0) (wgh : g ≫ h = 0) (whk : h ≫ k = 0)
    (hfg : (ShortComplex.mk f g wfg).Exact)
    (hgh : (ShortComplex.mk g h wgh).Exact)
    (hhk : (ShortComplex.mk h k whk).Exact)
    [A.IsQuasicoherent] [B.IsQuasicoherent] [D.IsQuasicoherent] [E.IsQuasicoherent] :
    C.IsQuasicoherent := by
  let a := cokernel.desc f g wfg
  let b := kernel.lift k h whk
  have ha : Mono a := hfg.mono_cokernelDesc
  have hb : Epi b := hhk.epi_kernelLift
  have wah : a ≫ h = 0 := by
    apply (cancel_epi (cokernel.π f)).mp
    simp only [a, cokernel.π_desc_assoc, comp_zero, wgh]
  have wab : a ≫ b = 0 := by
    apply (cancel_mono (kernel.ι k)).mp
    simp only [Category.assoc, b, kernel.lift_ι, zero_comp, wah]
  let S := ShortComplex.mk a b wab
  let T := ShortComplex.mk a h wah
  let φ : ShortComplex.mk g h wgh ⟶ T :=
    { τ₁ := cokernel.π f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, a] }
  let ψ : S ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι k
      comm₂₃ := by simp [S, T, b] }
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hgh
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hT }
  have : S.X₁.IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.quasicoherent_cokernel f
  have : S.X₃.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.quasicoherent_kernel
    k
  exact quasicoherent_of_shortExact hS

end AlgebraicGeometry.Scheme.Modules
