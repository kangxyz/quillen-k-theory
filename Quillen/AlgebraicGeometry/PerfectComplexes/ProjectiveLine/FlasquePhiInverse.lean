/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FirstEndpointGamma
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueGammaSecondComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueGammaThirdComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueNativePhiTransport

/-!
# Actual original affine projective-line inverse K-maps

The three natural weak-span comparisons and the literal original diagonal
additivity identify PhiG on the original model groups. The existing native
affine two-summand map is transported through the original model inclusions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiInverse
open FlasqueTwoSummands FlasqueCoefficients FlasqueTensorAdditivity FlasqueGammaEndpoints

lemma gammaFirst_KMap_eq_negative (R : CommRingCat.{u}) (n : ℕ) :
    tensorVertexKMap R .first n =
      Waldhausen.KMap ((FlasquePhiColumns.unshiftedCoefficient_exact R).comp
        (FlasquePhiColumns.negative_exact R)) n :=
  (FirstEndpoint.negativeColumn_KMap_eq_gammaFirst R n).symm

/-- The literal original Phi after G induces identity, retaining the native K0 group law. -/
theorem Phi_comp_G_KMap_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n) :
    Waldhausen.KMap (Phi_exact R) n (Waldhausen.KMap (G_exact R) n x) = x := by
  have h := tensorDiagonal_KMap_additivity R n x
  rw [gammaSecond_KMap_apply, gammaThird_KMap_apply] at h
  have hf := DFunLike.congr_fun (gammaFirst_KMap_eq_negative R n) x
  rw [hf] at h
  rw [Waldhausen.Additivity.K_mul_comm (FlasqueBoundedBelow.waldhausen (twoChartLine R))
    n _ x] at h
  calc
    _ = Waldhausen.KMap ((G0_exact R).comp (FlasquePhiColumns.positive_exact R)) n x *
        (Waldhausen.KMap ((FlasquePhiColumns.unshiftedCoefficient_exact R).comp
          (FlasquePhiColumns.negative_exact R)) n x)⁻¹ :=
      FlasquePhiColumns.Phi_comp_G_KMap_apply R n x
    _ = (x * Waldhausen.KMap ((FlasquePhiColumns.unshiftedCoefficient_exact R).comp
        (FlasquePhiColumns.negative_exact R)) n x) *
          (Waldhausen.KMap ((FlasquePhiColumns.unshiftedCoefficient_exact R).comp
            (FlasquePhiColumns.negative_exact R)) n x)⁻¹ :=
      congrArg (fun a => a * _) h
    _ = x := by rw [mul_assoc, mul_inv_cancel, mul_one]

theorem Phi_comp_G_KMap (R : CommRingCat.{u}) (n : ℕ) :
    (Waldhausen.KMap (Phi_exact R) n).comp (Waldhausen.KMap (G_exact R) n) =
      MonoidHom.id ((FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n) := by
  apply MonoidHom.ext
  intro x
  exact Phi_comp_G_KMap_apply R n x

/-- The same inverse law is the actual K-map of the original functor composite. -/
theorem PhiG_KMap_id (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap ((G_exact R).comp (Phi_exact R)) n =
      MonoidHom.id ((FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n) :=
  (Waldhausen.KMap_comp_KMap (G_exact R) (Phi_exact R) n).symm.trans (Phi_comp_G_KMap R n)

/-- Both actual original composites make the original chosen-zero Phi K-map bijective. -/
theorem Phi_KMap_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective (Waldhausen.KMap (Phi_exact R) n) := by
  constructor
  · intro a b hab
    exact (DFunLike.congr_fun (FlasquePhiEntries.G_comp_Phi_KMap R n) a).symm.trans
      ((congrArg (Waldhausen.KMap (G_exact R) n) hab).trans
        (DFunLike.congr_fun (FlasquePhiEntries.G_comp_Phi_KMap R n) b))
  · intro y
    exact ⟨Waldhausen.KMap (G_exact R) n y, DFunLike.congr_fun (Phi_comp_G_KMap R n) y⟩

theorem PhiTwoSummandKMap_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective (PhiTwoSummandKMap R n) :=
  (Phi_KMap_bijective R n).comp
    (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
      (FlasqueBoundedBelow.waldhausen (Spec R)) n).symm.bijective

/-- The EXISTING original native affine two-summand K-map is bijective in every degree. -/
theorem nativeTwoSummandKMap_affine_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective (nativeTwoSummandKMap (affineBase R) n) :=
  (PhiTwoSummandKMap_bijective_iff_native R n).mp (PhiTwoSummandKMap_bijective R n)

/-- A multiplicative equivalence whose forward map is exactly the original native map. -/
def nativeAffineTwoSummandKEquiv (R : CommRingCat.{u}) (n : ℕ) :
    PerfectK (Spec R) n × PerfectK (Spec R) n ≃*
      PerfectK (nativeLineFunctor.obj (affineBase R)).obj n :=
  MulEquiv.ofBijective (nativeTwoSummandKMap (affineBase R) n)
    (nativeTwoSummandKMap_affine_bijective R n)

lemma nativeAffineTwoSummandKEquiv_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : PerfectK (Spec R) n × PerfectK (Spec R) n) :
    nativeAffineTwoSummandKEquiv R n x = nativeTwoSummandKMap (affineBase R) n x := rfl

end Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiInverse
