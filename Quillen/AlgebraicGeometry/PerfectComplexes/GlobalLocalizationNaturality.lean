/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.ConnectingNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairRestriction

/-!
# Naturality of original qcqs perfect localization

The actual positive inverse endpoint and supported boundary commute with the
original K-pullback maps for every commutative open-pair square whose bases
are qcqs and opens are quasi-compact. All three arrows of the connective
localization sequence are natural, including the boundary into supported
K-zero. No flatness or cartesianness assumption is required.

The proof uses the literal original relative restriction and boundary squares
and the surjectivity already proved for their actual positive endpoint.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes

/-- The actual target boundary is natural for every commutative square of
qcqs open pairs, with no flatness or cartesianness assumption. -/
theorem qcqsPerfectConnectingHom_pullback
    {A B : Quillen.Scheme.QuasiCompactOpenPairs.{u}}
    [QuasiSeparatedSpace A.obj.obj.right] [QuasiSeparatedSpace B.obj.obj.right]
    [CompactSpace A.obj.obj.left] [CompactSpace B.obj.obj.left]
    (f : A ⟶ B) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (qcqsPerfectConnectingHom B.obj.obj.hom n) =
      (qcqsPerfectConnectingHom A.obj.obj.hom n).comp
        (perfectKPullback f.hom.hom.left (n+1)) := by
  ext x
  obtain ⟨a, rfl⟩ := (qcqsPerfectOpenKEquiv B.obj.obj.hom n).surjective x
  have h₁ := DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_relative B.obj.obj.hom n) a
  have h₂ := DFunLike.congr_fun (perfectOpenConnectingHom_pullback f n) a
  have h₃ := DFunLike.congr_fun (perfectOpenKRestrict_pullback f (n+1)) a
  have h₄ := DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_relative A.obj.obj.hom n)
    (perfectOpenKPullback f (n+1) a)
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃ h₄ ⊢
  change perfectSupportedKPullback f n
      (qcqsPerfectConnectingHom B.obj.obj.hom n (perfectOpenKRestrict B.obj.obj.hom (n+1) a)) =
    qcqsPerfectConnectingHom A.obj.obj.hom n
      (perfectKPullback f.hom.hom.left (n+1) (perfectOpenKRestrict B.obj.obj.hom (n+1) a))
  change perfectSupportedKPullback f n (perfectOpenConnectingHom B.obj.obj.hom n a) =
    perfectOpenConnectingHom A.obj.obj.hom n (perfectOpenKPullback f (n+1) a) at h₂
  change perfectKPullback f.hom.hom.left (n+1) (perfectOpenKRestrict B.obj.obj.hom (n+1) a) =
    perfectOpenKRestrict A.obj.obj.hom (n+1) (perfectOpenKPullback f (n+1) a) at h₃
  change qcqsPerfectConnectingHom A.obj.obj.hom n
      (perfectOpenKRestrict A.obj.obj.hom (n+1) (perfectOpenKPullback f (n+1) a)) =
    perfectOpenConnectingHom A.obj.obj.hom n (perfectOpenKPullback f (n+1) a) at h₄
  rw [h₁, h₂, h₃, h₄]

/-- The actual inverse endpoint is natural under the same original pair maps. -/
theorem qcqsPerfectOpenKEquiv_symm_pullback
    {A B : Quillen.Scheme.QuasiCompactOpenPairs.{u}}
    [QuasiSeparatedSpace A.obj.obj.right] [QuasiSeparatedSpace B.obj.obj.right]
    [CompactSpace A.obj.obj.left] [CompactSpace B.obj.obj.left]
    (f : A ⟶ B) (n : ℕ) :
    (perfectOpenKPullback f (n+1)).comp
        (qcqsPerfectOpenKEquiv B.obj.obj.hom n).symm.toMonoidHom =
      (qcqsPerfectOpenKEquiv A.obj.obj.hom n).symm.toMonoidHom.comp
        (perfectKPullback f.hom.hom.left (n+1)) := by
  ext x
  apply qcqs_perfectOpenKRestrict_injective A.obj.obj.hom (n+1)
  have h := DFunLike.congr_fun (perfectOpenKRestrict_pullback f (n+1))
    ((qcqsPerfectOpenKEquiv B.obj.obj.hom n).symm x)
  simp only [MonoidHom.comp_apply] at h ⊢
  change perfectOpenKRestrict A.obj.obj.hom (n+1)
      (perfectOpenKPullback f (n+1) ((qcqsPerfectOpenKEquiv B.obj.obj.hom n).symm x)) =
    perfectOpenKRestrict A.obj.obj.hom (n+1)
      ((qcqsPerfectOpenKEquiv A.obj.obj.hom n).symm
        (perfectKPullback f.hom.hom.left (n+1) x))
  rw [← h]
  change perfectKPullback f.hom.hom.left (n+1)
      (qcqsPerfectOpenKEquiv B.obj.obj.hom n
        ((qcqsPerfectOpenKEquiv B.obj.obj.hom n).symm x)) =
    qcqsPerfectOpenKEquiv A.obj.obj.hom n
      ((qcqsPerfectOpenKEquiv A.obj.obj.hom n).symm
        (perfectKPullback f.hom.hom.left (n+1) x))
  simp only [MulEquiv.apply_symm_apply]

/-- All original arrows in the connective sequence commute with the same
arbitrary open-pair pullback, including the supported degree-zero boundary. -/
theorem qcqsPerfect_longExactSequence_pullback
    {A B : Quillen.Scheme.QuasiCompactOpenPairs.{u}}
    [QuasiSeparatedSpace A.obj.obj.right] [QuasiSeparatedSpace B.obj.obj.right]
    [CompactSpace A.obj.obj.left] [CompactSpace B.obj.obj.left]
    (f : A ⟶ B) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (qcqsPerfectConnectingHom B.obj.obj.hom n) =
        (qcqsPerfectConnectingHom A.obj.obj.hom n).comp
          (perfectKPullback f.hom.hom.left (n+1)) ∧
      (perfectKPullback f.hom.hom.right n).comp (perfectSupportedKMap B.obj.obj.hom n) =
        (perfectSupportedKMap A.obj.obj.hom n).comp (perfectSupportedKPullback f n) ∧
      (perfectKPullback f.hom.hom.left n).comp (perfectKRestrict B.obj.obj.hom n) =
        (perfectKRestrict A.obj.obj.hom n).comp (perfectKPullback f.hom.hom.right n) :=
  ⟨qcqsPerfectConnectingHom_pullback f n, perfectSupportedKMap_pullback f n,
    perfectKRestrict_pairPullback f n⟩

end Quillen.PerfectComplexes
