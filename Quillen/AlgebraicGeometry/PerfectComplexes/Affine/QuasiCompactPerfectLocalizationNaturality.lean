/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.QuasiCompactPerfectLocalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.ConnectingNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairRestriction

/-! # Naturality of the actual affine-open supported boundary -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.Affine

/-- The original affine scheme and its original open, as the established geometric pair. -/
abbrev affineOpenPair (R : CommRingCat.{u}) (W : (Spec R).Opens) :
    AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u} :=
  ⟨⟨Arrow.mk W.ι, (show IsOpenImmersion W.ι from inferInstance)⟩,
    (show CompactSpace (Spec R) from inferInstance)⟩

/-- The actual target boundary is natural for every commutative square of
qc affine-open pairs, with no flatness or cartesianness assumption. -/
theorem quasiCompactPerfectConnectingHom_pullback
    {R S : CommRingCat.{u}} {W : (Spec R).Opens} {V : (Spec S).Opens}
    (hW : IsCompact (W : Set (Spec R))) (hV : IsCompact (V : Set (Spec S)))
    (f : affineOpenPair R W ⟶ affineOpenPair S V) (n : ℕ) :
    let : CompactSpace (affineOpenPair R W).obj.obj.left :=
      (show CompactSpace W.toScheme from isCompact_iff_compactSpace.mp hW)
    let : CompactSpace (affineOpenPair S V).obj.obj.left :=
      (show CompactSpace V.toScheme from isCompact_iff_compactSpace.mp hV)
    (perfectSupportedKPullback f n).comp (quasiCompactPerfectConnectingHom S V hV n) =
      (quasiCompactPerfectConnectingHom R W hW n).comp
        (perfectKPullback f.hom.hom.left (n+1)) := by
  let : CompactSpace (affineOpenPair R W).obj.obj.left :=
      (show CompactSpace W.toScheme from isCompact_iff_compactSpace.mp hW)
  let : CompactSpace (affineOpenPair S V).obj.obj.left :=
      (show CompactSpace V.toScheme from isCompact_iff_compactSpace.mp hV)
  ext x
  obtain ⟨a, rfl⟩ := (quasiCompactPerfectOpenKEquiv S V hV n).surjective x
  have h₁ := DFunLike.congr_fun (quasiCompactPerfectConnectingHom_comp_relative S V hV n) a
  have h₂ := DFunLike.congr_fun (perfectOpenConnectingHom_pullback f n) a
  have h₃ := DFunLike.congr_fun (perfectOpenKRestrict_pullback f (n+1)) a
  have h₄ := DFunLike.congr_fun (quasiCompactPerfectConnectingHom_comp_relative R W hW n)
    (perfectOpenKPullback f (n+1) a)
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃ h₄ ⊢
  change perfectSupportedKPullback f n
      (quasiCompactPerfectConnectingHom S V hV n (perfectOpenKRestrict V.ι (n+1) a)) =
    quasiCompactPerfectConnectingHom R W hW n
      (perfectKPullback f.hom.hom.left (n+1) (perfectOpenKRestrict V.ι (n+1) a))
  change perfectSupportedKPullback f n (perfectOpenConnectingHom V.ι n a) =
    perfectOpenConnectingHom W.ι n (perfectOpenKPullback f (n+1) a) at h₂
  change perfectKPullback f.hom.hom.left (n+1) (perfectOpenKRestrict V.ι (n+1) a) =
    perfectOpenKRestrict W.ι (n+1) (perfectOpenKPullback f (n+1) a) at h₃
  change quasiCompactPerfectConnectingHom R W hW n
      (perfectOpenKRestrict W.ι (n+1) (perfectOpenKPullback f (n+1) a)) =
    perfectOpenConnectingHom W.ι n (perfectOpenKPullback f (n+1) a) at h₄
  rw [h₁, h₂, h₃, h₄]

end Quillen.PerfectComplexes.Affine
