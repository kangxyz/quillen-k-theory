/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Cartesian
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeMayerVietorisGlue

/-! # Literal compact-open binary unions for the original native Phi property

The ambient scheme need only be quasi-separated. The actual union is used as
the compact base of the original Mayer-Vietoris sequence; its first open and
overlap are identified by canonical original open-immersion isomorphisms.
-/
@[expose] public section
open Quillen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine NativeMayerVietoris

/-- Original native Phi is bijective in every connective degree, for each compactness witness. -/
def NativePhiBijective (X : Scheme.{u}) : Prop :=
  ∀ (c : CompactSpace X) (n : ℕ), Function.Bijective (nativeTwoSummandKMap ⟨X, c⟩ n)

/-- The concrete original native property is invariant under actual scheme isomorphism. -/
theorem nativePhiBijective_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (hX : NativePhiBijective X) : NativePhiBijective Y := by
  intro cY n
  let := cY
  let : CompactSpace X := (AlgebraicGeometry.Scheme.homeoOfIso e.symm).compactSpace
  exact nativeTwoSummandKMap_bijective_of_iso (U := ⟨Y, cY⟩) (X := ⟨X, inferInstance⟩)
    e.symm n (hX inferInstance n)

/-- Accepted original affine P4 discharges the affine case of the concrete native property. -/
theorem nativePhiBijective_of_isAffine (X : Scheme.{u}) [IsAffine X] : NativePhiBijective X := by
  intro c n
  exact nativeTwoSummandKMap_bijective_of_isAffine ⟨X, c⟩ n

/-- The actual original native property is closed under literal compact-open binary unions. -/
theorem nativePhiBijective_union (Y : Scheme.{u}) [QuasiSeparatedSpace Y]
    (U V : Y.Opens) (hU : IsCompact (U : Set Y)) (hV : IsCompact (V : Set Y))
    (pU : NativePhiBijective U.toScheme) (pV : NativePhiBijective V.toScheme)
    (pI : NativePhiBijective (U ⊓ V).toScheme) : NativePhiBijective (U ⊔ V).toScheme := by
  intro c n
  let := c
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  let : QuasiSeparatedSpace (U ⊔ V).toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding (U ⊔ V).ι.isOpenEmbedding
  let : QuasiSeparatedSpace U.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding U.ι.isOpenEmbedding
  let X : QuasiCompactSchemes.{u} := ⟨(U ⊔ V).toScheme, c⟩
  let A : QuasiCompactSchemes.{u} := ⟨U.toScheme, inferInstance⟩
  let iU : U.toScheme ⟶ (U ⊔ V).toScheme := Y.homOfLE le_sup_left
  let iV : V.toScheme ⟶ (U ⊔ V).toScheme := Y.homOfLE le_sup_right
  let f : A ⟶ X := ⟨iU⟩
  let T : X.obj.Opens := iV.opensRange
  let eT : V.toScheme ≅ T.toScheme := iV.isoOpensRange
  let : IsOpenImmersion f.hom := inferInstanceAs (IsOpenImmersion iU)
  let : CompactSpace T.toScheme := (AlgebraicGeometry.Scheme.homeoOfIso eT).compactSpace
  let W : A.obj.Opens := f.hom ⁻¹ᵁ T
  let : CompactSpace W.toScheme := overlap_compactSpace f T
  have hi : (Y.homOfLE (inf_le_left : U ⊓ V ≤ U)).opensRange = W :=
    cartesian_openRange _ _ iU iV (isPullback_opens_inf_le le_sup_left le_sup_right)
  let eW : (U ⊓ V).toScheme ≅ W.toScheme :=
    IsOpenImmersion.isoOfRangeEq (Y.homOfLE inf_le_left) W.ι (by
      change ((Y.homOfLE (inf_le_left : U ⊓ V ≤ U)).opensRange : Set U.toScheme) =
        (W.ι.opensRange : Set U.toScheme)
      rw [hi, Scheme.Opens.opensRange_ι])
  let : CompactSpace (U ⊓ V).toScheme :=
    (AlgebraicGeometry.Scheme.homeoOfIso eW.symm).compactSpace
  have hc : ∀ x : X.obj, x ∈ Set.range f.hom ∨ x ∈ T := by
    intro x
    rcases x.property with hx | hx
    · exact Or.inl ⟨⟨x.val, hx⟩, by
        change Y.homOfLE le_sup_left ⟨x.val, hx⟩ = x
        exact Subtype.ext (by simp only [Scheme.homOfLE_apply])⟩
    · exact Or.inr ⟨⟨x.val, hx⟩, by
        change Y.homOfLE le_sup_right ⟨x.val, hx⟩ = x
        exact Subtype.ext (by simp only [Scheme.homOfLE_apply])⟩
  exact bijective_of_cover f T hc
    (fun m => nativeTwoSummandKMap_bijective_of_iso eT.symm m (pV inferInstance m))
    (fun m => pU inferInstance m)
    (fun m => nativeTwoSummandKMap_bijective_of_iso eW.symm m (pI inferInstance m)) n

end Quillen.PerfectComplexes.ProjectiveLine
