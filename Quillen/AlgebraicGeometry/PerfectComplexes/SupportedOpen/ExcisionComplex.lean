/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Restriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.ExtensionByZeroBaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.AffineExtension

/-!
# Actual extension by zero on supported perfect complexes

For an original open immersion `j : U ⟶ X` and auxiliary open `T`, the
actual base-change mate transfers acyclicity on `j ⁻¹ᵁ T` to acyclicity on
`T`. If the image of `j` together with `T` covers `X`, original extension by
zero preserves the existing supported perfect class: its restriction to
`U` is the given perfect complex and its restriction to `T` is acyclic.
The original global adjunction counit is then a quasi-isomorphism on this
class. There is no compactness, separation, affine, or termwise-QC premise.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open scoped ZeroObject
universe u
namespace Quillen.PerfectComplexes

lemma extensionByZero_acyclic {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K : Complex U} (hK : K.Acyclic) : ((extensionByZero j).obj K).Acyclic := by
  have hq : QuasiIso (0 : K ⟶ (0 : Complex U)) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt' _ n (acyclic_of_isZero _ (isZero_zero _) n)).mpr (hK n)
  intro n
  exact (exactAt_iff_of_quasiIsoAt ((extensionByZero j).map (0 : K ⟶ (0 : Complex U))) n).mpr
    (acyclic_of_isZero _ ((extensionByZero j).map_isZero (isZero_zero _)) n)

/-- The actual base-change mate identifies restriction to the auxiliary open
with extension of the original restriction to its inverse image. -/
def extensionByZeroSupportBaseChangeIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) :
    restrict (j ⁻¹ᵁ T).ι ⋙ extensionByZero (j.resLE T (j ⁻¹ᵁ T) le_rfl) ≅
      extensionByZero j ⋙ restrict T.ι :=
  extensionByZeroBaseChangeIso (j ⁻¹ᵁ T).ι (j.resLE T (j ⁻¹ᵁ T) le_rfl) j T.ι
    (j.resLE_comp_ι le_rfl).symm (by
      rintro x ⟨y,hy⟩
      have hyT : y ∈ j ⁻¹ᵁ T := by change j y ∈ T; rw [hy]; exact x.property
      refine ⟨⟨y,hyT⟩,?_⟩
      apply T.ι.isOpenEmbedding.injective
      change (j.resLE T (j ⁻¹ᵁ T) le_rfl ≫ T.ι) ⟨y,hyT⟩ = T.ι x
      rw [j.resLE_comp_ι]
      exact hy)

lemma extensionByZero_restrictAcyclic {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) {K : Complex U}
    (hK : ((restrict (j ⁻¹ᵁ T).ι).obj K).Acyclic) :
    ((restrict T.ι).obj ((extensionByZero j).obj K)).Acyclic := by
  intro n
  exact (extensionByZero_acyclic (j.resLE T (j ⁻¹ᵁ T) le_rfl) hK n).of_iso
    ((extensionByZeroSupportBaseChangeIso j T).app K)

/-- Global perfection follows from the actual two restricted complexes: the
original perfect source and an acyclic complex on the auxiliary open. -/
lemma perfectSupported_extensionByZero_of_cover {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
    {K : Complex U} (hK : perfectSupported (j ⁻¹ᵁ T).ι K) :
    perfectSupported T.ι ((extensionByZero j).obj K) := by
  have hT := extensionByZero_restrictAcyclic j T hK.2
  refine ⟨locallyPerfect_of_two_openImmersions j T.ι ?_ ?_ ?_,hT⟩
  · intro x
    rcases hcover x with hx | hx
    · exact Or.inl hx
    · exact Or.inr ⟨⟨x,hx⟩,rfl⟩
  · exact locallyPerfect_of_iso ((extensionByZeroRestrictIso j).app K).symm hK.1
  · have hq : QuasiIso (0 : (0 : Complex T.toScheme) ⟶ (restrict T.ι).obj ((extensionByZero j).obj
    K)) := by
      rw [quasiIso_iff]
      intro n
      exact (quasiIsoAt_iff_exactAt _ n (acyclic_of_isZero _ (isZero_zero _) n)).mpr (hT n)
    exact (locallyPerfect_iff_of_quasiIso (0 : (0 : Complex T.toScheme) ⟶ _)).mp
      (locallyPerfect_of_strictPerfect (strictPerfect_of_isZero (isZero_zero _)))

/-- The original global counit is genuinely weak on supported complexes,
by actual restriction to the two covering opens. -/
lemma extensionByZero_supported_counit_quasiIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
    {K : Complex X} (hK : perfectSupported T.ι K) :
    QuasiIso ((extensionByZeroAdjunction j).counit.app K) := by
  let V : Bool → Scheme.{u} := fun b => if b then U else T.toScheme
  let f : ∀ b, V b ⟶ X := fun b => by
    cases b with
    | false => exact T.ι
    | true => exact j
  have : ∀ b, IsOpenImmersion (f b) := by intro b; cases b <;> dsimp [f] <;> infer_instance
  apply quasiIso_of_openImmersionCover _ V f
  · intro x
    rcases hcover x with ⟨y,hy⟩ | hx
    · exact ⟨true,y,hy⟩
    · exact ⟨false,⟨x,hx⟩,rfl⟩
  · intro b
    cases b
    · change QuasiIso ((restrict T.ι).map ((extensionByZeroAdjunction j).counit.app K))
      rw [quasiIso_iff]
      intro n
      exact (quasiIsoAt_iff_exactAt _ n
        (extensionByZero_restrictAcyclic j T (perfectSupported_restrict j T hK).2 n)).mpr (hK.2 n)
    · change QuasiIso ((restrict j).map ((extensionByZeroAdjunction j).counit.app K))
      infer_instance

end Quillen.PerfectComplexes
