/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.GlobalSectionsExactness
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Mathlib.CategoryTheory.ObjectProperty.Extensions


/-!
# Quasicoherent sheaves are closed under actual short exact extensions

On an arbitrary scheme, the middle original module sheaf in a genuine short
exact sequence is quasicoherent whenever both ends are quasicoherent. This
also supplies the standard `ObjectProperty.IsClosedUnderExtensions` instance
for the existing intrinsic quasicoherent property.

The affine proof uses exact global sections only for a sequence with a
quasicoherent kernel. Applying exact associated sheaves and the original
`fromTildeΓ` counit produces a genuine short-five-lemma diagram. In particular,
the affine middle counit itself is proved invertible. Exact restriction to
actual affine charts globalizes the result. No noetherianity, compactness,
separatedness, or quasicoherence of the middle sheaf is assumed.
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

/-- The ORIGINAL affine counit is invertible on the middle term of a
short exact sequence with quasicoherent ends. -/
lemma isIso_fromTildeΓ_of_shortExact (R : CommRingCat.{u})
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : IsIso S.X₂.fromTildeΓ := by
  let T := (S.map moduleSpecΓFunctor).map (tilde.functor R)
  have hT : T.ShortExact :=
    (AlgebraicGeometry.Scheme.Modules.AffineCech.shortExact_globalSections_of_quasicoherent_kernel
      hS).map_of_exact (tilde.functor R)
  let φ : T ⟶ S :=
    { τ₁ := S.X₁.fromTildeΓ
      τ₂ := S.X₂.fromTildeΓ
      τ₃ := S.X₃.fromTildeΓ
      comm₁₂ := (Scheme.Modules.fromTildeΓNatTrans.naturality S.f).symm
      comm₂₃ := (Scheme.Modules.fromTildeΓNatTrans.naturality S.g).symm }
  have : IsIso φ.τ₁ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁
  have : IsIso φ.τ₃ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hT hS

/-- Quasicoherence is closed under genuine ambient short exact extensions on
Spec R, with no noetherian or ambient-middle QC assumption. -/
lemma quasicoherent_of_shortExact_affine (R : CommRingCat.{u})
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent :=
  (isQuasicoherent_iff_isIso_fromTildeΓ S.X₂).mpr
    (isIso_fromTildeΓ_of_shortExact R hS)

/-- Genuine short-exact extension closure of quasicoherent module sheaves on
an arbitrary scheme. Exactness is that of the original ambient sheaf category. -/
theorem quasicoherent_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  apply AlgebraicGeometry.Scheme.Modules.QuasiCoherent.quasicoherent_of_affineCharts S.X₂
  intro R j _
  have : ((S.map (Scheme.Modules.restrictFunctor j)).X₁).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor j S.X₁
  have : ((S.map (Scheme.Modules.restrictFunctor j)).X₃).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor j S.X₃
  exact quasicoherent_of_shortExact_affine R (hS.map_of_exact (Scheme.Modules.restrictFunctor j))

/-- The existing intrinsic quasicoherent property is genuinely closed under
ambient short exact extensions. -/
instance quasicoherent_isClosedUnderExtensions (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    let : S.X₁.IsQuasicoherent := h₁
    let : S.X₃.IsQuasicoherent := h₃
    exact quasicoherent_of_shortExact hS
end AlgebraicGeometry.Scheme.Modules
