/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Pairs

/-!
# Actual squares of support and localization opens

The given two commuting open squares induce the original inverse-image and union support squares. Every scheme map, inequality and compact-ambient wrapper is retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.hom.right = g ≫ j)

/-- The second actual square, involving the original localization opens. -/
def supportedOpenRestrictionSquare :
    (⟨Arrow.mk j', (by change IsOpenImmersion j'; infer_instance)⟩ :
      AlgebraicGeometry.Scheme.OpenPairs.{u}) ⟶
      ⟨Arrow.mk j, (by change IsOpenImmersion j; infer_instance)⟩ :=
  ObjectProperty.homMk (Arrow.homMk g f.hom.right w.symm)

variable [CompactSpace X'] [CompactSpace X]

/-- The same original support square in the existing compact-base pair category. -/
def qcSupportedBaseSquare :
    (⟨supportOpenPair S, (by change CompactSpace X'; infer_instance)⟩ :
      AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}) ⟶
      ⟨supportOpenPair T, (by change CompactSpace X; infer_instance)⟩ :=
  ObjectProperty.homMk f

end Quillen.PerfectComplexes

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.hom.right = g ≫ j)

variable {U'' X'' : Scheme.{u}} (j'' : U'' ⟶ X'') [IsOpenImmersion j'']
  {R : X''.Opens} (f₀ : supportOpenPair R ⟶ supportOpenPair S)
  (g₀ : U'' ⟶ U') (w₀ : j'' ≫ f₀.hom.right = g₀ ≫ j')

omit [IsOpenImmersion j''] [IsOpenImmersion j'] [IsOpenImmersion j] in
include w₀ w in
lemma supportedOpenSquare_comp :
    j'' ≫ (f₀ ≫ f).hom.right = (g₀ ≫ g) ≫ j := by
  change j'' ≫ (f₀.hom.right ≫ f.hom.right) = (g₀ ≫ g) ≫ j
  rw [← Category.assoc, w₀, Category.assoc, w, Category.assoc]

end Quillen.PerfectComplexes

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.hom.right = g ≫ j)

lemma supportPair_le_preimage : S ≤ f.hom.right ⁻¹ᵁ T := by
  intro x hx
  let y : T := f.hom.left ⟨x,hx⟩
  have he : y.val = f.hom.right x :=
    congrArg (fun k : S.toScheme ⟶ X => k ⟨x,hx⟩) (Arrow.w f.hom)
  change f.hom.right x ∈ T
  exact he ▸ y.property

omit [IsOpenImmersion j'] [IsOpenImmersion j] in
include w in
lemma supportedPair_target_le_preimage : j' ⁻¹ᵁ S ≤ g ⁻¹ᵁ (j ⁻¹ᵁ T) := by
  intro x hx
  have he := congrArg (fun k : U' ⟶ X => k x) w
  change f.hom.right (j' x) = j (g x) at he
  change j (g x) ∈ T
  rw [← he]
  exact supportPair_le_preimage f hx

/-- The induced square on the inverse-image supports of the given open square. -/
def supportedPairTargetSquare : supportOpenPair (j' ⁻¹ᵁ S) ⟶ supportOpenPair (j ⁻¹ᵁ T) :=
  ObjectProperty.homMk (Arrow.homMk
    (g.resLE (j ⁻¹ᵁ T) (j' ⁻¹ᵁ S) (supportedPair_target_le_preimage j' j f g w)) g
    (g.resLE_comp_ι (supportedPair_target_le_preimage j' j f g w)))

include w in
lemma supportedPair_union_le_preimage :
    S ⊔ j'.opensRange ≤ f.hom.right ⁻¹ᵁ (T ⊔ j.opensRange) := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (supportPair_le_preimage f hx)
  · rcases hx with ⟨y, rfl⟩
    right
    refine ⟨g y, ?_⟩
    exact (congrArg (fun k : U' ⟶ X => k y) w).symm

/-- The induced square on supports enlarged by the corresponding open ranges. -/
def supportedPairUnionSquare : supportOpenPair (S ⊔ j'.opensRange) ⟶ supportOpenPair (T ⊔
  j.opensRange) :=
  ObjectProperty.homMk (Arrow.homMk
    (f.hom.right.resLE (T ⊔ j.opensRange) (S ⊔ j'.opensRange)
      (supportedPair_union_le_preimage j' j f g w)) f.hom.right
    (f.hom.right.resLE_comp_ι (supportedPair_union_le_preimage j' j f g w)))

end Quillen.PerfectComplexes

end

end
