/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedOpenComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.RestrictionComparison

/-!
# Original supported relative pullback on arbitrary ambient pair squares

Two genuine commuting support/localization squares induce exact bounded-flat
relative pullback. Its original K-map is transported through proved literal
inclusion comparisons on compact ambient schemes. Identity, composition and
change-weak equations retain the original maps. The target inverse-image and
fiber union-support squares are actual squares induced by their proved open
inequalities; no cartesian or flatness hypothesis is imposed.
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
    (⟨Arrow.mk j', (by change IsOpenImmersion j'; infer_instance)⟩ : Quillen.Scheme.OpenPairs.{u}) ⟶
      ⟨Arrow.mk j, (by change IsOpenImmersion j; infer_instance)⟩ :=
  ObjectProperty.homMk (Arrow.homMk g f.hom.right w.symm)

include g w in
/-- Genuine bounded-flat pullback preserves the original supported relative weak class
for any two commuting open squares, without flatness or cartesianness. -/
lemma boundedFlatPerfectSupportedOpenPullback_exact : Waldhausen.IsExact
    (boundedFlatPerfectSupportedOpenWaldhausen j T).cof
      (boundedFlatPerfectSupportedOpenWaldhausen j T).weq
    (boundedFlatPerfectSupportedOpenWaldhausen j' S).cof
      (boundedFlatPerfectSupportedOpenWaldhausen j' S).weq
    (boundedFlatPerfectSupportedPullback f) where
  zero := (boundedFlatPerfectSupportedPullback_exact f).zero
  cofibration := (boundedFlatPerfectSupportedPullback_exact f).cofibration
  pushout := (boundedFlatPerfectSupportedPullback_exact f).pushout
  weak {K L} p hp := by
    exact @boundedFlatPerfect_pairPullback_quasiIso _ _ (supportedOpenRestrictionSquare j' j f g w)
      _ _ K.property.1 L.property.1 p.hom hp

/-- The relative supported K-map induced by the given pullback square. -/
def boundedFlatPerfectSupportedOpenKPullback (n : ℕ) :
    BoundedFlatPerfectSupportedOpenK j T n →* BoundedFlatPerfectSupportedOpenK j' S n :=
  Waldhausen.KMap (boundedFlatPerfectSupportedOpenPullback_exact j' j f g w) n

lemma boundedFlatPerfectSupportedOpenKPullback_comp_changeWeak (n : ℕ) :
    (boundedFlatPerfectSupportedOpenKPullback j' j f g w n).comp
        (boundedFlatPerfectSupportedOpenKMap j T n) =
      (boundedFlatPerfectSupportedOpenKMap j' S n).comp (boundedFlatPerfectSupportedKPullback f n)
        := by
  unfold boundedFlatPerfectSupportedOpenKPullback boundedFlatPerfectSupportedOpenKMap
    boundedFlatPerfectSupportedKPullback
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

variable [CompactSpace X'] [CompactSpace X]

/-- The original supported relative groups inherit the genuine bounded-flat pullback. -/
def perfectSupportedOpenKPullback (n : ℕ) :
    PerfectSupportedOpenK j T n →* PerfectSupportedOpenK j' S n :=
  (boundedFlatPerfectSupportedOpenKEquiv j' S n).toMonoidHom.comp
    ((boundedFlatPerfectSupportedOpenKPullback j' j f g w n).comp
      (boundedFlatPerfectSupportedOpenKEquiv j T n).symm.toMonoidHom)

lemma perfectSupportedOpenKPullback_comp_boundedFlat (n : ℕ) :
    (perfectSupportedOpenKPullback j' j f g w n).comp
        (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j T n) =
      (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j' S n).comp
        (boundedFlatPerfectSupportedOpenKPullback j' j f g w n) := by
  ext x
  change boundedFlatPerfectSupportedOpenKEquiv j' S n
    (boundedFlatPerfectSupportedOpenKPullback j' j f g w n
      ((boundedFlatPerfectSupportedOpenKEquiv j T n).symm
        (boundedFlatPerfectSupportedOpenKEquiv j T n x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The same original support square in the existing compact-base pair category. -/
def qcSupportedBaseSquare :
    (⟨supportOpenPair S, (by change CompactSpace X'; infer_instance)⟩ :
      Quillen.Scheme.QuasiCompactOpenPairs.{u}) ⟶
      ⟨supportOpenPair T, (by change CompactSpace X; infer_instance)⟩ :=
  ObjectProperty.homMk f

/-- The original change-of-weak map retains the public supported pair-pullback square. -/
lemma perfectSupportedOpenKPullback_comp_changeWeak (n : ℕ) :
    (perfectSupportedOpenKPullback j' j f g w n).comp (perfectSupportedOpenKMap j T n) =
      (perfectSupportedOpenKMap j' S n).comp (perfectSupportedKPullback (qcSupportedBaseSquare f) n)
        := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedFlatPerfectSupportedToPerfectSupportedKMap_bijective T.ι n).surjective
    x
  have h₁ := DFunLike.congr_fun (boundedFlatPerfectSupportedOpenToPerfectSupportedOpen_comp j T n) y
  have h₂ := DFunLike.congr_fun (perfectSupportedOpenKPullback_comp_boundedFlat j' j f g w n)
    (boundedFlatPerfectSupportedOpenKMap j T n y)
  have h₃ := DFunLike.congr_fun (boundedFlatPerfectSupportedOpenKPullback_comp_changeWeak j' j f g w
    n) y
  have h₄ := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat (qcSupportedBaseSquare
    f) n) y
  change perfectSupportedKPullback (qcSupportedBaseSquare f) n
    (boundedFlatPerfectSupportedToPerfectSupportedKMap T.ι n y) =
    boundedFlatPerfectSupportedToPerfectSupportedKMap S.ι n
      (boundedFlatPerfectSupportedKPullback f n y) at h₄
  have h₅ := DFunLike.congr_fun (boundedFlatPerfectSupportedOpenToPerfectSupportedOpen_comp j' S n)
    (boundedFlatPerfectSupportedKPullback f n y)
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃ ⊢
  rw [← h₁, h₂, h₃]
  exact h₅.trans (congrArg (perfectSupportedOpenKMap j' S n) h₄.symm)

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

lemma perfectSupportedOpenKPullback_unique [CompactSpace X'] [CompactSpace X]
    (n : ℕ) (k : PerfectSupportedOpenK j T n →* PerfectSupportedOpenK j' S n)
    (hk : k.comp (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j T n) =
      (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j' S n).comp
        (boundedFlatPerfectSupportedOpenKPullback j' j f g w n)) :
    k = perfectSupportedOpenKPullback j' j f g w n := by
  ext x
  obtain ⟨y, rfl⟩ :=
    (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap_bijective j T n).surjective x
  exact DFunLike.congr_fun
    (hk.trans (perfectSupportedOpenKPullback_comp_boundedFlat j' j f g w n).symm) y

@[simp] lemma boundedFlatPerfectSupportedOpenKPullback_id (T : X.Opens) (n : ℕ) :
    boundedFlatPerfectSupportedOpenKPullback j j (𝟙 (supportOpenPair T)) (𝟙 U)
      (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp) n = MonoidHom.id _ :=
  (Waldhausen.KMap_eq_of_iso
    (boundedFlatPerfectSupportedOpenPullback_exact j j (𝟙 (supportOpenPair T)) (𝟙 U)
      (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp))
    (Waldhausen.IsExact.id (boundedFlatPerfectSupportedOpenWaldhausen j T).cof
      (boundedFlatPerfectSupportedOpenWaldhausen j T).weq)
    (boundedFlatPerfectSupportedPullbackIdIso (supportOpenPair T)) n).trans
      (Waldhausen.KMap_id _ n)

@[simp] lemma perfectSupportedOpenKPullback_id [CompactSpace X] (T : X.Opens) (n : ℕ) :
    perfectSupportedOpenKPullback j j (𝟙 (supportOpenPair T)) (𝟙 U)
      (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp) n = MonoidHom.id _ := by
  symm
  apply perfectSupportedOpenKPullback_unique
  simp only [boundedFlatPerfectSupportedOpenKPullback_id, MonoidHom.id_comp,
    MonoidHom.comp_id]

variable {U'' X'' : Scheme.{u}} (j'' : U'' ⟶ X'') [IsOpenImmersion j'']
  {R : X''.Opens} (f₀ : supportOpenPair R ⟶ supportOpenPair S)
  (g₀ : U'' ⟶ U') (w₀ : j'' ≫ f₀.hom.right = g₀ ≫ j')

omit [IsOpenImmersion j''] [IsOpenImmersion j'] [IsOpenImmersion j] in
include w₀ w in
lemma supportedOpenSquare_comp :
    j'' ≫ (f₀ ≫ f).hom.right = (g₀ ≫ g) ≫ j := by
  change j'' ≫ (f₀.hom.right ≫ f.hom.right) = (g₀ ≫ g) ≫ j
  rw [← Category.assoc, w₀, Category.assoc, w, Category.assoc]

lemma boundedFlatPerfectSupportedOpenKPullback_comp (n : ℕ) :
    boundedFlatPerfectSupportedOpenKPullback j'' j (f₀ ≫ f) (g₀ ≫ g)
      (supportedOpenSquare_comp j' j f g w j'' f₀ g₀ w₀) n =
    (boundedFlatPerfectSupportedOpenKPullback j'' j' f₀ g₀ w₀ n).comp
      (boundedFlatPerfectSupportedOpenKPullback j' j f g w n) :=
  (Waldhausen.KMap_eq_of_iso
    (boundedFlatPerfectSupportedOpenPullback_exact j'' j (f₀ ≫ f) (g₀ ≫ g)
      (supportedOpenSquare_comp j' j f g w j'' f₀ g₀ w₀))
    ((boundedFlatPerfectSupportedOpenPullback_exact j' j f g w).comp
      (boundedFlatPerfectSupportedOpenPullback_exact j'' j' f₀ g₀ w₀))
    (boundedFlatPerfectSupportedPullbackCompIso f₀ f) n).trans
      (Quillen.Waldhausen.KMap_comp_KMap _ _ n).symm

lemma perfectSupportedOpenKPullback_comp
    [CompactSpace X''] [CompactSpace X'] [CompactSpace X] (n : ℕ) :
    perfectSupportedOpenKPullback j'' j (f₀ ≫ f) (g₀ ≫ g)
      (supportedOpenSquare_comp j' j f g w j'' f₀ g₀ w₀) n =
    (perfectSupportedOpenKPullback j'' j' f₀ g₀ w₀ n).comp
      (perfectSupportedOpenKPullback j' j f g w n) := by
  symm
  apply perfectSupportedOpenKPullback_unique
  rw [MonoidHom.comp_assoc, perfectSupportedOpenKPullback_comp_boundedFlat,
    ← MonoidHom.comp_assoc, perfectSupportedOpenKPullback_comp_boundedFlat,
    MonoidHom.comp_assoc]
  rw [boundedFlatPerfectSupportedOpenKPullback_comp j' j f g w j'' f₀ g₀ w₀ n]

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
