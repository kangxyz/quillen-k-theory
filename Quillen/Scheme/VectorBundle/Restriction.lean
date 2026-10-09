import Quillen.Scheme.VectorBundle.KTheory

/-!
# Actual open restriction of vector bundles

The local bases are transported by the same continuous-site pushforward that
implements geometric open restriction. Their index types are unchanged, so
both freeness and finiteness survive. The induced exact functor and K-map use
the underlying geometric restriction, not a surrogate module functor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w w' t t'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf

section General
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {D : Type t} [Category.{t'} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}}
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U, HasSheafify (K.over U) AddCommGrpCat.{u}]
  [∀ U, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
  (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
  [G.IsLeftAdjoint] [IsIso φ]
  [∀ U, (Over.post (X := U) G).IsContinuous (K.over U) (J.over (G.obj U))]
  [HasPullbacks C] [HasPullbacks D]

omit [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U, HasSheafify (K.over U) AddCommGrpCat.{u}]
  [∀ U, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The local restriction functors used to transport a basis preserve colimits. -/
theorem localBasisPushforward_preservesColimits (U : D) (V : C) (f : G.obj U ⟶ V) :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward.{u} (R := R.over V)
        (F := Over.post (X := U) G ⋙ Over.map f)
        (((Over.forget U).sheafPushforwardContinuous RingCat.{u} (K.over U) K).map φ)) := by
  let G' := Over.post (X := U) G ⋙ Over.map f
  have : G'.IsContinuous (K.over U) (J.over V) :=
    Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over U) (J.over V) :=
    CategoryTheory.isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over U ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over U) (J.over V)).obj (R.over V) :=
    ((Over.forget U).sheafPushforwardContinuous RingCat.{u} (K.over U) K).map φ
  have : (SheafOfModules.pushforward.{u} a).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso a
  infer_instance

/-- Transport a local basis by a continuous, cocontinuous left adjoint on
sites which carries the structure sheaf isomorphically to the target one. -/
def pushforwardLocalBasis {M : SheafOfModules.{u} R}
    (q : SheafOfModules.LocalGeneratorsData M) [q.IsLocallyFreeData] :
    SheafOfModules.LocalGeneratorsData ((SheafOfModules.pushforward φ).obj M) :=
  (q.quasiCoherentData.pushforward G φ η
    (localBasisPushforward_preservesColimits G φ)).localGeneratorsData

instance pushforwardLocalBasis_isLocallyFreeData {M : SheafOfModules.{u} R}
    (q : SheafOfModules.LocalGeneratorsData M) [q.IsLocallyFreeData] :
    (pushforwardLocalBasis G φ η q).IsLocallyFreeData where
  isIso i := by
    dsimp [pushforwardLocalBasis, SheafOfModules.QuasicoherentData.localGeneratorsData,
      SheafOfModules.QuasicoherentData.pushforward]
    rw [SheafOfModules.Presentation.map_π_eq]
    dsimp only [SheafOfModules.LocalGeneratorsData.quasiCoherentData]
    infer_instance

instance pushforwardLocalBasis_isFiniteType {M : SheafOfModules.{u} R}
    (q : SheafOfModules.LocalGeneratorsData M) [q.IsLocallyFreeData] [hq : q.IsFiniteType] :
    (pushforwardLocalBasis G φ η q).IsFiniteType where
  isFiniteType i := by
    let := hq.isFiniteType i.2.1
    constructor
    change Finite (q.generators i.2.1).I
    infer_instance

end General

/-- Actual geometric open restriction preserves finite local freeness. -/
instance finiteLocallyFree_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) [hM : IsFiniteLocallyFree X M] :
    IsFiniteLocallyFree U ((Scheme.Modules.restrictFunctor j).obj M) := by
  let α : U.presheaf ⟶ j.opensFunctor.op ⋙ X.presheaf := { app V := (j.appIso V.unop).inv }
  have hα : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : U.ringCatSheaf ⟶
      (j.opensFunctor.sheafPushforwardContinuous _ _ _).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  obtain ⟨q, hq, hf⟩ := hM.exists_localBasis
  exact ⟨pushforwardLocalBasis j.opensFunctor φ (Scheme.Modules.restrictUnitIso j) q,
    inferInstance, inferInstance⟩

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Open restriction on actual finite locally free module sheaves. -/
def vectorBundleRestrict : FiniteLocallyFree X ⥤ FiniteLocallyFree U :=
  (finiteLocallyFree U).lift
    ((finiteLocallyFree X).ι ⋙ Scheme.Modules.restrictFunctor j)
    (fun M => finiteLocallyFree_restrict j M.obj)

/-- The underlying functor is exactly geometric sheaf restriction. -/
@[simp]
theorem vectorBundleRestrict_comp_forget :
    vectorBundleRestrict j ⋙ (finiteLocallyFree U).ι =
      (finiteLocallyFree X).ι ⋙ Scheme.Modules.restrictFunctor j := rfl

instance vectorBundleRestrict_additive : (vectorBundleRestrict j).Additive := by
  dsimp [vectorBundleRestrict]
  infer_instance

/-- Actual open restriction is exact for the inherited vector-bundle
structures, because ambient sheaf restriction is exact. -/
def vectorBundleExactRestrict :
    ExactFunctor (vectorBundleExactStructure X) (vectorBundleExactStructure U) where
  toFunctor := vectorBundleRestrict j
  map_conflation S hS := by
    change ((S.map (finiteLocallyFree X).ι).map
      (Scheme.Modules.restrictFunctor j)).ShortExact
    exact hS.map_of_exact _

/-- The canonical contravariant open-restriction map on genuine scheme
K-groups, induced by actual restriction of vector bundles. -/
def schemeKRestrict (n : ℕ) : SchemeK X n →* SchemeK U n :=
  (vectorBundleExactRestrict j).smallKMap n

end Quillen.SchemeSheaf
