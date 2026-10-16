/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Localization.Serre.OverQArrows
public import Quillen.Localization.Serre.KernelPushoutComparison
public import Aglib.CategoryTheory.Abelian.SerreClass.Exact

/-! # Base change for the auxiliary kernel categories -/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace Quillen.Q
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{u} C] [Abelian C]

/-- A cartesian map on left legs and a commuting map on right legs gives
naturality of the associated Q-spans. -/
theorem span_naturality_of_pullback {X Y X' Y' : C}
    (s : AbelianSpan X Y) (t : AbelianSpan X' Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (c : s.apex ⟶ t.apex)
    [Mono a] [Mono b]
    (sq : IsPullback s.l c a t.l) (hr : s.r ≫ b = c ≫ t.r) :
    mkHom _ _ s ≫ inflationArrow b = inflationArrow a ≫ mkHom _ _ t := by
  let sq₁ : IsPullback (𝟙 s.apex) s.r s.r (𝟙 Y) := IsPullback.of_id_fst
  apply mkHom_eq_of_apexIso _ _ _ _ (sq₁.isoPullback.symm ≪≫ sq.isoPullback)
  · change (sq₁.isoPullback.inv ≫ sq.isoPullback.hom) ≫
        pullback.fst a t.l ≫ 𝟙 X = pullback.fst s.r (𝟙 Y) ≫ s.l
    simp only [Category.assoc, Category.comp_id, IsPullback.isoPullback_hom_fst]
    have h : sq₁.isoPullback.inv = pullback.fst s.r (𝟙 Y) := by
      simpa using sq₁.isoPullback_inv_fst
    rw [h]
  · change (sq₁.isoPullback.inv ≫ sq.isoPullback.hom) ≫
        pullback.snd a t.l ≫ t.r = pullback.snd s.r (𝟙 Y) ≫ b
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd_assoc]
    rw [← hr, ← Category.assoc]
    have h : sq₁.isoPullback.inv ≫ s.r = pullback.snd s.r (𝟙 Y) :=
      sq₁.isoPullback_inv_snd
    rw [h]

end Quillen.Q

namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Quillen.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]

@[reassoc (attr := simp)]
lemma overKernel_map_ι {N : C} {X Y : Over N} (f : X ⟶ Y) :
    (overKernel N).map f ≫ overKernelι Y = overKernelι X ≫ f.left :=
  (overKernel_map_isPullback f).w

/-- Naturality of slice pullback is itself an actual pullback square. -/
theorem overBaseChange_map_isPullback {M N : C} (i : M ⟶ N)
    {X Y : Over N} (f : X ⟶ Y) :
    IsPullback ((Over.pullback i).map f).left (pullback.fst X.hom i)
      (pullback.fst Y.hom i) f.left := by
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback Y.hom i).flip)
  · dsimp only [Over.pullback_map_left]
    erw [pullback.lift_snd, Over.w f]
    exact (IsPullback.of_hasPullback X.hom i).flip
  · dsimp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _

/-- Base change preserves both admissible legs and the pullbacks used in Q composition. -/
def overBaseChangeCompatible {M N : C} (i : M ⟶ N) :
    QCompatibleFunctor (overDeflation N) (overInflation N)
      (overDeflation M) (overInflation M) :=
  QCompatibleFunctor.ofPreservesPullbacks _ _ _ _ (Over.pullback i)
    (fun f h => MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
      (overBaseChange_map_isPullback i f).flip h)
    (fun f h => MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms C)
      (overBaseChange_map_isPullback i f).flip h)

/-- The actual restricted-span Q-functor of slice base change. -/
def overBaseChangeQ {M N : C} (i : M ⟶ N) : OverQ N ⥤ OverQ M :=
  (overBaseChangeCompatible i).mapQ

/-- The kernel of a base change is the same pullback kernel, via pasting. -/
def overBaseChangeKernelObjIso {M N : C} (i : M ⟶ N) (X : Over N) :
    (overKernel M).obj ((Over.pullback i).obj X) ≅ (overKernel N).obj X := by
  let sq := (IsPullback.of_hasPullback (pullback.snd X.hom i) (0 : (0 : C) ⟶ M)).paste_horiz
    (IsPullback.of_hasPullback X.hom i)
  simp only [zero_comp] at sq
  exact sq.isoPullback

@[reassoc (attr := simp)]
lemma overBaseChangeKernelObjIso_hom_ι {M N : C} (i : M ⟶ N) (X : Over N) :
    (overBaseChangeKernelObjIso i X).hom ≫ overKernelι X =
      overKernelι ((Over.pullback i).obj X) ≫ pullback.fst X.hom i := by
  exact IsPullback.isoPullback_hom_fst _

/-- Taking the kernel commutes naturally with arbitrary change of base. -/
def overBaseChangeKernelIso {M N : C} (i : M ⟶ N) :
    Over.pullback i ⋙ overKernel M ≅ overKernel N :=
  NatIso.ofComponents (overBaseChangeKernelObjIso i) (by
    intro X Y f
    apply (cancel_mono (overKernelι Y)).1
    simp only [Functor.comp_map, Category.assoc, overBaseChangeKernelObjIso_hom_ι,
      overKernel_map_ι_assoc, overKernel_map_ι, overBaseChangeKernelObjIso_hom_ι_assoc]
    rw [(overBaseChange_map_isPullback i f).w])

/-- An ordinary natural isomorphism of compatible functors induces a
natural isomorphism on their actual quotient span categories. -/
def compatibleKernelQIso
    {D : Type u} [Category.{u} D]
    {W V : MorphismProperty D}
    [W.ContainsIdentities] [V.ContainsIdentities]
    [W.IsStableUnderComposition] [V.IsStableUnderComposition]
    [W.HasPullbacksAgainst V] [W.IsStableUnderBaseChangeAgainst V]
    [V.IsStableUnderBaseChangeAgainst W]
    (F G : QCompatibleFunctor W V (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation) (e : F.toFunctor ≅ G.toFunctor) :
    F.mapQ ≅ G.mapQ :=
  NatIso.ofComponents (fun X => (abelianExactStructure C).qIsoOfIso (e.app X.obj.of)) (by
    rintro X Y ⟨s⟩
    change Q.mkHom _ _ (F.mapSpan s) ≫ Q.inflationArrow (e.app Y.obj.of).hom =
      Q.inflationArrow (e.app X.obj.of).hom ≫ Q.mkHom _ _ (G.mapSpan s)
    apply Q.span_naturality_of_pullback _ _ _ _ (e.app s.apex).hom
    · exact IsPullback.of_vert_isIso ⟨e.hom.naturality s.l⟩
    · exact e.hom.naturality s.r)

/-- The kernel comparison is natural on Q-arrows, with the chosen ordinary
pullback comparison as its component. -/
def overBaseChangeKernelQIso {M N : C} (i : M ⟶ N) :
    overBaseChangeQ i ⋙ overKernelQ M ≅ overKernelQ N :=
  NatIso.ofComponents
    (fun X => (abelianExactStructure C).qIsoOfIso ((overBaseChangeKernelIso i).app X.obj.of))
    (by
      rintro X Y ⟨s⟩
      exact (compatibleKernelQIso ((overBaseChangeCompatible i).comp (overKernelCompatible M))
        (overKernelCompatible N) (overBaseChangeKernelIso i)).hom.naturality (Q.mkHom _ _ s))

/-- Postcomposition changes the base without changing underlying span legs. -/
def overPostcomposeCompatible {M N : C} (i : M ⟶ N) :
    QCompatibleFunctor (overDeflation M) (overInflation M)
      (overDeflation N) (overInflation N) := by
  have : PreservesLimitsOfShape WalkingCospan (Over.map i) := by
    have : PreservesLimitsOfShape WalkingCospan (Over.map i ⋙ Over.forget N) :=
      inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Over.forget M))
    exact preservesLimitsOfShape_of_reflects_of_preserves (Over.map i) (Over.forget N)
  exact QCompatibleFunctor.ofPreservesPullbacks _ _ _ _ (Over.map i)
    (fun _ h => h) (fun _ h => h)

/-- The functor from `OverQ M` to `OverQ N` induced by postcomposing each slice structure map
with `i : M ⟶ N`. -/
def overPostcomposeQ {M N : C} (i : M ⟶ N) : OverQ M ⥤ OverQ N :=
  (overPostcomposeCompatible i).mapQ

/-- A monomorphic change of base does not change the kernel object. -/
def overPostcomposeKernelObjIso {M N : C} (i : M ⟶ N) [Mono i] (X : Over M) :
    (overKernel N).obj ((Over.map i).obj X) ≅ (overKernel M).obj X :=
  (overKernelIsKernel ((Over.map i).obj X)).conePointUniqueUpToIso
    (isKernelCompMono (overKernelIsKernel X) i rfl)

@[reassoc (attr := simp)]
lemma overPostcomposeKernelObjIso_hom_ι {M N : C} (i : M ⟶ N) [Mono i] (X : Over M) :
    (overPostcomposeKernelObjIso i X).hom ≫ overKernelι X =
      overKernelι ((Over.map i).obj X) :=
  (overKernelIsKernel ((Over.map i).obj X)).conePointUniqueUpToIso_hom_comp
    (isKernelCompMono (overKernelIsKernel X) i rfl) .zero

/-- The postcomposition comparison of kernels is natural on ordinary slice maps. -/
def overPostcomposeKernelIso {M N : C} (i : M ⟶ N) [Mono i] :
    Over.map i ⋙ overKernel N ≅ overKernel M :=
  NatIso.ofComponents (overPostcomposeKernelObjIso i) (by
    intro X Y f
    apply (cancel_mono (overKernelι Y)).1
    simp only [Category.assoc, overPostcomposeKernelObjIso_hom_ι]
    rw [(overKernel_map_isPullback f).w]
    rw [← Category.assoc, overPostcomposeKernelObjIso_hom_ι]
    exact (overKernel_map_isPullback ((Over.map i).map f)).w)

/-- The postcomposition kernel comparison lifts to actual Q-arrows. -/
def overPostcomposeKernelQIso {M N : C} (i : M ⟶ N) [Mono i] :
    overPostcomposeQ i ⋙ overKernelQ N ≅ overKernelQ M :=
  NatIso.ofComponents
    (fun X => (abelianExactStructure C).qIsoOfIso ((overPostcomposeKernelIso i).app X.obj.of))
    (by
      rintro X Y ⟨s⟩
      exact (compatibleKernelQIso ((overPostcomposeCompatible i).comp (overKernelCompatible N))
        (overKernelCompatible M) (overPostcomposeKernelIso i)).hom.naturality (Q.mkHom _ _ s))

/-- The canonical pullback inclusion is monic when the change of base is. -/
instance overBaseChangeCounit_mono {M N : C} (i : M ⟶ N) [Mono i] (X : Over N) :
    Mono ((Over.mapPullbackAdj i).counit.app X).left := by
  simpa only [Over.mapPullbackAdj_counit_app] using
    (inferInstanceAs (Mono (pullback.fst X.hom i)))

/-- The pullback inclusion gives a natural transformation on Q-categories;
its naturality follows from the actual cartesian square on each left leg. -/
def overBaseChangeCounitQ {M N : C} (i : M ⟶ N) [Mono i] :
    overBaseChangeQ i ⋙ overPostcomposeQ i ⟶ 𝟭 (OverQ N) where
  app X := overInflationArrow ((Over.mapPullbackAdj i).counit.app X.obj.of)
  naturality X Y f := by
    obtain ⟨s, rfl⟩ := Quotient.exists_rep f
    apply (overForgetQ N).map_injective
    simp only [Functor.map_comp, overForgetQ_inflationArrow, Over.mapPullbackAdj_counit_app]
    change Q.mkHom _ _ ((overForgetCompatible N).mapSpan
      ((overPostcomposeCompatible i).mapSpan ((overBaseChangeCompatible i).mapSpan s))) ≫
        Q.inflationArrow (pullback.fst Y.obj.of.hom i) =
      Q.inflationArrow (pullback.fst X.obj.of.hom i) ≫
        Q.mkHom _ _ ((overForgetCompatible N).mapSpan s)
    apply Q.span_naturality_of_pullback _ _ _ _ (pullback.fst s.apex.hom i)
    · exact overBaseChange_map_isPullback i s.l
    · exact (overBaseChange_map_isPullback i s.r).w

/-- The pullback counit's map on kernels is the composite of the two
canonical change-of-base identifications. -/
lemma overBaseChangeCounit_kernel {M N : C} (i : M ⟶ N) [Mono i] (X : Over N) :
    (overKernel N).map ((Over.mapPullbackAdj i).counit.app X) =
      (overPostcomposeKernelObjIso i ((Over.pullback i).obj X)).hom ≫
        (overBaseChangeKernelObjIso i X).hom := by
  apply (cancel_mono (overKernelι X)).1
  calc
    _ = overKernelι ((Over.map i).obj ((Over.pullback i).obj X)) ≫ pullback.fst X.hom i := by
      simp [Over.mapPullbackAdj_counit_app]
    _ = _ := by
      simp only [Category.assoc, overBaseChangeKernelObjIso_hom_ι,
        overPostcomposeKernelObjIso_hom_ι_assoc]

/-- Kernel compatibility of the actual Q-valued pullback counit. -/
lemma overBaseChangeCounitQ_kernel {M N : C} (i : M ⟶ N) [Mono i] (X : OverQ N) :
    (overKernelQ N).map ((overBaseChangeCounitQ i).app X) =
      (overPostcomposeKernelQIso i).hom.app ((overBaseChangeQ i).obj X) ≫
        (overBaseChangeKernelQIso i).hom.app X := by
  change (overKernelQ N).map (overInflationArrow _) = _
  rw [overKernelQ_inflationArrow]
  change Q.inflationArrow ((overKernel N).map ((Over.mapPullbackAdj i).counit.app X.obj.of)) =
    Q.inflationArrow (overPostcomposeKernelObjIso i ((Over.pullback i).obj X.obj.of)).hom ≫
      Q.inflationArrow (overBaseChangeKernelObjIso i X.obj.of).hom
  rw [Q.inflationArrow_comp]
  simp only [overBaseChangeCounit_kernel]

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- Pullback retains the Serre-isomorphism condition on the structure map. -/
theorem overBaseChange_isoModSerre {M N : C} (i : M ⟶ N) (X : Over N)
    (hX : P.isoModSerre X.hom) : P.isoModSerre ((Over.pullback i).obj X).hom :=
  MorphismProperty.of_isPullback (P := P.isoModSerre)
    (IsPullback.of_hasPullback X.hom i) hX

/-- Change of base on the full auxiliary categories. -/
def auxiliaryBaseChange {M N : C} (i : M ⟶ N) :
    AuxiliaryKernel P N ⥤ AuxiliaryKernel P M where
  obj X := ⟨(overBaseChangeQ i).obj X.obj,
    overBaseChange_isoModSerre P i X.obj.obj.of X.property⟩
  map f := ObjectProperty.homMk ((overBaseChangeQ i).map f.hom)
  map_id X := by apply ObjectProperty.hom_ext; exact (overBaseChangeQ i).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; exact (overBaseChangeQ i).map_comp _ _

/-- Change of base on epimorphic auxiliary objects. -/
def epiAuxiliaryBaseChange {M N : C} (i : M ⟶ N) :
    EpiAuxiliaryKernel P N ⥤ EpiAuxiliaryKernel P M where
  obj X := ⟨(overBaseChangeQ i).obj X.obj,
    overBaseChange_isoModSerre P i X.obj.obj.of X.property.1,
    MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
      (IsPullback.of_hasPullback X.obj.obj.of.hom i) X.property.2⟩
  map f := ObjectProperty.homMk ((overBaseChangeQ i).map f.hom)
  map_id X := by apply ObjectProperty.hom_ext; exact (overBaseChangeQ i).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; exact (overBaseChangeQ i).map_comp _ _

/-- A Serre-isomorphic change of base sends auxiliary objects forward. -/
def auxiliaryPostcompose {M N : C} (i : M ⟶ N) (hi : P.isoModSerre i) :
    AuxiliaryKernel P M ⥤ AuxiliaryKernel P N where
  obj X := ⟨(overPostcomposeQ i).obj X.obj,
    P.isoModSerre.comp_mem X.obj.obj.of.hom i X.property hi⟩
  map f := ObjectProperty.homMk ((overPostcomposeQ i).map f.hom)
  map_id X := by apply ObjectProperty.hom_ext; exact (overPostcomposeQ i).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; exact (overPostcomposeQ i).map_comp _ _

/-- The monomorphic pullback counit restricts to the actual auxiliary categories. -/
def auxiliaryBaseChangeCounit {M N : C} (i : M ⟶ N) [Mono i] (hi : P.isoModSerre i) :
    auxiliaryBaseChange P i ⋙ auxiliaryPostcompose P i hi ⟶ 𝟭 (AuxiliaryKernel P N) where
  app X := ObjectProperty.homMk ((overBaseChangeCounitQ i).app X.obj)
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    exact (overBaseChangeCounitQ i).naturality f.hom

/-- The base-change kernel comparison retains values in the Serre Q-category. -/
def auxiliaryBaseChangeKernelIso {M N : C} (i : M ⟶ N) :
    auxiliaryBaseChange P i ⋙ auxiliaryKernelFunctor P M ≅ auxiliaryKernelFunctor P N :=
  NatIso.ofComponents
    (fun X => (Devissage.mapQ P).preimageIso ((overBaseChangeKernelQIso i).app X.obj)) (by
      intro X Y f
      apply (Devissage.mapQ P).map_injective
      simp only [Functor.comp_map, auxiliaryBaseChange, auxiliaryKernelFunctor,
        Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (overBaseChangeKernelQIso i).hom.naturality f.hom)

/-- The postcomposition kernel comparison retains values in the Serre Q-category. -/
def auxiliaryPostcomposeKernelIso {M N : C} (i : M ⟶ N) [Mono i]
    (hi : P.isoModSerre i) :
    auxiliaryPostcompose P i hi ⋙ auxiliaryKernelFunctor P N ≅ auxiliaryKernelFunctor P M :=
  NatIso.ofComponents
    (fun X => (Devissage.mapQ P).preimageIso ((overPostcomposeKernelQIso i).app X.obj)) (by
      intro X Y f
      apply (Devissage.mapQ P).map_injective
      simp only [Functor.comp_map, auxiliaryPostcompose, auxiliaryKernelFunctor,
        Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (overPostcomposeKernelQIso i).hom.naturality f.hom)

/-- The auxiliary counit satisfies the exact kernel identity needed to lift
it to kernel comma categories. -/
lemma auxiliaryBaseChangeCounit_kernel {M N : C} (i : M ⟶ N) [Mono i]
    (hi : P.isoModSerre i) (X : AuxiliaryKernel P N) :
    (auxiliaryKernelFunctor P N).map ((auxiliaryBaseChangeCounit P i hi).app X) =
      (auxiliaryPostcomposeKernelIso P i hi).hom.app ((auxiliaryBaseChange P i).obj X) ≫
        (auxiliaryBaseChangeKernelIso P i).hom.app X := by
  apply (Devissage.mapQ P).map_injective
  simp only [Functor.map_comp, auxiliaryBaseChangeCounit, auxiliaryKernelFunctor,
    auxiliaryPostcomposeKernelIso, auxiliaryBaseChangeKernelIso, NatIso.ofComponents_hom_app,
    Functor.preimageIso_hom, Functor.map_preimage]
  exact overBaseChangeCounitQ_kernel i X.obj

end Quillen.SerreLocalization
