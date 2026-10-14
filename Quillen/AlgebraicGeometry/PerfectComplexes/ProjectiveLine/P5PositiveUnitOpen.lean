/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5PositiveUnitAffine
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeCoefficientsSupport

/-! # Original positive-unit descent through cartesian open base change

The restricted global total and the local total have an actual weak comparison
span. Every pushed weak arrow has bounded-below flasque source and target;
no flasqueness of the original geometric pullback is asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit


local instance positiveOpenStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

lemma totalTermsFlasque (P : Scheme.{u}) (K : CochainComplex.Plus P.Modules) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((godementTotalPlus P).obj K).obj.X n).presheaf := by
  obtain ⟨a, ha⟩ := K.property
  let := ha
  exact godementTotal_isFlasque K.obj a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE K.obj a i hi) n

lemma pushPlus_quasiIso_flasque {P X : Scheme.{u}} (p : P ⟶ X)
    {K M : CochainComplex.Plus P.Modules} (s : K ⟶ M) [QuasiIso s.hom]
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf)
    (hM : ∀ n, TopCat.Presheaf.IsFlasque (M.obj.X n).presheaf) :
    QuasiIso ((Scheme.Modules.pushforward p).mapCochainComplexPlus.map s).hom := by
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := M.property
  let := ha
  let := hb
  exact quasiIso_pushforward_of_flasque p s.hom a b
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE M.obj b n hn) hK hM

lemma quasiIso_of_QPlus_map_isIso {X : Scheme.{u}}
    {K M : CochainComplex.Plus X.Modules} (s : K ⟶ M)
    (h : IsIso (DerivedCategory.Plus.Q.map s)) : QuasiIso s.hom := by
  let := h
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).mp
  change IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map s))
  infer_instance

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

/-- The ordinary original open direct-image mate on the actual bounded complexes. -/
def openPushPlusIso :
    (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus ≅
      (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus ⋙
        (Scheme.Modules.pushforward b).mapCochainComplexPlus :=
  (Functor.mapCochainComplexPlusCompIso (Scheme.Modules.pushforward f)
    (Scheme.Modules.restrictFunctor j)).symm ≪≫
    NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b f j h) ≪≫
    Functor.mapCochainComplexPlusCompIso (Scheme.Modules.restrictFunctor a)
      (Scheme.Modules.pushforward b)

/-- Its actual second mate, with the original pullback-adjunction units. -/
def openPullPlusIso :
    (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus ⋙
        (Scheme.Modules.pullback b).mapCochainComplexPlus ≅
      (Scheme.Modules.pullback f).mapCochainComplexPlus ⋙
        (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus :=
  (Functor.mapCochainComplexPlusCompIso (Scheme.Modules.restrictFunctor j)
    (Scheme.Modules.pullback b)).symm ≪≫
    NatIso.mapCochainComplexPlus (asIso (cartesianPullbackBaseChangeMate a b f j h)) ≪≫
    Functor.mapCochainComplexPlusCompIso (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctor a)

lemma open_geometric_unit (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
        ((geometricPlusUnit f).app K) ≫
        (openPushPlusIso a b f j h).hom.app
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K) =
      (geometricPlusUnit b).app ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ≫
        (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
          ((openPullPlusIso a b f j h).hom.app K) := by
  apply ObjectProperty.hom_ext
  apply HomologicalComplex.Hom.ext
  funext n
  exact cartesianOpenBaseChange_pullback_unit a b f j h (K.obj.X n)

/-- Original local pullback maps to the restricted original global total. -/
def openTotalBridge (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.pullback b).mapCochainComplexPlus.obj
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ⟶
      (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.obj
        ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)) :=
  (openPullPlusIso a b f j h).hom.app K ≫
    (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.map
      ((godementTotalPlusUnit U).app ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))

lemma openTotalBridge_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso (openTotalBridge a b f j h K).hom := by
  have : QuasiIso ((godementTotalPlusUnit U).app
      ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom :=
    godementTotalPlusUnit_quasiIso _ _
  have hres : QuasiIso ((Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.map
      ((godementTotalPlusUnit U).app
        ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))).hom := by
    exact restrict_quasiIso a
      ((godementTotalPlusUnit U).app
        ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom
  have hiso : IsIso ((openPullPlusIso a b f j h).hom.app K) := inferInstance
  let e := (CochainComplex.Plus.ι W.Modules).mapIso ((openPullPlusIso a b f j h).app K)
  have : IsIso ((openPullPlusIso a b f j h).hom.app K).hom := by
    change IsIso e.hom
    infer_instance
  unfold openTotalBridge
  change QuasiIso (((openPullPlusIso a b f j h).hom.app K).hom ≫
    ((Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.map _).hom)
  infer_instance

lemma restrictedTotal_flasque (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    let J := (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.obj
      ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))
    TopCat.Presheaf.IsFlasque (J.obj.X n).presheaf := by
  dsimp only
  let C := (Scheme.Modules.pullback f).mapCochainComplexPlus.obj K
  exact @P5NativeCoefficients.restrictModule_isFlasque W U a inferInstance
    (((godementTotalPlus U).obj C).obj.X n) (totalTermsFlasque U C n)

/-- The literal base restriction of the global positive value. -/
def restrictedPositive (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus V.Modules :=
  (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj ((positivePlus f).obj K)

/-- The actual local positive value. -/
def localPositive (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus V.Modules :=
  (positivePlus b).obj ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)

/-- The actual restriction of the original global total. -/
abbrev restrictedTotal (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus W.Modules :=
  (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.obj
    ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))

/-- The original common target of the two actual comparison legs. -/
def openSpanTarget (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus V.Modules :=
  (Scheme.Modules.pushforward b).mapCochainComplexPlus.obj
    ((godementTotalPlus W).obj (restrictedTotal a f K))

/-- The actual base restriction of the original canonical positive unit. -/
def restrictedPositiveUnit (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K ⟶
      restrictedPositive f j K :=
  (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map ((positivePlusUnit f).app K)

/-- The original ordinary open mate applied to that same original total. -/
def openPositiveComparison (K : CochainComplex.Plus X.Modules) :
    restrictedPositive f j K ≅
      (Scheme.Modules.pushforward b).mapCochainComplexPlus.obj (restrictedTotal a f K) :=
  (openPushPlusIso a b f j h).app
    ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))

/-- The pushed augmentation on the actual restricted flasque global total. -/
def globalSpanLeg (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.pushforward b).mapCochainComplexPlus.obj (restrictedTotal a f K) ⟶
      openSpanTarget a b f K :=
  (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
    ((godementTotalPlusUnit W).app (restrictedTotal a f K))

/-- The pushed original local total of the actual geometric comparison/augmentation bridge. -/
def localSpanLeg (K : CochainComplex.Plus X.Modules) :
    localPositive b j K ⟶ openSpanTarget a b f K :=
  (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
    ((godementTotalPlus W).map (openTotalBridge a b f j h K))

lemma restrictedPositiveUnit_factor (K : CochainComplex.Plus X.Modules) :
    restrictedPositiveUnit f j K =
      (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
          ((geometricPlusUnit f).app K) ≫
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
          (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus).map
            ((godementTotalPlusUnit U).app
              ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)) := by
  unfold restrictedPositiveUnit
  rw [positivePlusUnit_app, Functor.map_comp]
  rfl

/-- Two-of-three for an actual comparison span of bounded-below complexes. -/
lemma quasiIso_of_plus_span {Y : Scheme.{u}}
    {A B C D E : CochainComplex.Plus Y.Modules}
    (u : A ⟶ B) (β : B ⟶ C) [IsIso β] (r : C ⟶ E) (v : A ⟶ D) (s : D ⟶ E)
    (he : u ≫ β ≫ r = v ≫ s)
    (hr : QuasiIso r.hom) (hv : QuasiIso v.hom) (hs : QuasiIso s.hom) :
    QuasiIso u.hom := by
  let := hr
  let := hv
  let := hs
  let e := (CochainComplex.Plus.ι Y.Modules).mapIso (asIso β)
  have : IsIso β.hom := by
    change IsIso e.hom
    infer_instance
  have : QuasiIso (u.hom ≫ (β.hom ≫ r.hom)) := by
    have hvs : QuasiIso (v.hom ≫ s.hom) := inferInstance
    have hehom : u.hom ≫ β.hom ≫ r.hom = v.hom ≫ s.hom :=
      congrArg (fun q => q.hom) he
    exact hehom.symm ▸ hvs
  exact _root_.quasiIso_of_comp_right u.hom (β.hom ≫ r.hom)

lemma globalSpanLeg_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso (globalSpanLeg a b f K).hom := by
  have : QuasiIso ((godementTotalPlusUnit W).app (restrictedTotal a f K)).hom :=
    godementTotalPlusUnit_quasiIso _ _
  exact pushPlus_quasiIso_flasque b _
    (restrictedTotal_flasque a f K) (totalTermsFlasque W (restrictedTotal a f K))

lemma localSpanLeg_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso (localSpanLeg a b f j h K).hom := by
  have : QuasiIso (openTotalBridge a b f j h K).hom :=
    openTotalBridge_quasiIso a b f j h K
  have : QuasiIso ((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom :=
    godementTotalPlus_map_quasiIso _
  exact pushPlus_quasiIso_flasque b _ (totalTermsFlasque W _) (totalTermsFlasque W _)

lemma augmentation_component_naturality {C : Type*} [Category C] [HasZeroMorphisms C]
    (T : CochainComplex.Plus C ⥤ CochainComplex.Plus C) (η : 𝟭 _ ⟶ T)
    (K L : CochainComplex.Plus C) (s : K ⟶ L) (n : ℤ) :
    s.hom.f n ≫ (η.app L).hom.f n = (η.app K).hom.f n ≫ (T.map s).hom.f n := by
  exact congrArg (fun q => q.hom.f n) (η.naturality s)

lemma openTotalBridge_f (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (openTotalBridge a b f j h K).hom.f n =
      (cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
        (Scheme.Modules.restrictFunctor a).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n) := rfl

lemma local_total_unit_component (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    ((cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
      (Scheme.Modules.restrictFunctor a).map
        (((godementTotalPlusUnit U).app
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n)) ≫
      ((godementTotalPlusUnit W).app (restrictedTotal a f K)).hom.f n =
    ((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))).hom.f n ≫
        ((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom.f n := by
  rw [← openTotalBridge_f]
  exact augmentation_component_naturality (godementTotalPlus W) (godementTotalPlusUnit W)
    ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))
    (restrictedTotal a f K) (openTotalBridge a b f j h K) n

lemma open_component_first_square (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (K.obj.X n))) ≫
        (Scheme.Modules.restrictFunctor j).map ((Scheme.Modules.pushforward f).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n))) ≫
      (cartesianOpenBaseChange a b f j h).hom.app
        (((godementTotalPlus U).obj
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).obj.X n) =
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
      ((Scheme.Modules.restrictFunctor j).obj (K.obj.X n)) ≫
    (Scheme.Modules.pushforward b).map
      ((cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
        (Scheme.Modules.restrictFunctor a).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n)) := by
  let u : (Scheme.Modules.pullback f).obj (K.obj.X n) ⟶
      ((godementTotalPlus U).obj
        ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).obj.X n :=
    ((godementTotalPlusUnit U).app
      ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n
  have hn := (cartesianOpenBaseChange a b f j h).hom.naturality u
  dsimp only [Functor.comp_map] at hn
  have he := cartesianOpenBaseChange_pullback_unit a b f j h (K.obj.X n)
  rw [Category.assoc, hn]
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor j).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (K.obj.X n))), he]
  simp only [Functor.map_comp, Category.assoc, u]

lemma open_component_second_square (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (Scheme.Modules.pushforward b).map
      ((cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
        (Scheme.Modules.restrictFunctor a).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n)) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlusUnit W).app (restrictedTotal a f K)).hom.f n) =
    (Scheme.Modules.pushforward b).map
      (((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))).hom.f n) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom.f n) := by
  have ht := congrArg (Scheme.Modules.pushforward b).map
    (local_total_unit_component a b f j h K n)
  simpa only [Functor.map_comp] using ht

lemma open_positive_unit_span_component (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (K.obj.X n))) ≫
        (Scheme.Modules.restrictFunctor j).map ((Scheme.Modules.pushforward f).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n))) ≫
      (cartesianOpenBaseChange a b f j h).hom.app
        (((godementTotalPlus U).obj
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).obj.X n) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlusUnit W).app (restrictedTotal a f K)).hom.f n) =
      ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
        ((Scheme.Modules.restrictFunctor j).obj (K.obj.X n)) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
          ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))).hom.f n)) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom.f n) := by
  rw [← Category.assoc, open_component_first_square, Category.assoc,
    open_component_second_square]
  simp only [Category.assoc]

lemma open_positive_unit_span_factorized (K : CochainComplex.Plus X.Modules) :
    ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
        ((geometricPlusUnit f).app K) ≫
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus).map
          ((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))) ≫
      (openPositiveComparison a b f j h K).hom ≫ globalSpanLeg a b f K =
    ((geometricPlusUnit b).app
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ≫
      (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
        ((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
          ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)))) ≫
      localSpanLeg a b f j h K := by
  apply ObjectProperty.hom_ext
  apply HomologicalComplex.Hom.ext
  funext n
  exact open_positive_unit_span_component a b f j h K n

/-- The same original canonical unit commutes with the actual comparison legs. -/
lemma open_positive_unit_span (K : CochainComplex.Plus X.Modules) :
    restrictedPositiveUnit f j K ≫ (openPositiveComparison a b f j h K).hom ≫
        globalSpanLeg a b f K =
      (positivePlusUnit b).app
          ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ≫
        localSpanLeg a b f j h K := by
  rw [restrictedPositiveUnit_factor, positivePlusUnit_app]
  exact open_positive_unit_span_factorized a b f j h K


include h
/-- A true local QI of the canonical unit detects the restricted global canonical unit. -/
theorem positivePlusUnit_restrict_quasiIso (K : CochainComplex.Plus X.Modules)
    (hK : QuasiIso ((positivePlusUnit b).app
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)).hom) :
    QuasiIso ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
      ((positivePlusUnit f).app K)).hom := by
  exact quasiIso_of_plus_span (restrictedPositiveUnit f j K)
    (openPositiveComparison a b f j h K).hom (globalSpanLeg a b f K)
    ((positivePlusUnit b).app ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))
    (localSpanLeg a b f j h K) (open_positive_unit_span a b f j h K)
    (globalSpanLeg_quasiIso a b f K) hK (localSpanLeg_quasiIso a b f j h K)

end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
