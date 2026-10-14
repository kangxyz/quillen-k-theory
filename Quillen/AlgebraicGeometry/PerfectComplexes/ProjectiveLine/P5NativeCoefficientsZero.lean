/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeProjectionPerfect

/-! # The literal zero coefficient over every native quasi-compact base

The original ordinary pushforward is exact on the flasque perfect model.
Perfection uses the accepted native projection theorem; no caller supplies a
pushforward-perfection or resolution premise.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Scheme Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeCoefficients
open FlasqueCoefficients

local instance nativeZeroStandardDerived (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _

/-- The underlying zero coefficient is the literal original degreewise direct image. -/
def G0Raw (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj ⥤ Complex X.obj :=
  (FlasqueBoundedBelow.objects (nativeLineFunctor.obj X).obj).ι ⋙
    (Scheme.Modules.pushforward (nativeProjection.app X).hom).mapHomologicalComplex (.up ℤ)

instance G0Raw_additive (X : QuasiCompactSchemes.{u}) : (G0Raw X).Additive := by
  unfold G0Raw
  infer_instance

/-- The installed natural unit and intrinsic P2 theorem give actual local perfection. -/
lemma G0_locallyPerfect (X : QuasiCompactSchemes.{u}) (K : FlasqueBoundedBelow.Obj
    (nativeLineFunctor.obj X).obj) :
    locallyPerfect X.obj ((G0Raw X).obj K) :=
  locallyPerfect_nativeProjection_flasque X K

/-- Ordinary direct image retains each specified strict lower bound. -/
lemma G0Raw_isStrictlyGE (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((G0Raw X).obj K).IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (Scheme.Modules.pushforward (nativeProjection.app X).hom).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

/-- The actual ordinary direct image has flasque terms and remains in the original model. -/
lemma G0_objects (X : QuasiCompactSchemes.{u}) (K : FlasqueBoundedBelow.Obj
    (nativeLineFunctor.obj X).obj) :
    FlasqueBoundedBelow.objects X.obj ((G0Raw X).obj K) := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  refine ⟨⟨G0_locallyPerfect X K, a, G0Raw_isStrictlyGE X K a⟩, fun n => ?_⟩
  let : TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf := K.property.2 n
  change TopCat.Presheaf.IsFlasque
    ((Scheme.Modules.pushforward (nativeProjection.app X).hom).obj (K.obj.X n)).presheaf
  infer_instance

/-- The actual zero coefficient, with values in the full original flasque-perfect category. -/
def G0 (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj ⥤ FlasqueBoundedBelow.Obj X.obj :=
  ObjectProperty.lift _ (G0Raw X) (G0_objects X)

instance G0_additive (X : QuasiCompactSchemes.{u}) : (G0 X).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (G0Raw X).map (f + g) = (G0Raw X).map f + (G0Raw X).map g
    exact CategoryTheory.Functor.map_add (G0Raw X)

/-- Exactness uses the proved original flasque-kernel section lifts. -/
def G0ExactFunctor (X : QuasiCompactSchemes.{u}) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (nativeLineFunctor.obj X).obj))
      (FlasqueBoundedBelow.objects (nativeLineFunctor.obj X).obj))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex X.obj))
      (FlasqueBoundedBelow.objects X.obj)) where
  toFunctor := G0 X
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects (nativeLineFunctor.obj X).obj).ι).ShortExact at hS
    change ((S.map (FlasqueBoundedBelow.objects (nativeLineFunctor.obj X).obj).ι).map
      ((Scheme.Modules.pushforward (nativeProjection.app X).hom).mapHomologicalComplex (.up
        ℤ))).ShortExact
    exact pushforwardComplex_shortExact_of_flasque_kernel (nativeProjection.app X).hom hS
      S.X₁.property.2

/-- Original quasi-isomorphisms between these actual flasque complexes remain weak arrows. -/
lemma G0_weak (X : QuasiCompactSchemes.{u})
    {K L : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj} (f : K ⟶ L)
    (hf : (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq f) :
    (FlasqueBoundedBelow.waldhausen X.obj).weq ((G0 X).map f) := by
  change QuasiIso f.hom at hf
  let := hf
  obtain ⟨a, ha⟩ := K.property.1.2
  obtain ⟨b, hb⟩ := L.property.1.2
  let := ha
  let := hb
  exact quasiIso_pushforward_of_flasque (nativeProjection.app X).hom f.hom a b
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE L.obj b n hn)
    K.property.2 L.property.2

/-- Literal ordinary projection is Waldhausen-exact on this original flasque model. -/
lemma G0_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq
    (FlasqueBoundedBelow.waldhausen X.obj).cof
    (FlasqueBoundedBelow.waldhausen X.obj).weq (G0 X) where
  zero h := (G0 X).map_isZero h
  cofibration f hf := (G0ExactFunctor X).map_inflation f hf
  weak f hf := G0_weak X f hf
  pushout hi h := (G0ExactFunctor X).map_isPushout hi h

/-- The exact original G0 functor computes Rp through the actual natural installed unit. -/
def G0DerivedIso (X : QuasiCompactSchemes.{u}) :
    G0 X ⋙ toPlus X.obj ⋙ DerivedCategory.Plus.Q ≅
      toPlus (nativeLineFunctor.obj X).obj ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus
        (nativeProjection.app X).hom :=
  derivedPushforwardIso (nativeProjection.app X).hom

/-- Its original component is precisely the installed derived unit. -/
lemma G0DerivedIso_hom_app (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    (G0DerivedIso X).hom.app K =
      (derivedPushforwardPlusUnit (nativeProjection.app X).hom).app ((toPlus
        (nativeLineFunctor.obj X).obj).obj K) := rfl

/-- Naturality retains the actual original projection maps. -/
@[reassoc]
lemma G0DerivedIso_naturality (X : QuasiCompactSchemes.{u})
    {K L : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj} (f : K ⟶ L) :
    (DerivedCategory.Plus.Q.map ((toPlus X.obj).map ((G0 X).map f))) ≫
        (G0DerivedIso X).hom.app L =
      (G0DerivedIso X).hom.app K ≫
        (derivedPushforwardPlus (nativeProjection.app X).hom).map
          (DerivedCategory.Plus.Q.map ((toPlus (nativeLineFunctor.obj X).obj).map f)) :=
  (G0DerivedIso X).hom.naturality f

/-- The native zero coefficient is literally the original direct-image complex. -/
lemma G0_obj_underlying (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    ((G0 X).obj K).obj =
      ((Scheme.Modules.pushforward (nativeProjection.app X).hom).mapHomologicalComplex
        (.up ℤ)).obj K.obj := rfl

/-- The zero coefficient uses the original ordinary direct-image maps. -/
lemma G0_map_underlying (X : QuasiCompactSchemes.{u})
    {K L : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj} (f : K ⟶ L) :
    ((G0 X).map f).hom =
      ((Scheme.Modules.pushforward (nativeProjection.app X).hom).mapHomologicalComplex
        (.up ℤ)).map f.hom := rfl

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeCoefficients
