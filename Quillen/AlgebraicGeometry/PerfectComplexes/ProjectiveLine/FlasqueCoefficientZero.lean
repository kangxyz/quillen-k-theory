/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Plus


public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlasqueBoundedBelow
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.IntrinsicPerfectPushforward
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.PushforwardExactness
public import Aglib.AlgebraicGeometry.Cohomology.Godement.DerivedPushforward.Total
public import Quillen.Waldhausen.ExactFunctor
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect

/-!
# The original exact zero coefficient on the flasque perfect model

Ordinary direct image is exact on the inherited sequences because their actual
kernel complex has flasque terms. Its natural installed derived unit and the
intrinsic projective-line pushforward theorem prove perfection of the values.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients

attribute [local instance] standardDerived

/-- The underlying zero coefficient is the literal original degreewise direct image. -/
def G0Raw (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex (Spec R).Modules ℤ :=
  (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
    (Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)

instance G0Raw_additive (R : CommRingCat.{u}) : (G0Raw R).Additive := by
  unfold G0Raw
  infer_instance

/-- The installed natural unit and intrinsic P2 theorem give actual local perfection. -/
lemma G0_locallyPerfect (R : CommRingCat.{u}) (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    locallyPerfect (Spec R) ((G0Raw R).obj K) := by
  let P := (toPlus (twoChartLine R)).obj K
  have hP : perfectDerivedObjects (twoChartLine R)
      (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj P)) :=
    (perfectDerivedObjects_toDerived_iff (twoChartLine R) K.obj).mpr K.property.1.1
  have hRp := perfect_derivedProjection_of_perfect R (DerivedCategory.Plus.Q.obj P) hP
  apply (perfectDerivedObjects_toDerived_iff (Spec R) ((G0Raw R).obj K)).mp
  exact (perfectDerivedObjects (Spec R)).prop_of_iso
    (DerivedCategory.Plus.ι.mapIso ((derivedPushforwardIso (projection R)).app K).symm) hRp

/-- Ordinary direct image retains each specified strict lower bound. -/
lemma G0Raw_isStrictlyGE (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((G0Raw R).obj K).IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (Scheme.Modules.pushforward (projection R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

/-- The actual ordinary direct image has flasque terms and remains in the original model. -/
lemma G0_objects (R : CommRingCat.{u}) (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    FlasqueBoundedBelow.objects (Spec R) ((G0Raw R).obj K) := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  refine ⟨⟨G0_locallyPerfect R K, a, G0Raw_isStrictlyGE R K a⟩, fun n => ?_⟩
  let : TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf := K.property.2 n
  change TopCat.Presheaf.IsFlasque
    ((Scheme.Modules.pushforward (projection R)).obj (K.obj.X n)).presheaf
  infer_instance

/-- The actual zero coefficient, with values in the full original flasque-perfect category. -/
def G0 (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ FlasqueBoundedBelow.Obj (Spec R) :=
  ObjectProperty.lift _ (G0Raw R) (G0_objects R)

instance G0_additive (R : CommRingCat.{u}) : (G0 R).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (G0Raw R).map (f + g) = (G0Raw R).map f + (G0Raw R).map g
    exact CategoryTheory.Functor.map_add (G0Raw R)

/-- Exactness uses the proved original flasque-kernel section lifts. -/
def G0ExactFunctor (R : CommRingCat.{u}) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex (twoChartLine R).Modules ℤ))
      (FlasqueBoundedBelow.objects (twoChartLine R)))
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex (Spec R).Modules ℤ))
      (FlasqueBoundedBelow.objects (Spec R))) where
  toFunctor := G0 R
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact at hS
    change ((S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).map
      ((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ))).ShortExact
    exact pushforwardComplex_shortExact_of_flasque_kernel (projection R) hS
      S.X₁.property.2

/-- Original quasi-isomorphisms between these actual flasque complexes remain weak arrows. -/
lemma G0_weak (R : CommRingCat.{u})
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L)
    (hf : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq f) :
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq ((G0 R).map f) := by
  change QuasiIso f.hom at hf
  let := hf
  obtain ⟨a, ha⟩ := K.property.1.2
  obtain ⟨b, hb⟩ := L.property.1.2
  let := ha
  let := hb
  exact quasiIso_pushforward_of_flasque (projection R) f.hom a b
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE L.obj b n hn)
    K.property.2 L.property.2

/-- Literal ordinary projection is Waldhausen-exact on this original flasque model. -/
lemma G0_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (G0 R) where
  zero h := (G0 R).map_isZero h
  cofibration f hf := (G0ExactFunctor R).map_inflation f hf
  weak f hf := G0_weak R f hf
  pushout hi h := (G0ExactFunctor R).map_isPushout hi h

/-- The exact original G0 functor computes Rp through the actual natural installed unit. -/
def G0DerivedIso (R : CommRingCat.{u}) :
    G0 R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q ≅
      toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (projection R) :=
  derivedPushforwardIso (projection R)

/-- Its original component is precisely the installed derived unit. -/
lemma G0DerivedIso_hom_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (G0DerivedIso R).hom.app K =
      (derivedPushforwardPlusUnit (projection R)).app ((toPlus (twoChartLine R)).obj K) := rfl

/-- Naturality retains the actual original projection maps. -/
@[reassoc]
lemma G0DerivedIso_naturality (R : CommRingCat.{u})
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    (DerivedCategory.Plus.Q.map ((toPlus (Spec R)).map ((G0 R).map f))) ≫
        (G0DerivedIso R).hom.app L =
      (G0DerivedIso R).hom.app K ≫
        (derivedPushforwardPlus (projection R)).map
          (DerivedCategory.Plus.Q.map ((toPlus (twoChartLine R)).map f)) :=
  (G0DerivedIso R).hom.naturality f

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
