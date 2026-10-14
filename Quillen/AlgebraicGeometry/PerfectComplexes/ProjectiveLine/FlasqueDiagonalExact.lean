/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalVertices
public import Quillen.Waldhausen.ExactFunctor

/-! # Exactness of the literal original flasque diagonal endofunctors -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal

/-- The inherited exact structure on the literal original flasque-perfect model. -/
abbrev modelExactStructure (R : CommRingCat.{u}) :=
  ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
    (FlasqueBoundedBelow.objects (twoChartLine R))

instance E_additive (R : CommRingCat.{u}) (v : Vertex) : (E R v).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    exact (raw R v).map_add

instance coefficient_preservesFiniteLimits (R : CommRingCat.{u}) (v : Vertex) :
    PreservesFiniteLimits (coefficient R v) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance coefficient_preservesFiniteColimits (R : CommRingCat.{u}) (v : Vertex) :
    PreservesFiniteColimits (coefficient R v) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- The full model inclusion recovers the literal original raw functor. -/
lemma E_underlying (R : CommRingCat.{u}) (v : Vertex) :
    E R v ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι = raw R v := rfl

/-- Exactness of the actual raw sequence retains its actual totalized flasque kernel. -/
lemma raw_shortExact (R : CommRingCat.{u}) (v : Vertex)
    (S : ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R)))
    (hS : (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact) :
    (S.map (raw R v)).ShortExact := by
  let C := (coefficient R v).mapHomologicalComplex (.up ℤ)
  let T := godementTotal (relativeSquare R)
  simp only [raw, ShortComplex.map_comp]
  have hc : ((S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).map C).ShortExact :=
    hS.map_of_exact C
  have ht : (((S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).map C).map
      T).ShortExact := godementTotal_shortExact hc
  exact pushforwardComplex_shortExact_of_flasque_kernel (relativeSecond R) ht
    (totalCoefficient_flasque R v S.X₁)

/-- Exact coefficients and totalization followed by flasque-kernel section lifting. -/
def EExactFunctor (R : CommRingCat.{u}) (v : Vertex) :
    ExactFunctor (modelExactStructure R) (modelExactStructure R) where
  toFunctor := E R v
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact at hS
    change ((S.map (E R v)).map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact
    simpa only [← ShortComplex.map_comp, E_underlying] using raw_shortExact R v S hS

/-- Each original quotient-bearing model cofibration is preserved. -/
lemma E_cofibration (R : CommRingCat.{u}) (v : Vertex)
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L)
    (hf : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof f) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof ((E R v).map f) :=
  (EExactFunctor R v).map_inflation f hf

/-- Actual direct image of the literal total preserves all lower-bounded quasi-isomorphisms. -/
lemma totalPushforwardPlus_quasiIso {X Y : Scheme.{u}} (p : X ⟶ Y)
    {K L : CochainComplex.Plus X.Modules} (f : K ⟶ L) [QuasiIso f.hom] :
    QuasiIso
      (((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal X).map f.hom)) := by
  let : QuasiIso ((godementTotal X).map f.hom) := godementTotalPlus_map_quasiIso f
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := L.property
  let := ha
  let := hb
  have hz := fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn
  have hw := fun n hn => CochainComplex.isZero_of_isStrictlyGE L.obj b n hn
  let : ((godementTotal X).obj K.obj).IsStrictlyGE a := godementTotal_isStrictlyGE K.obj a hz
  let : ((godementTotal X).obj L.obj).IsStrictlyGE b := godementTotal_isStrictlyGE L.obj b hw
  exact quasiIso_pushforward_of_flasque p ((godementTotal X).map f.hom) a b
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE
      ((godementTotal X).obj K.obj) a n hn)
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE
      ((godementTotal X).obj L.obj) b n hn)
    (godementTotal_isFlasque K.obj a hz) (godementTotal_isFlasque L.obj b hw)

/-- Ordinary second image preserves the actual quasi-isomorphism between the two totals. -/
lemma E_weak (R : CommRingCat.{u}) (v : Vertex)
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L)
    (hf : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq f) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((E R v).map f) := by
  change QuasiIso f.hom at hf
  let := hf
  let fp := (FlasqueCoefficients.toPlus (twoChartLine R)).map f
  let : QuasiIso fp.hom := hf
  let cp := (coefficient R v).mapCochainComplexPlus.map fp
  let : QuasiIso cp.hom := by
    change QuasiIso (((coefficient R v).mapHomologicalComplex (.up ℤ)).map f.hom)
    infer_instance
  exact totalPushforwardPlus_quasiIso (relativeSecond R) cp

/-- Literal original diagonal vertices preserve zero, cofibrations, weak arrows and pushouts. -/
lemma E_exact (R : CommRingCat.{u}) (v : Vertex) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (E R v) where
  zero h := (E R v).map_isZero h
  cofibration f hf := E_cofibration R v f hf
  weak f hf := E_weak R v f hf
  pushout hi h := (EExactFunctor R v).map_isPushout hi h

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
