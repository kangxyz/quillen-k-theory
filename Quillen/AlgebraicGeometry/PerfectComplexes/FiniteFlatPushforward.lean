/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ComplexPushforward
public import Quillen.AlgebraicGeometry.PerfectComplexes.VectorBundleInclusion
public import Quillen.Waldhausen.ExactFunctor
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.FinitePushforward

/-! # Finite flat direct image of strict perfect complexes

The original termwise direct image preserves bounded finite locally free terms.
Exact coherent direct image proves preservation of actual quasi-isomorphisms,
and exact vector-bundle direct image proves preservation of all inherited
conflations and cofibration pushouts. The degree-zero vector-bundle inclusion
commutes with this actual functor. No direct image of arbitrary locally perfect
representatives is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace Quillen.PerfectComplexes
variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] [Flat f]

/-- A strict perfect complex with its original terms regarded as coherent sheaves. -/
def strictToCoherentComplex (Y : Scheme.{u}) :
    StrictPerfect Y ⥤ CochainComplex (CoherentScheme.FiniteTypeSheaves Y) ℤ where
  obj K :=
    { X := fun n ↦ ⟨K.obj.X n, by
        let := K.property.2 n
        exact SchemeSheaf.coherent_of_finiteLocallyFree (K.obj.X n)⟩
      d := fun i j ↦ ObjectProperty.homMk (K.obj.d i j)
      shape := fun i j hij ↦ by
        apply ObjectProperty.hom_ext
        exact K.obj.shape i j hij
      d_comp_d' := fun i j k _ _ ↦ by
        apply ObjectProperty.hom_ext
        exact K.obj.d_comp_d i j k }
  map s :=
    { f := fun i ↦ ObjectProperty.homMk (s.hom.f i)
      comm' := fun i j _ ↦ by
        apply ObjectProperty.hom_ext
        exact s.hom.comm i j }

omit [IsLocallyNoetherian Z] in
/-- The actual termwise direct image preserves strict perfectness. -/
theorem strictPerfect_pushforward {K : Complex Z} (hK : strictPerfect Z K) :
    strictPerfect X ((pushforwardComplex f).obj K) := by
  obtain ⟨⟨a, b, hb⟩, hv⟩ := hK
  refine ⟨⟨a, b, fun n hn ↦ (Scheme.Modules.pushforward f).map_isZero (hb n hn)⟩,
    fun n ↦ by
      let := hv n
      exact SchemeSheaf.finiteLocallyFree_pushforward f (K.X n)⟩

/-- Actual direct image restricted to bounded vector-bundle complexes. -/
def strictFiniteFlatPushforward : StrictPerfect Z ⥤ StrictPerfect X :=
  (strictPerfect X).lift ((strictPerfect Z).ι ⋙ pushforwardComplex f)
    (fun K ↦ strictPerfect_pushforward f K.property)

instance strictFiniteFlatPushforward_additive : (strictFiniteFlatPushforward f).Additive := by
  unfold strictFiniteFlatPushforward pushforwardComplex
  infer_instance

/-- The original degree-zero inclusion commutes with finite flat direct image. -/
def vectorBundleInclusionFiniteFlatPushforwardIso :
    vectorBundleInclusion Z ⋙ strictFiniteFlatPushforward f ≅
      SchemeSheaf.vectorBundlePushforward f ⋙ vectorBundleInclusion X :=
  Functor.fullyFaithfulCancelRight (strictPerfect X).ι
    (Functor.isoWhiskerLeft (SchemeSheaf.finiteLocallyFree Z).ι
      (HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pushforward f) (ComplexShape.up ℤ) 0))

/-- Actual quasi-isomorphisms of strict complexes stay quasi-isomorphisms after direct image. -/
theorem strictFiniteFlatPushforward_quasiIso {K L : StrictPerfect Z} (s : K ⟶ L)
    [QuasiIso s.hom] : QuasiIso ((strictFiniteFlatPushforward f).map s).hom := by
  let sc := (strictToCoherentComplex Z).map s
  have : QuasiIso sc :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology sc
      (CoherentScheme.finiteTypeSheavesToModules Z)).mp (by
        change QuasiIso s.hom
        infer_instance)
  have : (CoherentScheme.Finite.coherentPushforward f).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    (((CoherentScheme.Finite.coherentPushforward f).mapHomologicalComplex (.up ℤ)).map sc)
    (CoherentScheme.finiteTypeSheavesToModules X)

/-- Finite flat direct image preserves all inherited strict-perfect conflations. -/
def strictExactFiniteFlatPushforward :
    ExactFunctor (strictExactStructure Z) (strictExactStructure X) where
  toFunctor := strictFiniteFlatPushforward f
  map_conflation S hS := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let ev : StrictPerfect Z ⥤ SchemeSheaf.FiniteLocallyFree Z :=
      (SchemeSheaf.finiteLocallyFree Z).lift
        ((strictPerfect Z).ι ⋙ HomologicalComplex.eval Z.Modules (.up ℤ) n)
        (fun K ↦ K.property.2 n)
    have h : (SchemeSheaf.vectorBundleExactStructure Z).conflation (S.map ev) :=
      (HomologicalComplex.shortExact_iff_degreewise_shortExact
        (S.map (strictPerfect Z).ι)).mp hS n
    exact (SchemeSheaf.vectorBundlePushforwardExact f).map_conflation (S.map ev) h

/-- Actual direct image preserves cofibrations, their pushouts, and quasi-isomorphisms. -/
theorem strictFiniteFlatPushforward_waldhausenExact :
    Waldhausen.IsExact (strictWaldhausen Z).cof (strictWaldhausen Z).weq
      (strictWaldhausen X).cof (strictWaldhausen X).weq (strictFiniteFlatPushforward f) where
  zero h := (strictFiniteFlatPushforward f).map_isZero h
  cofibration s hs := (strictExactFiniteFlatPushforward f).map_inflation s hs
  weak s hs := by
    let : QuasiIso s.hom := hs
    exact strictFiniteFlatPushforward_quasiIso f s
  pushout hi h := (strictExactFiniteFlatPushforward f).waldhausenExact.pushout hi h

/-- The genuine strict-perfect Waldhausen K-map induced by finite flat direct image. -/
def strictKFiniteFlatPushforward (n : ℕ) : StrictK Z n →* StrictK X n :=
  Waldhausen.KMap (strictFiniteFlatPushforward_waldhausenExact f) n

end Quillen.PerfectComplexes
