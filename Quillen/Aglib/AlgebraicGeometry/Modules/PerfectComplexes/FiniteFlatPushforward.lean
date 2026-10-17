/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Pushforward
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Exact
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Pushforward.Finite
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Finite flat direct image of strict perfect complexes

Under the original local noetherian, finite and flat hypotheses, the literal direct image
preserves strict perfectness, quasi-isomorphisms and inherited exact sequences.
The vector-bundle comparison is unchanged.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace Quillen.PerfectComplexes
variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] [Flat f]

/-- A strict perfect complex with its original terms regarded as coherent sheaves. -/
def strictToCoherentComplex (Y : Scheme.{u}) :
    StrictPerfect Y ⥤ CochainComplex
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves Y) ℤ where
  obj K :=
    { X := fun n ↦ ⟨K.obj.X n, by
        let := K.property.2 n
        exact AlgebraicGeometry.Scheme.Modules.coherent_of_finiteLocallyFree (K.obj.X n)⟩
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
theorem strictPerfect_pushforward {K : CochainComplex Z.Modules ℤ} (hK : strictPerfect Z K) :
    strictPerfect X ((pushforwardComplex f).obj K) := by
  obtain ⟨⟨a, b, hb⟩, hv⟩ := hK
  refine ⟨⟨a, b, fun n hn ↦ (Scheme.Modules.pushforward f).map_isZero (hb n hn)⟩,
    fun n ↦ by
      let := hv n
      exact AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_pushforward f (K.X n)⟩

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
      AlgebraicGeometry.Scheme.Modules.vectorBundlePushforward f ⋙ vectorBundleInclusion X :=
  Functor.fullyFaithfulCancelRight (strictPerfect X).ι
    (Functor.isoWhiskerLeft (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree Z).ι
      (HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pushforward f) (ComplexShape.up ℤ) 0))

/-- Actual quasi-isomorphisms of strict complexes stay quasi-isomorphisms after direct image. -/
theorem strictFiniteFlatPushforward_quasiIso {K L : StrictPerfect Z} (s : K ⟶ L)
    [QuasiIso s.hom] : QuasiIso ((strictFiniteFlatPushforward f).map s).hom := by
  let sc := (strictToCoherentComplex Z).map s
  have : QuasiIso sc :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology sc
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesToModules Z)).mp (by
        change QuasiIso s.hom
        infer_instance)
  have : (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforward
    f).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    (((AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforward
      f).mapHomologicalComplex (.up ℤ)).map sc)
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesToModules X)

/-- Finite flat direct image preserves all inherited strict-perfect conflations. -/
def strictExactFiniteFlatPushforward :
    ExactFunctor (strictExactStructure Z) (strictExactStructure X) where
  toFunctor := strictFiniteFlatPushforward f
  map_conflation S hS := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let ev : StrictPerfect Z ⥤ AlgebraicGeometry.Scheme.Modules.FiniteLocallyFree Z :=
      (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree Z).lift
        ((strictPerfect Z).ι ⋙ HomologicalComplex.eval Z.Modules (.up ℤ) n)
        (fun K ↦ K.property.2 n)
    have h : (AlgebraicGeometry.Scheme.Modules.vectorBundleExactStructure Z).conflation (S.map ev)
      :=
      (HomologicalComplex.shortExact_iff_degreewise_shortExact
        (S.map (strictPerfect Z).ι)).mp hS n
    exact (AlgebraicGeometry.Scheme.Modules.vectorBundlePushforwardExact f).map_conflation (S.map
      ev) h

end Quillen.PerfectComplexes

end

end
