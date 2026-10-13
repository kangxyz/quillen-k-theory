/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.CompactFundamentalGroupoid
public import Quillen.Topology.Realization.EdgePathPresentation.Attachment
public import Quillen.CategoryTheory.TheoremA.EnrichedBoundaryHEP
public import Quillen.Topology.Realization.Skeleton

/-!
# Actual skeletal attachments and compact path reduction

The simplicial skeletal pushouts are realized and identified with discrete
families of actual geometric simplex-boundary inclusions. This supplies closed
embeddings of stages and, in dimensions at least two, fullness on fundamental
groupoids. The compact-stage theorem applies to the actual realization colimit.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits Topology Convexity
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen

/-- The product of a discrete index space with a space is its constant coproduct. -/
def discreteProductCofan (ι : Type u) (Y : TopCat.{u}) : Cofan (fun _ : ι ↦ Y) :=
  Cofan.mk (TopCat.of ((TopCat.discrete.obj ι) × Y))
    (fun i ↦ TopCat.ofHom ⟨fun y ↦ (i, y), continuous_const.prodMk continuous_id⟩)

/-- Universal property of the explicit discrete-index product. -/
def discreteProductCofanIsColimit (ι : Type u) (Y : TopCat.{u}) :
    IsColimit (discreteProductCofan ι Y) :=
  Cofan.IsColimit.mk _
    (fun s ↦ TopCat.ofHom ⟨fun p ↦ s.inj p.1 p.2,
      continuous_prod_of_discrete_left.mpr (fun i ↦ (s.inj i).hom.continuous)⟩)
    (by intro s i; rfl)
    (by
      intro s m hm
      ext ⟨i, y⟩
      exact ConcreteCategory.congr_hom (hm i) y)

/-- Realization of the categorical coproduct is the explicit discrete product. -/
def realizationCoproductDiscreteProductIso (ι : Type u) (Y : SSet.{u}) :
    |(∐ fun _ : ι ↦ Y)| ≅ TopCat.of ((TopCat.discrete.obj ι) × |Y|) :=
  (isColimitCofanMkObjOfIsColimit SSet.toTop (fun _ : ι ↦ Y)
    (Sigma.ι (fun _ : ι ↦ Y)) (coproductIsCoproduct _)).coconePointUniqueUpToIso
      (discreteProductCofanIsColimit ι |Y|)

@[reassoc (attr := simp)]
theorem realizationCoproductDiscreteProductIso_ι (ι : Type u) (Y : SSet.{u}) (i : ι) :
    SSet.toTop.map (Sigma.ι (fun _ : ι ↦ Y) i) ≫
        (realizationCoproductDiscreteProductIso ι Y).hom =
      (discreteProductCofan ι |Y|).inj i :=
  (isColimitCofanMkObjOfIsColimit SSet.toTop (fun _ : ι ↦ Y)
    (Sigma.ι (fun _ : ι ↦ Y)) (coproductIsCoproduct _)).comp_coconePointUniqueUpToIso_hom
      (discreteProductCofanIsColimit ι |Y|) ⟨i⟩

section RelativeSkeleton

variable {A X : SSet.{u}} (i : A ⟶ X) (n : ℕ)

/-- The discrete indexing space of nondegenerate cells attached at stage `n`. -/
abbrev skeletalCellIndex : TopCat.{u} :=
  TopCat.discrete.obj (SSet.relativeCellComplexOfMono.Cell i n)

/-- Actual realized categorical simplex coproduct in geometric coordinates. -/
def realizedSkeletalCellsIso :
    |SSet.relativeCellComplexOfMono.sigmaStdSimplex i n| ≅
      TopCat.of (skeletalCellIndex i n × StdSimplex ℝ (Fin (n + 1))) :=
  realizationCoproductDiscreteProductIso _ (Δ[n] : SSet.{u}) ≪≫
    TopCat.isoOfHomeo ((Homeomorph.refl _).prodCongr (SimplexCategory.toTopHomeo ⦋n⦌))

/-- Actual realized categorical boundary coproduct in geometric coordinates. -/
def realizedSkeletalBoundariesIso :
    |SSet.relativeCellComplexOfMono.sigmaBoundary i n| ≅
      TopCat.of (skeletalCellIndex i n × simplexBoundary n) :=
  realizationCoproductDiscreteProductIso _ (∂Δ[n] : SSet.{u}) ≪≫
    TopCat.isoOfHomeo ((Homeomorph.refl _).prodCongr (realizationBoundaryHomeomorph n))

@[reassoc (attr := simp)]
theorem realizedSkeletalCellsIso_ι (a : SSet.relativeCellComplexOfMono.Cell i n) :
    SSet.toTop.map a.ιSigmaStdSimplex ≫ (realizedSkeletalCellsIso i n).hom =
      TopCat.ofHom (Y := TopCat.of (skeletalCellIndex i n × StdSimplex ℝ (Fin (n + 1))))
        ⟨fun x ↦ (a, SimplexCategory.toTopHomeo ⦋n⦌ x), by fun_prop⟩ := by
  dsimp only [realizedSkeletalCellsIso, Iso.trans_hom]
  rw [← Category.assoc, realizationCoproductDiscreteProductIso_ι]
  rfl

@[reassoc (attr := simp)]
theorem realizedSkeletalBoundariesIso_ι (a : SSet.relativeCellComplexOfMono.Cell i n) :
    SSet.toTop.map a.ιSigmaBoundary ≫ (realizedSkeletalBoundariesIso i n).hom =
      TopCat.ofHom (Y := TopCat.of (skeletalCellIndex i n × simplexBoundary n))
        ⟨fun x ↦ (a, realizationBoundaryHomeomorph n x), by fun_prop⟩ := by
  dsimp only [realizedSkeletalBoundariesIso, Iso.trans_hom]
  rw [← Category.assoc, realizationCoproductDiscreteProductIso_ι]
  rfl

/-- Realizing the categorical coproduct of boundary maps gives the genuine
parameterized geometric boundary inclusion under these isomorphisms. -/
theorem realizedSkeletalBoundary_square :
    SSet.toTop.map (SSet.relativeCellComplexOfMono.l i n) ≫
        (realizedSkeletalCellsIso i n).hom =
      (realizedSkeletalBoundariesIso i n).hom ≫
        Quillen.parameterizedSimplexBoundaryInclusion (skeletalCellIndex i n) n := by
  apply (isColimitCofanMkObjOfIsColimit SSet.toTop
    (fun _ : SSet.relativeCellComplexOfMono.Cell i n ↦ (∂Δ[n] : SSet.{u}))
    (Sigma.ι _) (coproductIsCoproduct _)).hom_ext
  intro ⟨a⟩
  change SSet.toTop.map a.ιSigmaBoundary ≫ _ = SSet.toTop.map a.ιSigmaBoundary ≫ _
  rw [← Category.assoc, ← SSet.toTop.map_comp, a.ι_l, SSet.toTop.map_comp,
    Category.assoc, realizedSkeletalCellsIso_ι, realizedSkeletalBoundariesIso_ι_assoc]
  rfl

/-- The attaching map on actual geometric boundaries. -/
def realizedSkeletalAttaching :
    TopCat.of (skeletalCellIndex i n × simplexBoundary n) ⟶
      |(SSet.skeletonOfMono i n : SSet.{u})| :=
  (realizedSkeletalBoundariesIso i n).inv ≫
    SSet.toTop.map (SSet.relativeCellComplexOfMono.t i n)

/-- The characteristic map on actual geometric simplices. -/
def realizedSkeletalCharacteristic :
    TopCat.of (skeletalCellIndex i n × StdSimplex ℝ (Fin (n + 1))) ⟶
      |(SSet.skeletonOfMono i (n + 1) : SSet.{u})| :=
  (realizedSkeletalCellsIso i n).inv ≫
    SSet.toTop.map (SSet.relativeCellComplexOfMono.b i n)

/-- The actual geometric cell-attachment pushout for a simplicial skeleton. -/
theorem realizedSkeletal_isPushout :
    IsPushout (Quillen.parameterizedSimplexBoundaryInclusion (skeletalCellIndex i n) n)
      (realizedSkeletalAttaching i n) (realizedSkeletalCharacteristic i n)
      (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)) := by
  apply ((SSet.relativeCellComplexOfMono.isPushout i n).flip.map SSet.toTop).of_iso
    (realizedSkeletalBoundariesIso i n) (realizedSkeletalCellsIso i n)
    (Iso.refl _) (Iso.refl _)
  · exact realizedSkeletalBoundary_square i n
  · simp [realizedSkeletalAttaching]
  · simp [realizedSkeletalCharacteristic]
  · simp

/-- Realization of every successor inclusion is a closed embedding. -/
theorem realizedSkeletal_transition_isClosedEmbedding :
    IsClosedEmbedding (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)) :=
  simplexAttachment_old_isClosedEmbedding (skeletalCellIndex i n) n
    (realizedSkeletal_isPushout i n)

/-- Cells of dimension at least two add no path generators to a skeleton. -/
theorem realizedSkeletal_transition_fundamentalGroupoid_full (hn : 2 ≤ n) :
    (FundamentalGroupoid.map
      (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)).hom).Full :=
  simplexAttachment_fundamentalGroupoid_full (skeletalCellIndex i n) n
    (realizedSkeletal_isPushout i n) hn

end RelativeSkeleton

/-- The actual relative simplicial skeleton tower after realization. -/
def realizedRelativeSkeletonTower {A X : SSet.{u}} (i : A ⟶ X) [Mono i] : ℕ ⥤ TopCat.{u} :=
  (SSet.relativeCellComplexOfMono i).F ⋙ SSet.toTop

/-- The canonical cocone of the actual relative realization tower. -/
def realizedRelativeSkeletonCocone {A X : SSet.{u}} (i : A ⟶ X) [Mono i] :
    Cocone (realizedRelativeSkeletonTower i) :=
  SSet.toTop.mapCocone { pt := X, ι := (SSet.relativeCellComplexOfMono i).incl }

/-- Realization preserves the exhaustive simplicial skeletal colimit. -/
def realizedRelativeSkeletonIsColimit {A X : SSet.{u}} (i : A ⟶ X) [Mono i] :
    IsColimit (realizedRelativeSkeletonCocone i) :=
  isColimitOfPreserves SSet.toTop (SSet.relativeCellComplexOfMono i).isColimit

/-- Successor maps of the actual relative tower are closed embeddings. -/
theorem realizedRelativeSkeleton_closedEmbeddings {A X : SSet.{u}} (i : A ⟶ X)
    [Mono i] (n : ℕ) :
    IsClosedEmbedding ((realizedRelativeSkeletonTower i).map (homOfLE (Nat.le_succ n))) :=
  realizedSkeletal_transition_isClosedEmbedding i n

/-- Every relative stage is T₁ whenever the original subspace is T₁. -/
instance realizedRelativeSkeleton_t1Space {A X : SSet.{u}} (i : A ⟶ X)
    [Mono i] [T1Space |A|] (n : ℕ) : T1Space ((realizedRelativeSkeletonTower i).obj n) := by
  induction n with
  | zero =>
    exact (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.relativeCellComplexOfMono
      i).isoBot)).symm.t1Space
  | succ n ih =>
    let : T1Space |(SSet.skeletonOfMono i n : SSet.{u})| := ih
    exact t1Space_pushout_of_closedEmbedding (realizedSkeletal_isPushout i n)
      (isClosedEmbedding_parameterizedSimplexBoundary (skeletalCellIndex i n) n)

/-- Realization of the empty subcomplex is empty. -/
instance realization_bot_isEmpty (X : SSet.{u}) :
    IsEmpty |((⊥ : X.Subcomplex) : SSet.{u})| := ⟨by
  intro x
  obtain ⟨m, f, t, ht⟩ := realization_exists_simplex x
  exact (SSet.yonedaEquiv f).2⟩

/-- The skeletal tower starting at the empty subcomplex. Stage `n` contains
exactly the simplices of dimension strictly less than `n`. -/
abbrev realizedSkeletonTower (X : SSet.{u}) : ℕ ⥤ TopCat.{u} :=
  realizedRelativeSkeletonTower ((⊥ : X.Subcomplex).ι)

/-- The ordinary skeletal cocone to the actual realization. -/
abbrev realizedSkeletonCocone (X : SSet.{u}) : Cocone (realizedSkeletonTower X) :=
  realizedRelativeSkeletonCocone ((⊥ : X.Subcomplex).ι)

/-- The actual realization is the colimit of its skeletal tower. -/
abbrev realizedSkeletonIsColimit (X : SSet.{u}) : IsColimit (realizedSkeletonCocone X) :=
  realizedRelativeSkeletonIsColimit ((⊥ : X.Subcomplex).ι)

/-- Identification of each chosen stage with the ordinary simplicial skeleton. -/
def realizedSkeletonStageIso (X : SSet.{u}) (n : ℕ) :
    (realizedSkeletonTower X).obj n ≅ |(X.skeleton n : SSet.{u})| :=
  SSet.toTop.mapIso (SSet.Subcomplex.eqToIso (skeletonOfMono_bot X n))

/-- Every compact subset of the actual realization lies in a finite skeleton. -/
theorem realization_isCompact_subset_stage (X : SSet.{u}) {K : Set |X|} (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range ((realizedSkeletonCocone X).ι.app n) :=
  RealizationCompactStages.isCompact_subset_stageRange_of_closedEmbeddings
    (realizedSkeletonIsColimit X) (realizedRelativeSkeleton_closedEmbeddings _) hK

/-- Every map from a compact space into the actual realization factors through
a finite stage of its actual skeletal tower. -/
theorem realization_continuousMap_factors {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (X : SSet.{u}) (f : C(Y, |X|)) :
    ∃ n, ∃ g : C(Y, (realizedSkeletonTower X).obj n),
      ∀ y, (realizedSkeletonCocone X).ι.app n (g y) = f y :=
  RealizationCompactStages.continuousMap_factors
    (realizedSkeletonIsColimit X) (realizedRelativeSkeleton_closedEmbeddings _) f

@[reassoc (attr := simp)]
theorem realizedSkeletonStageIso_hom_ι (X : SSet.{u}) (n : ℕ) :
    (realizedSkeletonStageIso X n).hom ≫ SSet.toTop.map (X.skeleton n).ι =
      (realizedSkeletonCocone X).ι.app n := by
  change SSet.toTop.map (SSet.Subcomplex.eqToIso (skeletonOfMono_bot X n)).hom ≫
    SSet.toTop.map (X.skeleton n).ι = SSet.toTop.map _
  rw [← SSet.toTop.map_comp]
  congr 1

/-- The actual realization of every simplicial set is T₁. -/
instance realization_t1Space (X : SSet.{u}) : T1Space |X| :=
  RealizationCompactStages.t1Space_colimit (realizedSkeletonIsColimit X)
    (realizedRelativeSkeleton_closedEmbeddings _)

/-- The inclusion of any stage containing all edges is full on fundamental
groupoids in the actual realization. -/
theorem realizedSkeleton_fundamentalGroupoid_full (X : SSet.{u}) (k : ℕ) (hk : 2 ≤ k) :
    (FundamentalGroupoid.map ((realizedSkeletonCocone X).ι.app k).hom).Full :=
  RealizationCompactStages.stage_fundamentalGroupoid_full (realizedSkeletonIsColimit X)
    (realizedRelativeSkeleton_closedEmbeddings _) k
    (fun n hn ↦ realizedSkeletal_transition_fundamentalGroupoid_full _ n (hk.trans hn))

/-- In particular every path between points of the one-dimensional skeleton
is represented up to endpoint-fixed homotopy by a path in that skeleton. -/
theorem realizedSkeleton_path_homotopic_from_stage (X : SSet.{u}) (k : ℕ) (hk : 2 ≤ k)
    {x y : (realizedSkeletonTower X).obj k}
    (p : Path ((realizedSkeletonCocone X).ι.app k x) ((realizedSkeletonCocone X).ι.app k y)) :
    ∃ q : Path x y,
      (q.map ((realizedSkeletonCocone X).ι.app k).hom.continuous).Homotopic p :=
  RealizationCompactStages.path_homotopic_from_stage (realizedSkeletonIsColimit X)
    (realizedRelativeSkeleton_closedEmbeddings _) k
    (fun n hn ↦ realizedSkeletal_transition_fundamentalGroupoid_full _ n (hk.trans hn)) p

/-- The standard one-dimensional skeleton, expressed directly as `X.skeleton 2`,
is full on fundamental groupoids after realization. -/
theorem realization_skeleton_fundamentalGroupoid_full (X : SSet.{u}) (k : ℕ) (hk : 2 ≤ k) :
    (FundamentalGroupoid.map (SSet.toTop.map (X.skeleton k).ι).hom).Full := by
  let e := realizedSkeletonStageIso X k
  have heq : SSet.toTop.map (X.skeleton k).ι =
      e.inv ≫ (realizedSkeletonCocone X).ι.app k := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact realizedSkeletonStageIso_hom_ι X k
  rw [heq]
  change (FundamentalGroupoid.map
    (((realizedSkeletonCocone X).ι.app k).hom.comp e.inv.hom)).Full
  rw [FundamentalGroupoid.map_comp]
  let := realizedSkeleton_fundamentalGroupoid_full X k hk
  have : (FundamentalGroupoid.map e.inv.hom).IsEquivalence :=
    (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
      (TopCat.homeoOfIso e.symm).toHomotopyEquiv).isEquivalence_functor
  infer_instance

/-- Every ordinary skeletal inclusion is a closed embedding in the actual
realization, with its actual subspace topology. -/
theorem realization_skeleton_isClosedEmbedding (X : SSet.{u}) (n : ℕ) :
    IsClosedEmbedding (SSet.toTop.map (X.skeleton n).ι) := by
  let e := realizedSkeletonStageIso X n
  have heq : SSet.toTop.map (X.skeleton n).ι =
      e.inv ≫ (realizedSkeletonCocone X).ι.app n := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact realizedSkeletonStageIso_hom_ι X n
  rw [heq]
  exact (RealizationCompactStages.stage_isClosedEmbedding (realizedSkeletonIsColimit X)
    (realizedRelativeSkeleton_closedEmbeddings _) n).comp
      (TopCat.homeoOfIso e.symm).isClosedEmbedding

/-- Compact containment expressed in terms of the ordinary simplicial skeleton. -/
theorem realization_isCompact_subset_skeleton (X : SSet.{u}) {K : Set |X|} (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range (SSet.toTop.map (X.skeleton n).ι) := by
  obtain ⟨n, hn⟩ := realization_isCompact_subset_stage X hK
  refine ⟨n, ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := hn hx
  exact ⟨(realizedSkeletonStageIso X n).hom y,
    ConcreteCategory.congr_hom (realizedSkeletonStageIso_hom_ι X n) y⟩

/-- Compact-source factorization through an ordinary finite skeleton. -/
theorem realization_continuousMap_factors_skeleton
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] (X : SSet.{u}) (f : C(Y, |X|)) :
    ∃ n, ∃ g : C(Y, |(X.skeleton n : SSet.{u})|),
      ∀ y, SSet.toTop.map (X.skeleton n).ι (g y) = f y := by
  obtain ⟨n, g, hg⟩ := realization_continuousMap_factors X f
  refine ⟨n, (realizedSkeletonStageIso X n).hom.hom.comp g, ?_⟩
  intro y
  exact (ConcreteCategory.congr_hom (realizedSkeletonStageIso_hom_ι X n) (g y)).trans (hg y)

/-- Every path with endpoints in the ordinary one-dimensional skeleton is
homotopic relative endpoints to a path in that skeleton. -/
theorem realization_skeleton_path_homotopic (X : SSet.{u}) (k : ℕ) (hk : 2 ≤ k)
    {x y : |(X.skeleton k : SSet.{u})|}
    (p : Path (SSet.toTop.map (X.skeleton k).ι x) (SSet.toTop.map (X.skeleton k).ι y)) :
    ∃ q : Path x y, (q.map (SSet.toTop.map (X.skeleton k).ι).hom.continuous).Homotopic p := by
  let := realization_skeleton_fundamentalGroupoid_full X k hk
  let F := FundamentalGroupoid.map (SSet.toTop.map (X.skeleton k).ι).hom
  obtain ⟨q, hq⟩ := F.map_surjective
    (X := FundamentalGroupoid.mk x) (Y := FundamentalGroupoid.mk y) ⟦p⟧
  obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  exact ⟨q, Path.Homotopic.Quotient.eq.mp hq⟩

end Quillen
