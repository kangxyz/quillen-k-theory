/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremB.Rows
public import Quillen.Topology.HELP.Basic
public import Quillen.Topology.Realization.SubfamilyHEP
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Cofibrant degeneracies in the simplicial replacement

Outer degeneracies of the actual realized replacement rows are open and
closed embeddings. In coproduct coordinates they include entire summands,
with a homeomorphism on each included summand.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremB

/-- Reindexing coproducts along an injection, with homeomorphisms on the
fibers, is an open embedding. -/
theorem sigmaReindexContinuousMap_isOpenEmbedding
    {ι κ : Type u} {X : ι → Type u} {Y : κ → Type u}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (a : ι → κ) (f : ∀ i, C(X i, Y (a i))) (ha : Function.Injective a)
    (hf : ∀ i, Topology.IsOpenEmbedding (f i)) :
    Topology.IsOpenEmbedding (sigmaReindexContinuousMap a f) :=
  (Topology.isOpenEmbedding_sigmaMap ha).2 hf

/-- With surjective fiber maps, the range consists exactly of the selected
base-index summands. -/
theorem sigmaReindexContinuousMap_range
    {ι κ : Type u} {X : ι → Type u} {Y : κ → Type u}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (a : ι → κ) (f : ∀ i, C(X i, Y (a i)))
    (hf : ∀ i, Function.Surjective (f i)) :
    Set.range (sigmaReindexContinuousMap a f) = Sigma.fst ⁻¹' Set.range a := by
  ext ⟨j, y⟩
  constructor
  · rintro ⟨⟨i, x⟩, h⟩
    exact ⟨i, congrArg Sigma.fst h⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨x, rfl⟩ := hf i y
    exact ⟨⟨i, x⟩, rfl⟩

/-- Any collection of summands of a topological coproduct is closed. -/
theorem sigma_index_preimage_isClosed
    {κ : Type u} {Y : κ → Type u} [∀ j, TopologicalSpace (Y j)] (S : Set κ) :
    IsClosed (Sigma.fst ⁻¹' S : Set (Σ j, Y j)) := by
  apply isClosed_sigma_iff.mpr
  intro j
  by_cases hj : j ∈ S
  · simp [Set.preimage, hj]
  · simp [Set.preimage, hj]

/-- Reindexing with injective indices and homeomorphic fibers is a closed
embedding as well. -/
theorem sigmaReindexContinuousMap_isClosedEmbedding
    {ι κ : Type u} {X : ι → Type u} {Y : κ → Type u}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (a : ι → κ) (f : ∀ i, C(X i, Y (a i))) (ha : Function.Injective a)
    (hf : ∀ i, Topology.IsEmbedding (f i))
    (hs : ∀ i, Function.Surjective (f i)) :
    Topology.IsClosedEmbedding (sigmaReindexContinuousMap a f) := by
  refine ⟨(Topology.isEmbedding_sigmaMap ha).2 hf, ?_⟩
  rw [sigmaReindexContinuousMap_range a f hs]
  exact sigma_index_preimage_isClosed _

/-- Reindexing by an injection with homeomorphic fibers is a homeomorphism
onto the corresponding subfamily of target summands. -/
def sigmaReindexRangeHomeomorph
    {ι κ : Type u} {X : ι → Type u} {Y : κ → Type u}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (a : ι → κ) (e : ∀ i, X i ≃ₜ Y (a i)) (ha : Function.Injective a) :
    (Σ i, X i) ≃ₜ (Σ j : Set.range a, Y j.1) := by
  let f : C((Σ i, X i), Σ j : Set.range a, Y j.1) :=
    sigmaReindexContinuousMap (fun i ↦ (⟨a i, ⟨i, rfl⟩⟩ : Set.range a))
      (fun i ↦ (e i : C(X i, Y (a i))))
  have hf : Topology.IsOpenEmbedding f :=
    sigmaReindexContinuousMap_isOpenEmbedding _ _
      (fun i j h ↦ ha (congrArg Subtype.val h)) (fun i ↦ (e i).isOpenEmbedding)
  apply hf.isEmbedding.toHomeomorphOfSurjective
  rintro ⟨⟨j, ⟨i, rfl⟩⟩, y⟩
  obtain ⟨x, rfl⟩ := (e i).surjective y
  exact ⟨⟨i, x⟩, rfl⟩

/-- Injective reindexing by homeomorphic fibers has genuine homotopy
extension, by factoring as a homeomorphism and a subfamily inclusion. -/
theorem sigmaReindexContinuousMap_homotopyExtensionProperty
    {ι κ : Type u} {X : ι → Type u} {Y : κ → Type u}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (a : ι → κ) (e : ∀ i, X i ≃ₜ Y (a i)) (ha : Function.Injective a) :
    Quillen.homotopyExtensionProperty
      (TopCat.ofHom (sigmaReindexContinuousMap a (fun i ↦ (e i : C(X i, Y (a i)))))) := by
  let E : TopCat.of (Σ i, X i) ≅ TopCat.of (Σ j : Set.range a, Y j.1) :=
    TopCat.isoOfHomeo (sigmaReindexRangeHomeomorph a e ha)
  have hfac : TopCat.ofHom (sigmaReindexContinuousMap a
      (fun i ↦ (e i : C(X i, Y (a i))))) =
      E.hom ≫ TopCat.ofHom (Quillen.sigmaSubfamilyInclusion (X := Y) (Set.range a)) := rfl
  rw [hfac]
  apply Quillen.homotopyExtensionProperty_comp
    (Quillen.homotopyExtensionProperty_of_isIso E.hom)
  exact Quillen.homotopyExtensionProperty_of_continuous _ fun _ f K hzero ↦
    Quillen.sigmaSubfamily_homotopyExtension (Set.range a) f K hzero

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- Degeneracies are split injections on the base chains. -/
theorem nerve_degeneracy_injective {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective ((nerve D).map (SimplexCategory.σ i).op) := by
  apply Function.LeftInverse.injective
    (g := (nerve D).map (SimplexCategory.δ i.castSucc).op)
  intro s
  change ((nerve D).map (SimplexCategory.σ i).op ≫
    (nerve D).map (SimplexCategory.δ i.castSucc).op) s = s
  rw [← Functor.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id,
    (nerve D).map_id]
  rfl

/-- A degeneracy preserves the initial vertex, hence its fiber transition
is an isomorphism (the identity under the canonical object equality). -/
theorem firstVertexEdge_degeneracy_isIso {n : ℕ} (i : Fin (n + 1))
    (s : (nerve D).obj (op ⦋n⦌)) :
    IsIso (TheoremA.firstVertexEdge (SimplexCategory.σ i).op s) := by
  change IsIso (s.map (homOfLE (Fin.zero_le (i.predAbove 0))))
  change IsIso (s.map (𝟙 (0 : Fin (n + 1))))
  rw [s.map_id]
  infer_instance

/-- Each component of an outer degeneracy is an actual homeomorphism. -/
def degeneracyFiberHomeomorph {n : ℕ} (i : Fin (n + 1))
    (s : (nerve D).obj (op ⦋n⦌)) :
    |H.obj (s.obj 0)| ≃ₜ
      |H.obj (((nerve D).map (SimplexCategory.σ i).op s).obj 0)| := by
  letI := firstVertexEdge_degeneracy_isIso (D := D) i s
  exact TopCat.homeoOfIso
    (asIso (SSet.toTop.map (H.map (TheoremA.firstVertexEdge (SimplexCategory.σ i).op s))))

@[simp]
theorem degeneracyFiberHomeomorph_apply {n : ℕ} (i : Fin (n + 1))
    (s : (nerve D).obj (op ⦋n⦌)) (x : |H.obj (s.obj 0)|) :
    degeneracyFiberHomeomorph H i s x =
      SSet.toTop.map (H.map (TheoremA.firstVertexEdge (SimplexCategory.σ i).op s)) x := rfl

/-- Outer degeneracies are open embeddings in the topological replacement. -/
theorem topologicalRowMap_degeneracy_isOpenEmbedding {n : ℕ} (i : Fin (n + 1)) :
    Topology.IsOpenEmbedding (topologicalRowMap H (SimplexCategory.σ i).op) :=
  sigmaReindexContinuousMap_isOpenEmbedding _ _ (nerve_degeneracy_injective i)
    (fun s ↦ (degeneracyFiberHomeomorph H i s).isOpenEmbedding)

/-- Outer degeneracies are closed embeddings in the topological replacement. -/
theorem topologicalRowMap_degeneracy_isClosedEmbedding {n : ℕ} (i : Fin (n + 1)) :
    Topology.IsClosedEmbedding (topologicalRowMap H (SimplexCategory.σ i).op) :=
  sigmaReindexContinuousMap_isClosedEmbedding _ _ (nerve_degeneracy_injective i)
    (fun s ↦ (degeneracyFiberHomeomorph H i s).isEmbedding)
    (fun s ↦ (degeneracyFiberHomeomorph H i s).surjective)

/-- A degeneracy includes every point of every selected base summand. -/
theorem topologicalRowMap_degeneracy_range {n : ℕ} (i : Fin (n + 1)) :
    Set.range (topologicalRowMap H (SimplexCategory.σ i).op) =
      Sigma.fst ⁻¹' Set.range ((nerve D).map (SimplexCategory.σ i).op) :=
  sigmaReindexContinuousMap_range _ _
    (fun s ↦ (degeneracyFiberHomeomorph H i s).surjective)

/-- The coordinate homeomorphisms give an exact conjugation formula for the
actual realization map, suitable for transferring topological properties. -/
theorem replacementRowMap_realization_eq {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    SSet.toTop.map (TheoremA.replacementRowMap H α) =
      (TheoremA.replacementRowRealizationIso H p).hom ≫
        TopCat.ofHom (topologicalRowMap H α) ≫
          (TheoremA.replacementRowRealizationIso H q).inv := by
  rw [← Category.assoc, ← replacementRowRealizationIso_naturality]
  simp

/-- The genuine realized row degeneracy is an open embedding. -/
theorem replacementRowMap_degeneracy_realization_isOpenEmbedding
    {n : ℕ} (i : Fin (n + 1)) :
    Topology.IsOpenEmbedding
      (SSet.toTop.map (TheoremA.replacementRowMap H (SimplexCategory.σ i).op)) := by
  rw [replacementRowMap_realization_eq]
  exact (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso H _).symm).isOpenEmbedding.comp
    ((topologicalRowMap_degeneracy_isOpenEmbedding H i).comp
      (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso H _)).isOpenEmbedding)

/-- The genuine realized row degeneracy is a closed embedding. -/
theorem replacementRowMap_degeneracy_realization_isClosedEmbedding
    {n : ℕ} (i : Fin (n + 1)) :
    Topology.IsClosedEmbedding
      (SSet.toTop.map (TheoremA.replacementRowMap H (SimplexCategory.σ i).op)) := by
  rw [replacementRowMap_realization_eq]
  exact (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso H _).symm).isClosedEmbedding.comp
    ((topologicalRowMap_degeneracy_isClosedEmbedding H i).comp
      (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso H _)).isClosedEmbedding)

/-- Every outer degeneracy satisfies homotopy extension in the genuine
coproduct coordinates. -/
theorem topologicalRowMap_degeneracy_homotopyExtensionProperty
    {n : ℕ} (i : Fin (n + 1)) :
    Quillen.homotopyExtensionProperty
      (TopCat.ofHom (topologicalRowMap H (SimplexCategory.σ i).op)) :=
  sigmaReindexContinuousMap_homotopyExtensionProperty
    (X := fun s : (nerve D).obj (op ⦋n⦌) ↦ |H.obj (s.obj 0)|)
    (Y := fun s : (nerve D).obj (op ⦋n + 1⦌) ↦ |H.obj (s.obj 0)|)
    ((nerve D).map (SimplexCategory.σ i).op)
    (degeneracyFiberHomeomorph H i) (nerve_degeneracy_injective (D := D) i)

/-- Every actual realized row degeneracy satisfies homotopy extension. -/
theorem replacementRowMap_degeneracy_realization_homotopyExtensionProperty
    {n : ℕ} (i : Fin (n + 1)) :
    Quillen.homotopyExtensionProperty
      (SSet.toTop.map (TheoremA.replacementRowMap H (SimplexCategory.σ i).op)) := by
  rw [replacementRowMap_realization_eq]
  exact Quillen.homotopyExtensionProperty_comp
    (Quillen.homotopyExtensionProperty_of_isIso _)
    (Quillen.homotopyExtensionProperty_comp
      (topologicalRowMap_degeneracy_homotopyExtensionProperty H i)
      (Quillen.homotopyExtensionProperty_of_isIso _))

/-- The degenerate part of a replacement row consists of all fiber summands
over degenerate base chains. -/
def degenerateReplacementRow (n : ℕ) : SSet.{u} :=
  Quillen.Realization.simplicialSigma
    (fun s : (nerve D).degenerate n ↦ H.obj (s.1.obj 0))

/-- Canonical inclusion of the whole degenerate part into the row. -/
def degenerateReplacementRowInclusion (n : ℕ) :
    degenerateReplacementRow H n ⟶ TheoremA.replacementRow H (op ⦋n⦌) :=
  Quillen.Realization.simplicialSubfamilyInclusion
    (fun s : (nerve D).obj (op ⦋n⦌) ↦ H.obj (s.obj 0)) ((nerve D).degenerate n)

/-- The same inclusion in topological coproduct coordinates. -/
def topologicalDegenerateRowInclusion (n : ℕ) :
    C((Σ s : (nerve D).degenerate n, |H.obj (s.1.obj 0)|),
      Σ s : (nerve D).obj (op ⦋n⦌), |H.obj (s.obj 0)|) :=
  Quillen.sigmaSubfamilyInclusion
    (X := fun s : (nerve D).obj (op ⦋n⦌) ↦ |H.obj (s.obj 0)|) ((nerve D).degenerate n)

/-- The range of the degenerate-row inclusion is exactly the collection of
summands indexed by degenerate base chains. -/
theorem topologicalDegenerateRowInclusion_range (n : ℕ) :
    Set.range (topologicalDegenerateRowInclusion H n) =
      Sigma.fst ⁻¹' (nerve D).degenerate n := by
  ext ⟨s, x⟩
  constructor
  · rintro ⟨⟨⟨s', hs'⟩, x'⟩, h⟩
    have hs : s' = s := congrArg Sigma.fst h
    simpa [hs] using hs'
  · intro hs
    exact ⟨⟨⟨s, hs⟩, x⟩, rfl⟩

/-- The whole degenerate row is exactly the union of the images of the
actual outer degeneracies, with no condition imposed on the fibers. -/
theorem topologicalDegenerateRowInclusion_range_eq_union (n : ℕ) :
    Set.range (topologicalDegenerateRowInclusion H (n + 1)) =
      ⋃ i : Fin (n + 1), Set.range (topologicalRowMap H (SimplexCategory.σ i).op) := by
  rw [topologicalDegenerateRowInclusion_range,
    (nerve D).degenerate_eq_iUnion_range_σ, Set.preimage_iUnion]
  congr 1
  funext i
  exact (topologicalRowMap_degeneracy_range H i).symm

/-- The inclusion of the whole degenerate row is an open embedding. -/
theorem topologicalDegenerateRowInclusion_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (topologicalDegenerateRowInclusion H n) :=
  sigmaReindexContinuousMap_isOpenEmbedding
    (X := fun s : (nerve D).degenerate n ↦ |H.obj (s.1.obj 0)|)
    (Y := fun s : (nerve D).obj (op ⦋n⦌) ↦ |H.obj (s.obj 0)|)
    Subtype.val (fun _ ↦ ContinuousMap.id _) Subtype.val_injective
    (fun _ ↦ (Homeomorph.refl _).isOpenEmbedding)

/-- The inclusion of the whole degenerate row is a closed embedding. -/
theorem topologicalDegenerateRowInclusion_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (topologicalDegenerateRowInclusion H n) := by
  refine ⟨(topologicalDegenerateRowInclusion_isOpenEmbedding H n).isEmbedding, ?_⟩
  rw [topologicalDegenerateRowInclusion_range]
  exact sigma_index_preimage_isClosed _

/-- The whole degenerate-row inclusion satisfies categorical homotopy
extension in genuine coproduct topologies. -/
theorem topologicalDegenerateRowInclusion_homotopyExtensionProperty (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (topologicalDegenerateRowInclusion H n)) :=
  Quillen.homotopyExtensionProperty_of_continuous _ fun _ f K hzero ↦
    Quillen.sigmaSubfamily_homotopyExtension ((nerve D).degenerate n) f K hzero

/-- The canonical inclusion into the actual realized row has homotopy
extension against every target space. -/
theorem degenerateReplacementRowInclusion_realization_homotopyExtensionProperty (n : ℕ) :
    Quillen.homotopyExtensionProperty
      (SSet.toTop.map (degenerateReplacementRowInclusion H n)) :=
  Quillen.Realization.homotopyExtensionProperty_realizationSubfamily
    (fun s : (nerve D).obj (op ⦋n⦌) ↦ H.obj (s.obj 0)) ((nerve D).degenerate n)

/-- Realizing the degenerate inclusion gives the canonical subfamily
inclusion under the proved row homeomorphisms. -/
theorem degenerateReplacementRowInclusion_realization_eq (n : ℕ) :
    SSet.toTop.map (degenerateReplacementRowInclusion H n) =
      (Quillen.Realization.realizationSigmaIso
        (fun s : (nerve D).degenerate n ↦ H.obj (s.1.obj 0))).hom ≫
      TopCat.ofHom (topologicalDegenerateRowInclusion H n) ≫
      (TheoremA.replacementRowRealizationIso H (op ⦋n⦌)).inv := by
  have h := Quillen.Realization.realizationSubfamilyInclusion_naturality
    (fun s : (nerve D).obj (op ⦋n⦌) ↦ H.obj (s.obj 0)) ((nerve D).degenerate n)
  change SSet.toTop.map (degenerateReplacementRowInclusion H n) ≫
      (TheoremA.replacementRowRealizationIso H (op ⦋n⦌)).hom =
      (Quillen.Realization.realizationSigmaIso
        (fun s : (nerve D).degenerate n ↦ H.obj (s.1.obj 0))).hom ≫
      TopCat.ofHom (topologicalDegenerateRowInclusion H n) at h
  rw [← Category.assoc, ← h]
  simp

/-- The entire degenerate part is an open subspace of the actual realized row. -/
theorem degenerateReplacementRowInclusion_realization_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (SSet.toTop.map (degenerateReplacementRowInclusion H n)) := by
  rw [degenerateReplacementRowInclusion_realization_eq]
  exact (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso H _).symm).isOpenEmbedding.comp
    ((topologicalDegenerateRowInclusion_isOpenEmbedding H n).comp
      (TopCat.homeoOfIso (Quillen.Realization.realizationSigmaIso _)).isOpenEmbedding)

/-- The entire degenerate part is a closed subspace of the actual realized row. -/
theorem degenerateReplacementRowInclusion_realization_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (SSet.toTop.map (degenerateReplacementRowInclusion H n)) := by
  rw [degenerateReplacementRowInclusion_realization_eq]
  exact (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso H _).symm).isClosedEmbedding.comp
    ((topologicalDegenerateRowInclusion_isClosedEmbedding H n).comp
      (TopCat.homeoOfIso (Quillen.Realization.realizationSigmaIso _)).isClosedEmbedding)

/-- A commuting change of coordinates transports ranges by preimage. -/
theorem range_eq_preimage_of_homeomorphs
    {A B A' B' : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace A'] [TopologicalSpace B']
    (e : A ≃ₜ A') (e' : B ≃ₜ B') (f : A → B) (g : A' → B')
    (h : ∀ a, e' (f a) = g (e a)) :
    Set.range f = e' ⁻¹' Set.range g := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e a, (h a).symm⟩
  · rintro ⟨a, ha⟩
    refine ⟨e.symm a, e'.injective ?_⟩
    rw [h, e.apply_symm_apply]
    exact ha

/-- The range of any actual realized row operator in coproduct coordinates. -/
theorem replacementRowMap_realization_range {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    Set.range (SSet.toTop.map (TheoremA.replacementRowMap H α)) =
      (TheoremA.replacementRowRealizationIso H q).hom ⁻¹'
        Set.range (topologicalRowMap H α) :=
  range_eq_preimage_of_homeomorphs
    (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso H p))
    (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso H q)) _ _
    (fun x ↦ ConcreteCategory.congr_hom (replacementRowRealizationIso_naturality H α) x)

/-- The actual realization of the degenerate subfamily selects precisely
the degenerate summands in coproduct coordinates. -/
theorem degenerateReplacementRowInclusion_realization_range (n : ℕ) :
    Set.range (SSet.toTop.map (degenerateReplacementRowInclusion H n)) =
      (TheoremA.replacementRowRealizationIso H (op ⦋n⦌)).hom ⁻¹'
        Set.range (topologicalDegenerateRowInclusion H n) :=
  range_eq_preimage_of_homeomorphs
    (TopCat.homeoOfIso (Quillen.Realization.realizationSigmaIso
      (fun s : (nerve D).degenerate n ↦ H.obj (s.1.obj 0))))
    (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso H (op ⦋n⦌))) _ _
    (fun x ↦ Quillen.Realization.realizationSubfamilyInclusion_apply
      (fun s : (nerve D).obj (op ⦋n⦌) ↦ H.obj (s.obj 0)) ((nerve D).degenerate n) x)

/-- In the actual realized row, the degenerate subspace is exactly the union
of all realized degeneracy images. Its HEP and closed embedding above are
therefore properties of this genuine union. -/
theorem degenerateReplacementRowInclusion_realization_range_eq_union (n : ℕ) :
    Set.range (SSet.toTop.map (degenerateReplacementRowInclusion H (n + 1))) =
      ⋃ i : Fin (n + 1),
        Set.range (SSet.toTop.map (TheoremA.replacementRowMap H (SimplexCategory.σ i).op)) := by
  rw [degenerateReplacementRowInclusion_realization_range,
    topologicalDegenerateRowInclusion_range_eq_union, Set.preimage_iUnion]
  congr 1
  funext i
  exact (replacementRowMap_realization_range H (SimplexCategory.σ i).op).symm

end Quillen.TheoremB
