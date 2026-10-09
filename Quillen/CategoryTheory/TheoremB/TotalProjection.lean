import Quillen.CategoryTheory.TheoremB.CartesianProducts
import Quillen.CategoryTheory.TheoremA.IteratedRealization
import Quillen.CategoryTheory.TheoremA.Augmentations

/-!
# The actual total replacement projection

The coend realization of the displayed topological replacement is compared
homeomorphically with the actual diagonal realization. The corresponding
base coend is homeomorphic to the ordinary nerve realization. These
homeomorphisms identify the total projection with the canonical map of
simplicial sets, including its direction and all simplex maps.
-/

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremB

/-- A topological coproduct of points is the discrete index space. -/
def sigmaPointHomeomorph (A : Type u) :
    (Σ _a : A, |(Δ[0] : SSet.{u})|) ≃ₜ TopCat.discrete.obj A where
  toFun := Sigma.fst
  invFun a := ⟨a, default⟩
  left_inv := by
    rintro ⟨a, x⟩
    exact congrArg (Sigma.mk a) (Subsingleton.elim _ _)
  right_inv a := rfl
  continuous_toFun := continuous_sigma fun _ ↦ continuous_const
  continuous_invFun := continuous_of_discreteTopology

/-- Realization of a constant simplicial set is its discrete space of
values, with the genuine geometric-realization topology. -/
def constantRealizationIso (A : Type u) :
    SSet.toTop.obj ((Functor.const SimplexCategoryᵒᵖ).obj A) ≅ TopCat.discrete.obj A :=
  (SSet.toTop.mapIso (TheoremA.pointSigmaIso A)).symm ≪≫
    TheoremA.realizationSigmaIso (fun _ : A ↦ (Δ[0] : SSet.{u})) ≪≫
      TopCat.isoOfHomeo (sigmaPointHomeomorph A)

/-- Each point-simplex summand realizes to its index under the comparison. -/
@[reassoc (attr := simp)]
theorem constantRealizationIso_ι (A : Type u) (a : A) :
    SSet.toTop.map (TheoremA.simplicialSigmaι (fun _ : A ↦ (Δ[0] : SSet.{u})) a ≫
      (TheoremA.pointSigmaIso A).hom) ≫ (constantRealizationIso A).hom =
      TopCat.ofHom (ContinuousMap.const |(Δ[0] : SSet.{u})| (show TopCat.discrete.obj A from a)) := by
  simp only [Functor.map_comp, constantRealizationIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [← Category.assoc (SSet.toTop.map (TheoremA.pointSigmaIso A).hom),
    ← Functor.map_comp]
  simp only [Iso.hom_inv_id]
  rw [SSet.toTop.map_id, Category.id_comp, TheoremA.realizationSigmaIso_ι_assoc]
  rfl

/-- The discrete realization homeomorphisms respect arbitrary index maps. -/
theorem constantRealizationIso_naturality {A B : Type u} (f : A ⟶ B) :
    SSet.toTop.map ((Functor.const SimplexCategoryᵒᵖ).map f) ≫ (constantRealizationIso B).hom =
      (constantRealizationIso A).hom ≫ TopCat.discrete.map f := by
  apply (cancel_epi (SSet.toTop.map (TheoremA.pointSigmaIso A).hom)).mp
  apply (TheoremA.realizedSigmaIsColimit (fun _ : A ↦ (Δ[0] : SSet.{u}))).hom_ext
  intro ⟨a⟩
  dsimp
  have heq : TheoremA.simplicialSigmaι (fun _ : A ↦ (Δ[0] : SSet.{u})) a ≫
      (TheoremA.pointSigmaIso A).hom ≫ (Functor.const SimplexCategoryᵒᵖ).map f =
    TheoremA.simplicialSigmaι (fun _ : B ↦ (Δ[0] : SSet.{u})) (f a) ≫
      (TheoremA.pointSigmaIso B).hom := rfl
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [Category.assoc (TheoremA.simplicialSigmaι _ a), heq]
  simp only [constantRealizationIso_ι]
  rfl

/-- Iterated topological realization is a functor, with the already defined
canonical coend map. -/
def topologicalRealizationFunctor : (SimplexCategoryᵒᵖ ⥤ TopCat.{u}) ⥤ TopCat.{u} where
  obj := TheoremA.iteratedRealization
  map := TheoremA.iteratedRealizationMap
  map_id Y := by
    change coend.map (TheoremA.iteratedRealizationBifunctorMap (𝟙 Y)) = _
    have hi : TheoremA.iteratedRealizationBifunctorMap (𝟙 Y) = 𝟙 _ := by
      ext p q
      simp [TheoremA.iteratedRealizationBifunctorMap]
      rfl
    rw [hi, coend.map_id]
    rfl
  map_comp η θ := by
    change coend.map (TheoremA.iteratedRealizationBifunctorMap (η ≫ θ)) = _
    have hc : TheoremA.iteratedRealizationBifunctorMap (η ≫ θ) =
        TheoremA.iteratedRealizationBifunctorMap η ≫
          TheoremA.iteratedRealizationBifunctorMap θ := by
      ext p q
      simp [TheoremA.iteratedRealizationBifunctorMap]
      rfl
    rw [hc]
    exact (coend.map_comp _ _).symm

/-- The actual realized rows of the base bisimplicial set form precisely
the simplicial discrete space of base chains. -/
def baseRowsRealizationIso (D : Type u) [SmallCategory D] :
    TheoremA.baseBisimplicial D ⋙ SSet.toTop ≅ nerve D ⋙ TopCat.discrete :=
  NatIso.ofComponents (fun p ↦ constantRealizationIso ((nerve D).obj p))
    (fun α ↦ constantRealizationIso_naturality ((nerve D).map α))

/-- The coend realization of the discrete nerve is homeomorphic to its
ordinary simplicial realization. -/
def baseTotalRealizationIso (D : Type u) [SmallCategory D] :
    TheoremA.iteratedRealization (nerve D ⋙ TopCat.discrete) ≅ ClassifyingSpace D :=
  (topologicalRealizationFunctor.mapIso (baseRowsRealizationIso D)).symm ≪≫
    (TheoremA.diagonalIteratedRealizationIso (TheoremA.baseBisimplicial D)).symm ≪≫
      SSet.toTop.mapIso (TheoremA.diagonalBaseIso D)

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The topological replacement's coend is homeomorphic to the actual
realization of its simplicial diagonal. -/
def replacementTotalRealizationIso :
    |TheoremA.replacementDiagonal H| ≅ TheoremA.iteratedRealization (topologicalReplacement H) :=
  TheoremA.diagonalIteratedRealizationIso (TheoremA.simplicialReplacement H) ≪≫
    topologicalRealizationFunctor.mapIso (topologicalReplacementIso H)

/-- In every actual row, the realized target augmentation is the displayed
coproduct projection under the two canonical homeomorphisms. -/
theorem targetAugmentation_row_projection (p : SimplexCategoryᵒᵖ) :
    SSet.toTop.map ((TheoremA.targetAugmentation H).app p) ≫
        (constantRealizationIso ((nerve D).obj p)).hom =
      (TheoremA.replacementRowRealizationIso H p).hom ≫
        (topologicalReplacementProjection H).app p := by
  apply (TheoremA.realizedSigmaIsColimit
    (fun s : (nerve D).obj p ↦ H.obj (s.obj 0))).hom_ext
  intro ⟨s⟩
  dsimp
  have heq : TheoremA.simplicialSigmaι
      (fun s : (nerve D).obj p ↦ H.obj (s.obj 0)) s ≫
        (TheoremA.targetAugmentation H).app p =
      SSet.stdSimplex.isTerminalObj₀.from (H.obj (s.obj 0)) ≫
        (TheoremA.simplicialSigmaι (fun _ : (nerve D).obj p ↦ (Δ[0] : SSet.{u})) s ≫
          (TheoremA.pointSigmaIso ((nerve D).obj p)).hom) := rfl
  rw [← Functor.map_comp_assoc]
  erw [heq]
  rw [Functor.map_comp_assoc]
  erw [constantRealizationIso_ι]
  change _ = SSet.toTop.map (TheoremA.simplicialSigmaι _ s) ≫
    (TheoremA.realizationSigmaIso _).hom ≫ (topologicalReplacementProjection H).app p
  rw [TheoremA.realizationSigmaIso_ι_assoc]
  rfl

/-- The row projection identification is an equality of simplicial maps. -/
theorem targetAugmentation_realization_projection :
    Functor.whiskerRight (TheoremA.targetAugmentation H) SSet.toTop ≫
        (baseRowsRealizationIso D).hom =
      (topologicalReplacementIso H).hom ≫ topologicalReplacementProjection H := by
  apply NatTrans.ext
  funext p
  exact targetAugmentation_row_projection H p

/-- The topological coend projection is exactly the realized canonical
simplicial projection after the source and target homeomorphisms. -/
theorem replacementTotalRealizationIso_projection :
    (replacementTotalRealizationIso H).hom ≫
        TheoremA.iteratedRealizationMap (topologicalReplacementProjection H) ≫
          (baseTotalRealizationIso D).hom =
      SSet.toTop.map (TheoremA.replacementBaseMap H) := by
  let R := topologicalRealizationFunctor
  have hn := TheoremA.diagonalIteratedRealizationIso_naturality (TheoremA.targetAugmentation H)
  change SSet.toTop.map (TheoremA.diagonalMap (TheoremA.targetAugmentation H)) ≫
      (TheoremA.diagonalIteratedRealizationIso (TheoremA.baseBisimplicial D)).hom =
    (TheoremA.diagonalIteratedRealizationIso (TheoremA.simplicialReplacement H)).hom ≫
      R.map (Functor.whiskerRight (TheoremA.targetAugmentation H) SSet.toTop) at hn
  change ((TheoremA.diagonalIteratedRealizationIso (TheoremA.simplicialReplacement H)).hom ≫
    R.map (topologicalReplacementIso H).hom) ≫
    R.map (topologicalReplacementProjection H) ≫
      (R.map (baseRowsRealizationIso D).inv ≫
        (TheoremA.diagonalIteratedRealizationIso (TheoremA.baseBisimplicial D)).inv ≫
          SSet.toTop.map (TheoremA.diagonalBaseIso D).hom) = _
  simp only [Category.assoc]
  rw [← R.map_comp_assoc, ← targetAugmentation_realization_projection]
  rw [R.map_comp_assoc]
  rw [← R.map_comp_assoc (baseRowsRealizationIso D).hom (baseRowsRealizationIso D).inv]
  rw [Iso.hom_inv_id, R.map_id, Category.id_comp]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, TheoremA.targetAugmentation_diagonal]

end Quillen.TheoremB
