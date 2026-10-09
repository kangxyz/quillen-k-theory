import Quillen.CategoryTheory.TheoremA.Augmentations
import Quillen.Topology.Realization.Opposite

/-! Opposite-chain presentation of the source columns. -/

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.TheoremA

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

private theorem chainMap_heq {n : ℕ} (c : ComposableArrows C n)
    {i j i' j' : Fin (n + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : c.map f ≍ c.map g := by
  subst i'; subst j'
  exact heq_of_eq (congrArg c.map (Subsingleton.elim f g))

private theorem chainMap_op_heq {n : ℕ} (c : ComposableArrows C n)
    {i j i' j' : Fin (n + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : (c.map f).op ≍ (c.map g).op := by
  subst i'; subst j'
  exact heq_of_eq (congrArg (fun f ↦ (c.map f).op) (Subsingleton.elim f g))

/-- Reverse a chain while passing to the opposite category. -/
def reverseChain {n : ℕ} (c : ComposableArrows C n) : ComposableArrows Cᵒᵖ n where
  obj i := op (c.obj i.rev)
  map {i j} f := (c.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom f)))).op
  map_id i := by simp
  map_comp f g := by
    change (c.map _).op = (c.map _ ≫ c.map _).op
    rw [← c.map_comp]
    rfl

/-- Read a reversed opposite chain in its original direction. -/
def unreverseChain {n : ℕ} (c : ComposableArrows Cᵒᵖ n) : ComposableArrows C n where
  obj i := (c.obj i.rev).unop
  map {i j} f := (c.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom f)))).unop
  map_id i := by simp
  map_comp f g := by
    change (c.map _).unop = (c.map _ ≫ c.map _).unop
    rw [← c.map_comp]
    rfl

@[simp] theorem unreverse_reverseChain {n : ℕ} (c : ComposableArrows C n) :
    unreverseChain (reverseChain c) = c := by
  refine CategoryTheory.Functor.hext (fun i ↦ by simp [reverseChain, unreverseChain]) ?_
  intro i j f
  exact chainMap_heq c (Fin.rev_rev i) (Fin.rev_rev j) _ _

@[simp] theorem reverse_unreverseChain {n : ℕ} (c : ComposableArrows Cᵒᵖ n) :
    reverseChain (unreverseChain c) = c := by
  refine CategoryTheory.Functor.hext (fun i ↦ by simp [reverseChain, unreverseChain]) ?_
  intro i j f
  exact chainMap_heq c (Fin.rev_rev i) (Fin.rev_rev j) _ _

/-- Reversal is a bijection on chains, including their actual objects and arrows. -/
def reverseChainEquiv (n : ℕ) : ComposableArrows C n ≃ ComposableArrows Cᵒᵖ n where
  toFun := reverseChain
  invFun := unreverseChain
  left_inv := unreverse_reverseChain
  right_inv := reverse_unreverseChain

/-- Reversal intertwines the two simplicial operators. -/
theorem reverseChain_naturality {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q)
    (c : (nerve C).obj p) :
    reverseChain ((nerve C).map (SimplexCategory.rev.map α.unop).op c) =
      (nerve Cᵒᵖ).map α (reverseChain c) := by
  refine CategoryTheory.Functor.hext (fun i ↦ ?_) ?_
  · change op (c.obj (α.unop.toOrderHom i.rev.rev).rev) =
      op (c.obj (α.unop.toOrderHom i).rev)
    simp
  · intro i j f
    change (c.map (homOfLE (show (α.unop.toOrderHom j.rev.rev).rev ≤
      (α.unop.toOrderHom i.rev.rev).rev from by
        simpa using Fin.rev_le_rev.mpr (α.unop.toOrderHom.monotone (leOfHom f))))).op ≍
        (c.map (homOfLE (show (α.unop.toOrderHom j).rev ≤
          (α.unop.toOrderHom i).rev from
            Fin.rev_le_rev.mpr (α.unop.toOrderHom.monotone (leOfHom f))))).op
    exact chainMap_op_heq c (by simp) (by simp) _ _

/-- The nerve of the opposite category is the reversed nerve. -/
def nerveOppositeIso : (nerve C).op ≅ nerve Cᵒᵖ :=
  NatIso.ofComponents (fun p ↦ (reverseChainEquiv p.unop.len).toIso) (by
    intro p q α
    ext c : 3
    exact reverseChain_naturality α c)

/-- Under categories vary covariantly with the opposite source category. -/
def sourceUnderDiagram (F : C ⥤ D) : Cᵒᵖ ⥤ Cat.{u, u} where
  obj c := Cat.of (StructuredArrow (F.obj c.unop) (𝟭 D))
  map f := (StructuredArrow.map (F.map f.unop)).toCatHom
  map_id c := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun X ↦ ?_) ?_
    · simp only [unop_id, F.map_id]
      exact StructuredArrow.map_id
    · intro X Y f
      apply StructuredArrow.hom_ext
      simp
  map_comp f g := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun X ↦ ?_) ?_
    · simp only [unop_comp, F.map_comp]
      exact StructuredArrow.map_comp
    · intro X Y h
      apply StructuredArrow.hom_ext
      simp

/-- The covariant nerve-valued diagram used for the source augmentation. -/
def sourceUnderNerveDiagram (F : C ⥤ D) : Cᵒᵖ ⥤ SSet.{u} :=
  sourceUnderDiagram F ⋙ nerveFunctor

/-- Reindex the under-category summands by reversed chains. -/
def sourceUnderColumnEquiv (F : C ⥤ D) (q p : SimplexCategoryᵒᵖ) :
    (commaColumnSummands F q).obj p ≃
      (replacementRow (sourceUnderNerveDiagram F) q).obj p :=
  Equiv.sigmaCongr (reverseChainEquiv q.unop.len) (fun _ ↦ Equiv.refl _)

/-- The decomposition with opposite chains respects the inner simplicial maps. -/
def sourceUnderColumnIso (F : C ⥤ D) (q : SimplexCategoryᵒᵖ) :
    commaColumnSummands F q ≅ replacementRow (sourceUnderNerveDiagram F) q :=
  NatIso.ofComponents (fun p ↦ (sourceUnderColumnEquiv F q p).toIso) (by
    intro p r α
    ext x : 3
    rfl)

/-- Reversing the outer simplex direction turns the source columns into
an ordinary covariant first-vertex simplicial replacement. -/
def sourceColumnsOppositeIso (F : C ⥤ D) :
    SimplexCategory.rev.op ⋙ (simplicialReplacement (commaNerveDiagram F)).flip ≅
      simplicialReplacement (sourceUnderNerveDiagram F) :=
  NatIso.ofComponents (fun q ↦ commaColumnIso F q ≪≫ sourceUnderColumnIso F q) (by
    intro q r α
    ext p x : 4
    dsimp [commaColumnIso, sourceUnderColumnIso, sourceUnderColumnEquiv,
      commaColumnSimplexEquiv, reverseChainEquiv, simplicialReplacement,
      replacementRowMap, sourceUnderNerveDiagram, sourceUnderDiagram,
      commaChainEquiv, structuredChainEquiv]
    apply Sigma.ext
    · exact reverseChain_naturality (C := C) α (x.2 ⋙ CostructuredArrow.proj F (x.1.obj 0))
    · change structuredChainOfFirst (𝟭 D) x.1
        (x.2.obj ((SimplexCategory.rev.map α.unop).toOrderHom
          (Fin.last r.unop.len))).hom ≍
        structuredChainOfFirst (𝟭 D) x.1 (x.2.obj (Fin.last q.unop.len)).hom ⋙
          StructuredArrow.map (F.map ((x.2.map (homOfLE
            (Fin.le_last (α.unop.toOrderHom 0).rev))).left))
      have hindex : (SimplexCategory.rev.map α.unop).toOrderHom
          (Fin.last r.unop.len) = (α.unop.toOrderHom 0).rev := by simp
      rw [hindex]
      apply heq_of_eq
      refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
      · refine StructuredArrow.obj_ext _ _ rfl ?_
        dsimp [structuredChainOfFirst]
        simpa only [Category.comp_id, Category.assoc] using
          congrArg (fun h ↦ h ≫ x.1.map (homOfLE (Fin.zero_le i)))
            (CostructuredArrow.w
              (x.2.map (homOfLE (Fin.le_last (α.unop.toOrderHom 0).rev)))).symm
      · intro i j f
        apply StructuredArrow.hom_ext
        simp [structuredChainOfFirst])

/-- On the base, the same reversal is precisely the nerve-opposite isomorphism. -/
def sourceBaseOppositeIso :
    SimplexCategory.rev.op ⋙
      ((Functor.const SimplexCategoryᵒᵖ).obj (nerve C)).flip ≅
      baseBisimplicial Cᵒᵖ :=
  Functor.isoWhiskerRight nerveOppositeIso (Functor.const SimplexCategoryᵒᵖ)

/-- The opposite-column presentation preserves the actual source augmentation. -/
theorem sourceColumnsOppositeIso_augmentation (F : C ⥤ D) :
    Functor.whiskerLeft SimplexCategory.rev.op
        ((CategoryTheory.flipFunctor _ _ _).map (sourceAugmentation F)) ≫
      sourceBaseOppositeIso.hom =
    (sourceColumnsOppositeIso F).hom ≫ targetAugmentation (sourceUnderNerveDiagram F) := by
  ext p q : 4
  rfl

/-- Every value of the source-column diagram is contractible by its initial object. -/
theorem sourceUnderNerveDiagram_contractible (F : C ⥤ D) (c : Cᵒᵖ) :
    ContractibleSpace |(sourceUnderNerveDiagram F).obj c| :=
  classifyingSpace_contractible_of_isInitial
    (StructuredArrow.mkIdInitial (T := 𝟭 D) (Y := F.obj c.unop))

end Quillen.TheoremA
