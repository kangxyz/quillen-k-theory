import Quillen.Waldhausen.ExtensionCategory.Product
import Quillen.Waldhausen.Additivity.SplitSequence
import Quillen.Waldhausen.ExtensionCategory.ExactTransport

/-! # The actual split extension functor

Pairs `(A,C)` are sent to `A → C ⨿ A`. This is the actual coproduct in the
extension category of `(0→C)` and `(A→A)`, proved by its universal property.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C]

/-- The literal split cofibration, with quotient/subobject summand order. -/
def split : C × C ⥤ Obj W where
  obj X := ⟨Arrow.mk (coprod.inr : X.1 ⟶ X.2 ⨿ X.1), Additivity.coprod_inr_cof W _ _⟩
  map f := (objects W).homMk (Arrow.homMk f.1 (coprod.map f.2 f.1) (by simp))
  map_id X := by apply ObjectProperty.hom_ext; apply Arrow.hom_ext <;> simp
  map_comp f g := by apply ObjectProperty.hom_ext; apply Arrow.hom_ext <;> simp

/-- The quotient-only summand inside a split extension. -/
def splitInl : CategoryTheory.Prod.snd C C ⋙ zeroEmbedding W ⟶ split W where
  app X := (objects W).homMk (Arrow.homMk (W.isZero.to_ X.1) coprod.inl (W.isZero.eq_of_src _ _))
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact W.isZero.eq_of_src _ _
    · simp [split, zeroEmbedding]

/-- The identity-source summand inside a split extension. -/
def splitInr : CategoryTheory.Prod.fst C C ⋙ identityEmbedding W ⟶ split W where
  app X := (objects W).homMk (Arrow.homMk (𝟙 X.1) coprod.inr (by simp [identityEmbedding, split]))
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> simp [split, identityEmbedding]

/-- The displayed split extension is the genuine coproduct of the two canonical embeddings. -/
def splitCofanIsColimit (X : C × C) :
    IsColimit (BinaryCofan.mk ((splitInl W).app X) ((splitInr W).app X)) := by
  let d {T : Obj W} (a : (zeroEmbedding W).obj X.2 ⟶ T) (b : (identityEmbedding W).obj X.1 ⟶ T) :
      (split W).obj X ⟶ T :=
    (objects W).homMk (Arrow.homMk b.hom.left (coprod.desc a.hom.right b.hom.right) (by
      change b.hom.left ≫ T.obj.hom = coprod.inr ≫ coprod.desc a.hom.right b.hom.right
      rw [coprod.inr_desc]
      have h := b.hom.w
      change b.hom.left ≫ T.obj.hom = (𝟙 X.1) ≫ b.hom.right at h
      simpa only [Category.id_comp] using h))
  refine BinaryCofan.IsColimit.mk _ (fun a b ↦ d a b) ?_ ?_ ?_
  · intro T a b
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact W.isZero.eq_of_src _ _
    · exact coprod.inl_desc _ _
  · intro T a b
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact Category.id_comp _
    · exact coprod.inr_desc _ _
  · intro T a b m hm hn
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · have h := congrArg (fun f ↦ f.hom.left) hn
      change (𝟙 X.1) ≫ m.hom.left = b.hom.left at h
      simpa only [Category.id_comp] using! h
    · apply coprod.hom_ext
      · have h := congrArg (fun f ↦ f.hom.right) hm
        simpa [d, splitInl] using! h
      · have h := congrArg (fun f ↦ f.hom.right) hn
        simpa [d, splitInr] using! h

variable [HasBinaryCoproducts (Obj W)]

/-- The canonical coproduct-to-split identification. -/
def splitCoproductIso (X : C × C) :
    (zeroEmbedding W).obj X.2 ⨿ (identityEmbedding W).obj X.1 ≅ (split W).obj X :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso (splitCofanIsColimit W X)

@[reassoc (attr := simp)] theorem splitCoproductIso_inl (X : C × C) :
    coprod.inl ≫ (splitCoproductIso W X).hom = (splitInl W).app X :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod ((zeroEmbedding W).obj X.2) ((identityEmbedding W).obj X.1))
    (splitCofanIsColimit W X) (Discrete.mk WalkingPair.left)

@[reassoc (attr := simp)] theorem splitCoproductIso_inr (X : C × C) :
    coprod.inr ≫ (splitCoproductIso W X).hom = (splitInr W).app X :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod ((zeroEmbedding W).obj X.2) ((identityEmbedding W).obj X.1))
    (splitCofanIsColimit W X) (Discrete.mk WalkingPair.right)

/-- The actual sum of the canonical embeddings identifies naturally with split extensions. -/
def splitSumIso :
    Additivity.sumFunctor (CategoryTheory.Prod.snd C C ⋙ zeroEmbedding W)
      (CategoryTheory.Prod.fst C C ⋙ identityEmbedding W) ≅ split W :=
  NatIso.ofComponents (splitCoproductIso W) (by
    intro X Y f
    apply coprod.hom_ext
    · simp only [Additivity.sumFunctor, coprod.inl_map_assoc]
      have h := (splitInl W).naturality f
      rw [← splitCoproductIso_inl W X, ← splitCoproductIso_inl W Y] at h
      simpa only [Category.assoc] using! h
    · simp only [Additivity.sumFunctor, coprod.inr_map_assoc]
      have h := (splitInr W).naturality f
      rw [← splitCoproductIso_inr W X, ← splitCoproductIso_inr W Y] at h
      simpa only [Category.assoc] using! h)

/-- The literal split-extension functor is genuinely exact. -/
theorem split_exact : IsExact (productStructure W W).cof (productStructure W W).weq
    (waldhausenStructure W).cof (waldhausenStructure W).weq (split W) :=
  isExact_of_natIso (productStructure W W) (waldhausenStructure W)
    (Additivity.sumFunctor_isExact (productStructure W W) (waldhausenStructure W)
    ((snd_exact W W).comp (zeroEmbedding_exact W))
    ((fst_exact W W).comp (identityEmbedding_exact W))) (splitSumIso W)

/-- The split/source-cofiber composite is the actual sum in the internal sequence. -/
def internalSumSplitIso :
    Additivity.sumFunctor (cofiber W ⋙ zeroEmbedding W) (source W ⋙ identityEmbedding W) ≅
      sourceCofiber W ⋙ split W :=
  Functor.isoWhiskerLeft (sourceCofiber W) (splitSumIso W)

end Quillen.Waldhausen.ExtensionCategory
