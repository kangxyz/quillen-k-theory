/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.KTheory.Bass.PolynomialLaurent
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
Bass contraction as the actual categorical cokernel of the polynomial chart difference. Includes
naturality, exactness, the literal Laurent quotient presentation, representatives, the exact
two-chart kernel criterion and unique descent. No spectrum comparison is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Bass

/-- The actual two polynomial charts map to the Laurent group by their difference. -/
def polynomialDifference (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u}) :
    F.obj (polynomialFunctor.obj R) ⊞ F.obj (polynomialFunctor.obj R) ⟶
      F.obj (laurentFunctor.obj R) :=
  biprod.desc (F.map (plus.app R)) (-F.map (minus.app R))

@[reassoc] lemma polynomialDifference_naturality (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v})
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    biprod.map (F.map (polynomialFunctor.map f)) (F.map (polynomialFunctor.map f)) ≫
      polynomialDifference F S = polynomialDifference F R ≫ F.map (laurentFunctor.map f) := by
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc,polynomialDifference,biprod.inl_desc_assoc,
      biprod.inl_desc,← F.map_comp]
    rw [plus.naturality]
  · simp only [biprod.inr_map_assoc,polynomialDifference,biprod.inr_desc_assoc,
      biprod.inr_desc,Preadditive.comp_neg,Preadditive.neg_comp,← F.map_comp]
    rw [minus.naturality]

/-- Ring maps give literal commuting squares of polynomial-difference homomorphisms. -/
def polynomialDifferenceDiagram (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) :
    CommRingCat.{u} ⥤ Arrow AddCommGrpCat.{v} where
  obj R := Arrow.mk (polynomialDifference F R)
  map f := Arrow.homMk
    (biprod.map (F.map (polynomialFunctor.map f)) (F.map (polynomialFunctor.map f)))
    (F.map (laurentFunctor.map f)) (polynomialDifference_naturality F f)
  map_id R := by
    apply Arrow.hom_ext
    · apply biprod.hom_ext <;> simp
    · simp
  map_comp f g := by
    apply Arrow.hom_ext
    · apply biprod.hom_ext <;> simp
    · simp

/-- Bass contraction is the genuine categorical cokernel of the two chart maps. -/
def contraction (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) :
    CommRingCat.{u} ⥤ AddCommGrpCat.{v} := polynomialDifferenceDiagram F ⋙ coker AddCommGrpCat

/-- The original Laurent-to-cokernel projection, natural in the coefficient ring. -/
def contractionπ (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) :
    laurentFunctor ⋙ F ⟶ contraction F where
  app R := cokernel.π (polynomialDifference F R)
  naturality {R S} f := by
    simp [contraction, polynomialDifferenceDiagram, coker]

@[reassoc (attr := simp)] lemma polynomialDifference_contractionπ
    (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u}) :
    polynomialDifference F R ≫ (contractionπ F).app R = 0 := cokernel.condition _

/-- Descent from the actual Laurent group through the Bass quotient. -/
def contractionDesc (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u})
    {A : AddCommGrpCat.{v}} (f : F.obj (laurentFunctor.obj R) ⟶ A)
    (hf : polynomialDifference F R ≫ f = 0) : (contraction F).obj R ⟶ A :=
  cokernel.desc _ f hf

@[reassoc (attr := simp)] lemma contractionπ_desc
    (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u})
    {A : AddCommGrpCat.{v}} (f : F.obj (laurentFunctor.obj R) ⟶ A)
    (hf : polynomialDifference F R ≫ f = 0) :
    (contractionπ F).app R ≫ contractionDesc F R f hf = f := cokernel.π_desc _ _ _

lemma contraction_hom_ext (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u})
    {A : AddCommGrpCat.{v}} {f g : (contraction F).obj R ⟶ A}
    (h : (contractionπ F).app R ≫ f = (contractionπ F).app R ≫ g) : f = g :=
  (cancel_epi (cokernel.π (polynomialDifference F R))).mp h

/-- The actual presentation is right exact, without any hypothesis on F. -/
lemma contraction_exact (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u}) :
    (ShortComplex.mk (polynomialDifference F R) ((contractionπ F).app R)
      (polynomialDifference_contractionπ F R)).Exact :=
  ShortComplex.cokernelSequence_exact (polynomialDifference F R)

instance contractionπ_epi (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u}) :
    Epi ((contractionπ F).app R) := by
  change Epi (cokernel.π (polynomialDifference F R))
  infer_instance

@[reassoc (attr := simp)] lemma plus_contractionπ
    (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u}) :
    F.map (plus.app R) ≫ (contractionπ F).app R = 0 := by
  simpa [polynomialDifference] using congrArg (fun f ↦ biprod.inl ≫ f)
    (polynomialDifference_contractionπ F R)

@[reassoc (attr := simp)] lemma minus_contractionπ
    (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u}) :
    F.map (minus.app R) ≫ (contractionπ F).app R = 0 := by
  simpa [polynomialDifference] using congrArg (fun f ↦ biprod.inr ≫ f)
    (polynomialDifference_contractionπ F R)

/-- The categorical cokernel is the ordinary quotient by the original difference image. -/
def contractionQuotientIso (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u}) :
    (contraction F).obj R ≅ AddCommGrpCat.of
      (F.obj (laurentFunctor.obj R) ⧸ AddMonoidHom.range (polynomialDifference F R).hom) :=
  AddCommGrpCat.cokernelIsoQuotient (polynomialDifference F R)

@[reassoc (attr := simp)] lemma contractionπ_quotientIso
    (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u}) :
    (contractionπ F).app R ≫ (contractionQuotientIso F R).hom =
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' _) := by
  exact cokernel.π_desc _ _ _

/-- Natural transformations of original group functors induce the original difference square. -/
def polynomialDifferenceTransformation {F G : CommRingCat.{u} ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) : polynomialDifferenceDiagram F ⟶ polynomialDifferenceDiagram G where
  app R := Arrow.homMk (biprod.map (α.app _) (α.app _)) (α.app _) (by
    apply biprod.hom_ext' <;> simp [polynomialDifferenceDiagram, polynomialDifference,
      α.naturality])
  naturality {R S} f := by
    apply Arrow.hom_ext
    · apply biprod.hom_ext <;> simp [polynomialDifferenceDiagram, α.naturality]
    · exact α.naturality _

/-- The genuine induced map of Bass cokernels, natural in every coefficient ring. -/
def contractionMap {F G : CommRingCat.{u} ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) :
    contraction F ⟶ contraction G :=
  Functor.whiskerRight (polynomialDifferenceTransformation α) (coker AddCommGrpCat)

@[reassoc (attr := simp)] lemma contractionMap_π
    {F G : CommRingCat.{u} ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) (R : CommRingCat.{u}) :
    (contractionπ F).app R ≫ (contractionMap α).app R =
      α.app (laurentFunctor.obj R) ≫ (contractionπ G).app R := by
  simp [contractionMap, polynomialDifferenceTransformation, polynomialDifferenceDiagram,
    contractionπ, coker]

@[simp] lemma contractionMap_id (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) :
    contractionMap (𝟙 F) = 𝟙 (contraction F) := by
  apply NatTrans.ext
  funext R
  apply contraction_hom_ext F R
  simp

@[simp] lemma contractionMap_comp {F G H : CommRingCat.{u} ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) (β : G ⟶ H) :
    contractionMap (α ≫ β) = contractionMap α ≫ contractionMap β := by
  apply NatTrans.ext
  funext R
  apply contraction_hom_ext F R
  simp

/-- Bass contraction is an actual endofunctor on ring-indexed abelian group functors. -/
def contractionFunctor :
    (CommRingCat.{u} ⥤ AddCommGrpCat.{v}) ⥤ (CommRingCat.{u} ⥤ AddCommGrpCat.{v}) where
  obj := contraction
  map := contractionMap
  map_id := contractionMap_id
  map_comp := contractionMap_comp

end Quillen.Bass

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Bass

/-- The actual presentation homomorphism is literally plus(a) minus minus(b). -/
lemma polynomialDifference_pair (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u})
    (a b : F.obj (polynomialFunctor.obj R)) :
    polynomialDifference F R ((AddCommGrpCat.biprodIsoProd _ _).inv (a,b)) =
      F.map (plus.app R) a - F.map (minus.app R) b := by
  have h := AddCommGrpCat.biprodIsoProd_inv_comp_desc (F.map (plus.app R)) (-F.map (minus.app R))
  simpa [polynomialDifference, sub_eq_add_neg] using congrArg (fun f ↦ f (a,b)) h

/-- Every Bass class has an original Laurent representative. -/
lemma contractionπ_surjective (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u}) :
    Function.Surjective ((contractionπ F).app R) :=
  (AddCommGrpCat.epi_iff_surjective _).mp inferInstance

/-- A Laurent class vanishes precisely when it is an actual difference of the two chart images. -/
lemma contractionπ_eq_zero_iff (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u})
    (x : F.obj (laurentFunctor.obj R)) :
    (contractionπ F).app R x = 0 ↔ ∃ a b : F.obj (polynomialFunctor.obj R),
      F.map (plus.app R) a - F.map (minus.app R) b = x := by
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (ShortComplex.ab_exact_iff _).mp (contraction_exact F R) x hx
    let e := AddCommGrpCat.biprodIsoProd (F.obj (polynomialFunctor.obj R)) (F.obj
      (polynomialFunctor.obj R))
    refine ⟨(e.hom y).1,(e.hom y).2,?_⟩
    rw [← polynomialDifference_pair]
    simpa [e] using hy
  · rintro ⟨a,b,rfl⟩
    rw [← polynomialDifference_pair]
    exact congrArg (fun f ↦ f ((AddCommGrpCat.biprodIsoProd _ _).inv (a,b)))
      (polynomialDifference_contractionπ F R)

/-- A map killing both original chart images descends uniquely through the actual Bass cokernel. -/
def contractionDescOfCharts (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u})
    {A : AddCommGrpCat.{v}} (f : F.obj (laurentFunctor.obj R) ⟶ A)
    (hp : F.map (plus.app R) ≫ f = 0) (hm : F.map (minus.app R) ≫ f = 0) :
    (contraction F).obj R ⟶ A :=
  contractionDesc F R f (by apply biprod.hom_ext' <;> simp [polynomialDifference,hp,hm])

@[reassoc (attr := simp)] lemma contractionπ_descOfCharts
    (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u})
    {A : AddCommGrpCat.{v}} (f : F.obj (laurentFunctor.obj R) ⟶ A)
    (hp : F.map (plus.app R) ≫ f = 0) (hm : F.map (minus.app R) ≫ f = 0) :
    (contractionπ F).app R ≫ contractionDescOfCharts F R f hp hm = f :=
  contractionπ_desc F R f _

/-- If the plus chart is already surjective, its Bass cokernel is genuinely zero. -/
lemma contraction_isZero_of_epi_plus (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (R : CommRingCat.{u})
    [Epi (F.map (plus.app R))] : IsZero ((contraction F).obj R) := by
  apply IsZero.of_epi_eq_zero ((contractionπ F).app R)
  exact (cancel_epi (F.map (plus.app R))).mp (by simp)

/-- In particular the construction kills actual constant group functors. -/
lemma contraction_constant_isZero (A : AddCommGrpCat.{v}) (R : CommRingCat.{u}) :
    IsZero ((contraction ((Functor.const CommRingCat.{u}).obj A)).obj R) := by
  let : Epi (((Functor.const CommRingCat.{u}).obj A).map (plus.app R)) := by
    change Epi (𝟙 A)
    infer_instance
  exact contraction_isZero_of_epi_plus _ _

end Quillen.Bass

end
