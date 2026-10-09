import Quillen.Waldhausen.QuillenComparison.ZeroNormalization
import Quillen.Waldhausen.QuillenComparison.Functoriality
import Quillen.Waldhausen.QuillenComparison.Equivalence
import Quillen.Waldhausen.PointedFunctor

/-! # Normalized based naturality of the canonical Q/S equivalence

The strict-zero case follows from the actual simplicial squares and their
chosen zero vertices. Normalizing the original exact functor then gives the
unconditional based theorem, using genuine based invariance of Quillen K-maps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject
universe v u

namespace Quillen.Waldhausen.QuillenComparison

private theorem piMap_of_commuting_square
    {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y'] {x : X} {y : Y} {x' : X'} {y' : Y'}
    (n : ℕ) (f : ContinuousMap X Y) (hf : f x = y)
    (g : ContinuousMap X' Y') (hg : g x' = y')
    (a : ContinuousMap X X') (ha : a x = x')
    (b : ContinuousMap Y Y') (hb : b y = y') (h : g.comp a = b.comp f) :
    (piMap n g hg).comp (piMap n a ha) = (piMap n b hb).comp (piMap n f hf) := by
  ext z
  refine Quotient.inductionOn z (fun p ↦ ?_)
  apply congrArg Quotient.mk'
  ext t
  exact DFunLike.congr_fun h (p t)

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : Quillen.ExactStructure C} {ED : Quillen.ExactStructure D}
  (F : Quillen.ExactFunctor EC ED)

/-- Strict zero preservation retains the actual constant zero simplex in every degree. -/
theorem exactSSetMap_zeroSimplex_of_zeroEq
    (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : SimplexCategoryᵒᵖ) :
    (exactSSetMap F).app n
      (zeroSimplex EC.inflation (MorphismProperty.isomorphisms C) (0 : C) (isZero_zero C) n) =
    zeroSimplex ED.inflation (MorphismProperty.isomorphisms D) (0 : D) (isZero_zero D) n := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ h) ?_
  intro i j f
  simp [exactSSetMap, zeroSimplex]

/-- The raw S-map is based when its original functor preserves the chosen zero strictly. -/
theorem exactSSetMap_basepoint_of_zeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) :
    SSet.toTop.map (exactSSetMap F) (ofExactCategory EC).kBasepoint =
      (ofExactCategory ED).kBasepoint := by
  change (SSet.toTop.map (SSet.yonedaEquiv.symm
    (zeroSimplex EC.inflation (MorphismProperty.isomorphisms C) (0 : C) (isZero_zero C) (op ⦋0⦌))) ≫
      SSet.toTop.map (exactSSetMap F)) default = _
  rw [← CategoryTheory.Functor.map_comp, SSet.yonedaEquiv_symm_comp,
    exactSSetMap_zeroSimplex_of_zeroEq F h]
  rfl

/-- The same strict equality preserves the actual subdivided zero vertex. -/
theorem subdivisionExactMap_basepoint_of_zeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) :
    SSet.toTop.map (Edgewise.subdivisionFunctor.map (exactSSetMap F)) (subdivisionBasepoint EC) =
      subdivisionBasepoint ED := by
  have hz : (Edgewise.subdivisionFunctor.map (exactSSetMap F)).app (op ⦋0⦌)
      (subdivisionZeroVertex EC) = subdivisionZeroVertex ED :=
    exactSSetMap_zeroSimplex_of_zeroEq F h _
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (subdivisionZeroVertex EC)) ≫
    SSet.toTop.map (Edgewise.subdivisionFunctor.map (exactSSetMap F))) default = _
  rw [← CategoryTheory.Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  exact congrArg (fun z : (Edgewise.subdivision
    (sSet ED.inflation (MorphismProperty.isomorphisms D))).obj (op ⦋0⦌) ↦
      SSet.toTop.map (SSet.yonedaEquiv.symm z) default) hz

/-- The actual S-homomorphism of a strictly zero-preserving exact functor. -/
def exactSKMapOfZeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    (ofExactCategory EC).K n →* (ofExactCategory ED).K n :=
  piMap n (SSet.toTop.map (exactSSetMap F)).hom (exactSSetMap_basepoint_of_zeroEq F h)

/-- Its actual map on the common subdivided source of the Q/S zigzag. -/
def subdivisionExactKMapOfZeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    SubdivisionK EC n →* SubdivisionK ED n :=
  piMap n (SSet.toTop.map (Edgewise.subdivisionFunctor.map (exactSSetMap F))).hom
    (subdivisionExactMap_basepoint_of_zeroEq F h)

/-- The endpoint leg of the based zigzag commutes with actual strict-zero S-maps. -/
theorem subdivisionEndpointK_naturality_of_zeroEq
    (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    (subdivisionEndpointK ED n).comp (subdivisionExactKMapOfZeroEq F h n) =
      (exactSKMapOfZeroEq F h n).comp (subdivisionEndpointK EC n) := by
  apply piMap_of_commuting_square
  have hn := congrArg (fun f ↦ (SSet.toTop.map f).hom)
    (Edgewise.endpointNatTrans.naturality (exactSSetMap F))
  simpa only [CategoryTheory.Functor.map_comp, TopCat.hom_comp,
    Edgewise.endpointNatTrans, realizationEndpoint, CategoryTheory.Functor.id_map] using! hn

/-- The Q leg commutes with the existing normalized Quillen K-map in the strict-zero case. -/
theorem subdivisionComparisonK_naturality_of_zeroEq
    (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    (subdivisionComparisonK ED n).comp (subdivisionExactKMapOfZeroEq F h n) =
      (F.KMap n).comp (subdivisionComparisonK EC n) := by
  rw [F.KMap_eq_piMap_of_zeroEq h]
  apply piMap_of_commuting_square
  have hn := congrArg (fun f ↦ (SSet.toTop.map f).hom) (comparisonMap_naturality F)
  simpa only [CategoryTheory.Functor.map_comp, TopCat.hom_comp,
    realizationComparison, classifyingSpaceMap] using hn

/-- Inverting the proved endpoint isomorphism gives based Q/S naturality. -/
theorem comparisonK_naturality_of_zeroEq
    (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    (comparisonK ED n).comp (exactSKMapOfZeroEq F h n) =
      (F.KMap n).comp (comparisonK EC n) := by
  apply (MonoidHom.cancel_right (f := subdivisionEndpointK EC n)
    (subdivisionKEquiv EC n).surjective).mp
  calc
    _ = (comparisonK ED n).comp
        ((subdivisionEndpointK ED n).comp (subdivisionExactKMapOfZeroEq F h n)) := by
      rw [MonoidHom.comp_assoc, subdivisionEndpointK_naturality_of_zeroEq]
    _ = (subdivisionComparisonK ED n).comp (subdivisionExactKMapOfZeroEq F h n) := by
      rw [← MonoidHom.comp_assoc, comparisonK_comp_endpoint]
    _ = (F.KMap n).comp (subdivisionComparisonK EC n) :=
      subdivisionComparisonK_naturality_of_zeroEq F h n
    _ = _ := by rw [MonoidHom.comp_assoc, comparisonK_comp_endpoint]

/-- The canonical comparison equivalence commutes with strict-zero exact functors. -/
theorem comparisonKEquiv_naturality_of_zeroEq
    (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    (comparisonKEquiv ED n).toMonoidHom.comp (exactSKMapOfZeroEq F h n) =
      (F.KMap n).comp (comparisonKEquiv EC n).toMonoidHom :=
  comparisonK_naturality_of_zeroEq F h n

/-- The genuine normalized S-map of any exact functor, without a strict zero hypothesis. -/
def normalizedExactSKMap (n : ℕ) : (ofExactCategory EC).K n →* (ofExactCategory ED).K n :=
  exactSKMapOfZeroEq F.zeroNormalized F.zeroNormalized_obj_zero n

/-- Normalized based Q/S naturality for every genuine exact functor.
The Quillen map is the existing normalized map, not a newly defined substitute. -/
theorem comparisonKEquiv_naturality (n : ℕ) :
    (comparisonKEquiv ED n).toMonoidHom.comp (normalizedExactSKMap F n) =
      (F.KMap n).comp (comparisonKEquiv EC n).toMonoidHom := by
  simpa only [normalizedExactSKMap, Quillen.ExactFunctor.zeroNormalized_KMap] using
    comparisonKEquiv_naturality_of_zeroEq F.zeroNormalized F.zeroNormalized_obj_zero n

private theorem piMap_congr_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f g : ContinuousMap X Y) (hf : f x = y) (hg : g x = y)
    (h : f = g) : piMap n f hf = piMap n g hg := by
  subst g
  rfl

private theorem groupsMapOfZeroEq_eq_piMap {G : C ⥤ D}
    (hG : IsExact EC.inflation (MorphismProperty.isomorphisms C)
      ED.inflation (MorphismProperty.isomorphisms D) G)
    (Z : C) (hZ : IsZero Z) (Z' : D) (hZ' : IsZero Z') (h : G.obj Z = Z') (n : ℕ)
    (hb : deloopingMap hG (basepoint EC.inflation (MorphismProperty.isomorphisms C) Z hZ) =
      basepoint ED.inflation (MorphismProperty.isomorphisms D) Z' hZ') :
    groupsMapOfZeroEq hG Z hZ Z' hZ' h n = piMap n (deloopingMap hG).hom hb := by
  subst Z'
  rfl

/-- The canonical zero isomorphisms used by the two normalization APIs agree,
because maps to an actual zero object are unique. -/
theorem zeroNormalized_eq_waldhausenRebase
    (hF : IsExact (ofExactCategory EC).cof (ofExactCategory EC).weq
      (ofExactCategory ED).cof (ofExactCategory ED).weq F.toFunctor) :
    F.zeroNormalized.toFunctor = rebaseFunctor F.toFunctor
      (ofExactCategory EC).zero (ofExactCategory ED).zero
      ((hF.zero (ofExactCategory EC).isZero).iso (ofExactCategory ED).isZero) := by
  rw [F.zeroNormalized_toFunctor]
  congr 1
  apply Iso.ext
  apply Subsingleton.elim

/-- The normalized S-map uses exactly the simplicial map already underlying
Waldhausen.KMap, when its structural exactness witness is supplied. -/
theorem exactSSetMap_zeroNormalized_eq_sSetMap_rebase
    (hF : IsExact (ofExactCategory EC).cof (ofExactCategory EC).weq
      (ofExactCategory ED).cof (ofExactCategory ED).weq F.toFunctor) :
    exactSSetMap F.zeroNormalized = sSetMap hF.rebase := by
  ext n A
  apply Subtype.ext
  exact congrArg (fun G ↦ A.1 ⋙ G) (zeroNormalized_eq_waldhausenRebase F hF)

/-- Agreement with the existing genuinely zero-normalized Waldhausen K-map.
The extra witness is ordinary structural exactness, not a comparison square. -/
theorem normalizedExactSKMap_eq_KMap
    (hF : IsExact (ofExactCategory EC).cof (ofExactCategory EC).weq
      (ofExactCategory ED).cof (ofExactCategory ED).weq F.toFunctor) (n : ℕ) :
    normalizedExactSKMap F n = Waldhausen.KMap hF n := by
  have hs := exactSSetMap_zeroNormalized_eq_sSetMap_rebase F hF
  have hb : deloopingMap hF.rebase (ofExactCategory EC).kBasepoint =
      (ofExactCategory ED).kBasepoint := by
    change SSet.toTop.map (sSetMap hF.rebase) _ = _
    rw [← hs]
    exact exactSSetMap_basepoint_of_zeroEq F.zeroNormalized F.zeroNormalized_obj_zero
  exact (piMap_congr_map n _ _
    (exactSSetMap_basepoint_of_zeroEq F.zeroNormalized F.zeroNormalized_obj_zero) hb
      (congrArg (fun f ↦ (SSet.toTop.map f).hom) hs)).trans
    (groupsMapOfZeroEq_eq_piMap hF.rebase (0 : C) (isZero_zero C) (0 : D) (isZero_zero D)
      (rebaseFunctor_obj_base _ _ _ _) n hb).symm

/-- The proved comparison equivalence commutes with the two original based
K-map APIs, with their actual canonical zero normalization. -/
theorem comparisonKEquiv_naturality_KMap
    (hF : IsExact (ofExactCategory EC).cof (ofExactCategory EC).weq
      (ofExactCategory ED).cof (ofExactCategory ED).weq F.toFunctor) (n : ℕ) :
    (comparisonKEquiv ED n).toMonoidHom.comp (Waldhausen.KMap hF n) =
      (F.KMap n).comp (comparisonKEquiv EC n).toMonoidHom := by
  rw [← normalizedExactSKMap_eq_KMap F hF n]
  exact comparisonKEquiv_naturality F n

end Quillen.Waldhausen.QuillenComparison
