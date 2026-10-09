import Quillen.CategoryTheory.TheoremA.RealizationSkeleton
import Quillen.CategoryTheory.TheoremA.RealizationBoundary

/-!
# Homotopy extension for the actual enriched boundary inclusions

The realization of the standard simplicial boundary is homeomorphic to its
zero-coordinate barycentric boundary. The proof uses the finite face charts,
including their codimension-two intersections, and compactness. The empty
zero-dimensional boundary is treated explicitly.

A colimit argument then proves that realization preserves products with a
simplicial set whose realization is locally compact, in particular every
standard boundary. Together with the simplex product comparison and the
explicit geometric boundary extension theorem, this proves HEP for the
realized diagonal of every enriched simplex-boundary inclusion.
-/

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremA

/-- The diagonal of an external product is its ordinary simplicial product. -/
def diagonalOuterProductIso (K X : SSet.{u}) :
    diagonalSSet (outerProduct K X) ≅ X ⊗ K :=
  NatIso.ofComponents (fun p ↦ Equiv.toIso
    { toFun := fun x ↦ (x.2, x.1)
      invFun := fun x ↦ ⟨x.2, x.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) (by intros; rfl)

@[reassoc]
theorem diagonalOuterProductIso_naturality {K L X : SSet.{u}} (f : K ⟶ L) :
    diagonalMap (outerProductMap (X := X) f) ≫ (diagonalOuterProductIso L X).hom =
      (diagonalOuterProductIso K X).hom ≫ (X ◁ f) := rfl

end Quillen.TheoremA

namespace Quillen

/-- The realized face inclusion in a simplicial boundary. -/
def realizationBoundaryFace {n : ℕ} (i : Fin (n + 2)) :
    |(Δ[n] : SSet.{u})| ⟶ |(∂Δ[n + 1] : SSet.{u})| :=
  SSet.toTop.map (SSet.boundary.ι i)

/-- Realizing the boundary inclusion and taking barycentric coordinates. -/
def realizationBoundaryCoordinates (n : ℕ) :
    C(|(∂Δ[n] : SSet.{u})|, StdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun x ↦ SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map ∂Δ[n].ι x), by fun_prop⟩

@[simp] theorem realizationBoundaryCoordinates_face {n : ℕ} (i : Fin (n + 2))
    (t : |(Δ[n] : SSet.{u})|) :
    realizationBoundaryCoordinates (n + 1) (realizationBoundaryFace i t) =
      (SimplexCategory.toTopHomeo ⦋n⦌ t).map i.succAbove := by
  change SimplexCategory.toTopHomeo ⦋n + 1⦌
    ((SSet.toTop.map (SSet.boundary.ι i) ≫ SSet.toTop.map ∂Δ[n + 1].ι) t) = _
  rw [← Functor.map_comp, SSet.boundary.ι_ι]
  exact SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i) t

/-- Every boundary simplex factors through one of its finitely many faces. -/
theorem boundary_simplex_factors {n : ℕ} {m : SimplexCategoryᵒᵖ}
    (s : (∂Δ[n + 1] : SSet.{u}).obj m) :
    ∃ (i : Fin (n + 2)) (f : m.unop ⟶ ⦋n⦌),
      (SSet.boundary.ι i).app m (SSet.stdSimplex.objEquiv.symm f) = s := by
  obtain ⟨i, f, hf⟩ := SimplexCategory.eq_comp_δ_of_not_surjective
    (SSet.stdSimplex.objEquiv s.1) s.2
  refine ⟨i, f, ?_⟩
  apply Subtype.ext
  apply SSet.stdSimplex.objEquiv.injective
  exact hf.symm

/-- The finitely many face charts cover the realized boundary. -/
theorem realizationBoundaryFace_jointly_surjective {n : ℕ}
    (x : |(∂Δ[n + 1] : SSet.{u})|) :
    ∃ (i : Fin (n + 2)) (t : |(Δ[n] : SSet.{u})|), realizationBoundaryFace i t = x := by
  obtain ⟨m, f, t, rfl⟩ := realization_exists_simplex x
  obtain ⟨i, g, hg⟩ := boundary_simplex_factors (SSet.yonedaEquiv f)
  refine ⟨i, SSet.toTop.map (SSet.stdSimplex.map g) t, ?_⟩
  change (SSet.toTop.map (SSet.stdSimplex.map g) ≫
    SSet.toTop.map (SSet.boundary.ι i)) t = _
  rw [← Functor.map_comp]
  have heq : SSet.stdSimplex.map g ≫ SSet.boundary.ι i = f := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map] using hg
  rw [heq]

instance realizationBoundarySucc_compactSpace (n : ℕ) :
    CompactSpace |(∂Δ[n + 1] : SSet.{u})| := by
  let f : (Σ _ : Fin (n + 2), |(Δ[n] : SSet.{u})|) →
      |(∂Δ[n + 1] : SSet.{u})| := fun z ↦ realizationBoundaryFace z.1 z.2
  have hf : Continuous f := continuous_sigma (fun _ ↦ (realizationBoundaryFace _).hom.continuous)
  exact Function.Surjective.compactSpace hf (fun x ↦ by
    obtain ⟨i, t, ht⟩ := realizationBoundaryFace_jointly_surjective x
    exact ⟨⟨i, t⟩, ht⟩)

instance realizationBoundaryZero_isEmpty : IsEmpty |(∂Δ[0] : SSet.{u})| := ⟨by
  intro x
  obtain ⟨m, f, t, ht⟩ := realization_exists_simplex x
  have h := (SSet.yonedaEquiv f).2
  simp at h⟩

instance realizationBoundary_compactSpace (n : ℕ) :
    CompactSpace |(∂Δ[n] : SSet.{u})| := by
  cases n with
  | zero => infer_instance
  | succ n => infer_instance

instance simplexBoundaryZero_isEmpty : IsEmpty (simplexBoundary 0) := ⟨by
  rintro ⟨x, i, hi⟩
  have he : i = 0 := Fin.ext (by omega)
  have ht : x.weights 0 = 1 := by simp
  rw [he, ht] at hi
  exact zero_ne_one hi.symm⟩

/-- Boundary coordinates land in the actual zero-coordinate boundary. -/
theorem realizationBoundaryCoordinates_mem (n : ℕ) (x : |(∂Δ[n] : SSet.{u})|) :
    realizationBoundaryCoordinates n x ∈ simplexBoundary n := by
  cases n with
  | zero => exact isEmptyElim x
  | succ n =>
    obtain ⟨i, t, rfl⟩ := realizationBoundaryFace_jointly_surjective x
    refine ⟨i, ?_⟩
    rw [realizationBoundaryCoordinates_face]
    exact (StdSimplex.mem_range_map_iff i.succAbove _).mp ⟨_, rfl⟩ i
      (by simp [Fin.range_succAbove])

/-- The canonical continuous boundary comparison. -/
def realizationBoundaryComparison (n : ℕ) :
    C(|(∂Δ[n] : SSet.{u})|, simplexBoundary n) :=
  ⟨fun x ↦ ⟨realizationBoundaryCoordinates n x, realizationBoundaryCoordinates_mem n x⟩,
    (realizationBoundaryCoordinates n).continuous.subtype_mk _⟩

/-- Every point on the geometric boundary lies in a realized face. -/
theorem realizationBoundaryComparison_surjective (n : ℕ) :
    Function.Surjective (realizationBoundaryComparison.{u} n) := by
  cases n with
  | zero => exact fun x ↦ isEmptyElim x
  | succ n =>
    rintro ⟨z, i, hi⟩
    obtain ⟨w, hw⟩ := stdSimplex_exists_face_of_weight_zero i z hi
    refine ⟨realizationBoundaryFace i ((SimplexCategory.toTopHomeo ⦋n⦌).symm w), ?_⟩
    apply Subtype.ext
    change realizationBoundaryCoordinates (n + 1) _ = z
    rw [realizationBoundaryCoordinates_face, Homeomorph.apply_symm_apply, hw]

lemma stdSimplex_map_injective {A B : Type*} {f : A → B} (hf : Function.Injective f) :
    Function.Injective (StdSimplex.map (R := ℝ) f) := by
  intro x y h
  apply StdSimplex.ext
  exact Finsupp.mapDomain_injective hf (congrArg StdSimplex.weights h)

/-- The two orders of passing to a codimension-two face agree. -/
lemma boundaryFace_pair_relation {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    SSet.stdSimplex.δ (j.pred (Fin.ne_zero_of_lt h)) ≫ SSet.boundary.ι i =
      SSet.stdSimplex.δ (i.castPred (Fin.ne_last_of_lt h)) ≫ SSet.boundary.ι j := by
  rw [← cancel_mono ∂Δ[n + 2].ι]
  simp only [Category.assoc, SSet.boundary.ι_ι]
  exact (SSet.stdSimplex.facePairComplIso_hom_ι' i j h).symm.trans
    (SSet.stdSimplex.facePairComplIso_hom_ι i j h)

lemma simplex_face_pair_relation {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt h)) ≫ SimplexCategory.δ i =
      SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt h)) ≫ SimplexCategory.δ j := by
  obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  dsimp
  rw [Fin.pred_succ]
  exact (SimplexCategory.δ_comp_δ (by grind)).symm


/-- Two geometric faces meet along their common codimension-two face. -/
lemma stdSimplex_exists_pair_face {n : ℕ} (i j : Fin (n + 3)) (h : i < j)
    (z : StdSimplex ℝ (Fin (n + 3))) (hi : z.weights i = 0) (hj : z.weights j = 0) :
    ∃ w : StdSimplex ℝ (Fin (n + 1)),
      (w.map (j.pred (Fin.ne_zero_of_lt h)).succAbove).map i.succAbove = z ∧
      (w.map (i.castPred (Fin.ne_last_of_lt h)).succAbove).map j.succAbove = z := by
  let e := SSet.stdSimplex.finOrderIsoPairCompl i j h
  let g : Fin (n + 1) → Fin (n + 3) := fun k ↦ (e k).1
  have hz : z ∈ Set.range (StdSimplex.map g) := by
    rw [StdSimplex.mem_range_map_iff]
    intro k hk
    by_cases hki : k = i
    · simpa [hki] using hi
    by_cases hkj : k = j
    · simpa [hkj] using hj
    exfalso
    apply hk
    have hkm : k ∈ ({i, j}ᶜ : Finset _) := by simp [hki, hkj]
    refine ⟨e.symm ⟨k, hkm⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨k, hkm⟩)
  obtain ⟨w, hw⟩ := hz
  refine ⟨w, ?_, ?_⟩
  · rw [StdSimplex.map_map]
    have hg : (fun k ↦ i.succAbove ((j.pred (Fin.ne_zero_of_lt h)).succAbove k)) = g := by
      funext k
      exact ConcreteCategory.congr_hom (simplex_face_pair_relation i j h) k
    rwa [hg]
  · simpa only [StdSimplex.map_map, g, e, SSet.stdSimplex.finOrderIsoPairCompl_apply_val] using hw

/-- Distinct realized face charts agree whenever their barycentric points agree. -/
lemma realizationBoundaryFace_overlap_ordered {n : ℕ} (i j : Fin (n + 3)) (h : i < j)
    (v w : StdSimplex ℝ (Fin (n + 2)))
    (hvw : v.map i.succAbove = w.map j.succAbove) :
    realizationBoundaryFace.{u} i ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm v) =
      realizationBoundaryFace j ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm w) := by
  have hi : (v.map i.succAbove).weights i = 0 :=
    (StdSimplex.mem_range_map_iff i.succAbove _).mp ⟨v, rfl⟩ i
      (by simp [Fin.range_succAbove])
  have hj : (v.map i.succAbove).weights j = 0 := by
    rw [hvw]
    exact (StdSimplex.mem_range_map_iff j.succAbove _).mp ⟨w, rfl⟩ j
      (by simp [Fin.range_succAbove])
  obtain ⟨z, hzi, hzj⟩ := stdSimplex_exists_pair_face i j h _ hi hj
  have hv : z.map (j.pred (Fin.ne_zero_of_lt h)).succAbove = v :=
    stdSimplex_map_injective (Fin.succAbove_right_injective (p := i)) hzi
  have hw : z.map (i.castPred (Fin.ne_last_of_lt h)).succAbove = w :=
    stdSimplex_map_injective (Fin.succAbove_right_injective (p := j)) (hzj.trans hvw)
  rw [← hv, ← hw]
  change realizationBoundaryFace i ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
      (z.map (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt h))))) =
    realizationBoundaryFace j ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
      (z.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt h)))))
  rw [SimplexCategory.toTopHomeo_symm_naturality_apply,
    SimplexCategory.toTopHomeo_symm_naturality_apply]
  change (SSet.toTop.map (SSet.stdSimplex.δ _) ≫ SSet.toTop.map (SSet.boundary.ι i)) _ =
    (SSet.toTop.map (SSet.stdSimplex.δ _) ≫ SSet.toTop.map (SSet.boundary.ι j)) _
  rw [← Functor.map_comp, ← Functor.map_comp, boundaryFace_pair_relation i j h]

/-- All realized boundary charts identify exactly their common geometric faces. -/
lemma realizationBoundaryFace_overlap {n : ℕ} (i j : Fin (n + 2))
    (v w : StdSimplex ℝ (Fin (n + 1)))
    (hvw : v.map i.succAbove = w.map j.succAbove) :
    realizationBoundaryFace.{u} i ((SimplexCategory.toTopHomeo ⦋n⦌).symm v) =
      realizationBoundaryFace j ((SimplexCategory.toTopHomeo ⦋n⦌).symm w) := by
  by_cases hij : i = j
  · subst j
    have hvw' := stdSimplex_map_injective (Fin.succAbove_right_injective (p := i)) hvw
    rw [hvw']
  cases n with
  | zero =>
    have hv : v = StdSimplex.single (0 : Fin 1) := Subsingleton.elim _ _
    have hw : w = StdSimplex.single (0 : Fin 1) := Subsingleton.elim _ _
    rw [hv, hw, StdSimplex.map_single, StdSimplex.map_single] at hvw
    have he := StdSimplex.single_injective hvw
    fin_cases i <;> fin_cases j <;> simp_all
  | succ n =>
    rcases lt_or_gt_of_ne hij with h | h
    · exact realizationBoundaryFace_overlap_ordered i j h v w hvw
    · exact (realizationBoundaryFace_overlap_ordered j i h w v hvw.symm).symm

/-- The boundary comparison is injective, including all face intersections. -/
theorem realizationBoundaryComparison_injective (n : ℕ) :
    Function.Injective (realizationBoundaryComparison.{u} n) := by
  intro x y h
  cases n with
  | zero => exact isEmptyElim x
  | succ n =>
    obtain ⟨i, s, rfl⟩ := realizationBoundaryFace_jointly_surjective x
    obtain ⟨j, t, rfl⟩ := realizationBoundaryFace_jointly_surjective y
    obtain ⟨v, rfl⟩ := (SimplexCategory.toTopHomeo ⦋n⦌).symm.surjective s
    obtain ⟨w, rfl⟩ := (SimplexCategory.toTopHomeo ⦋n⦌).symm.surjective t
    have h' := congrArg Subtype.val h
    change realizationBoundaryCoordinates (n + 1) _ =
      realizationBoundaryCoordinates (n + 1) _ at h'
    simp only [realizationBoundaryCoordinates_face, Homeomorph.apply_symm_apply] at h'
    exact realizationBoundaryFace_overlap i j v w h'

/-- Realization of the simplicial boundary is its actual barycentric boundary. -/
def realizationBoundaryHomeomorph (n : ℕ) :
    |(∂Δ[n] : SSet.{u})| ≃ₜ simplexBoundary n :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (realizationBoundaryComparison n)
      ⟨realizationBoundaryComparison_injective n, realizationBoundaryComparison_surjective n⟩)
    (realizationBoundaryComparison n).continuous

instance realizationBoundary_t2Space (n : ℕ) : T2Space |(∂Δ[n] : SSet.{u})| :=
  (realizationBoundaryHomeomorph n).symm.t2Space

instance realizationBoundary_locallyCompactSpace (n : ℕ) :
    LocallyCompactSpace |(∂Δ[n] : SSet.{u})| := inferInstance

/-- Product comparison is compatible with interchanging the two factors. -/
lemma realizationProductComparison_swap (X Y : SSet.{u}) :
    SSet.toTop.map (β_ X Y).hom ≫ CartesianMonoidalCategory.prodComparison SSet.toTop Y X =
      CartesianMonoidalCategory.prodComparison SSet.toTop X Y ≫ (β_ |X| |Y|).hom := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

lemma realizationProductComparison_isIso_swap (X Y : SSet.{u})
    [IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop Y X)] :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Y) := by
  have h : CartesianMonoidalCategory.prodComparison SSet.toTop X Y =
      SSet.toTop.map (β_ X Y).hom ≫ CartesianMonoidalCategory.prodComparison SSet.toTop Y X ≫ (β_ |X| |Y|).inv := by
    rw [← Category.assoc, realizationProductComparison_swap]
    simp
  rw [h]
  infer_instance

/-- The product comparison with a fixed second simplicial factor. -/
def realizationProductComparisonRightNatTrans (Y : SSet.{u}) :
    tensorRight Y ⋙ SSet.toTop ⟶ SSet.toTop ⋙ tensorRight |Y| where
  app X := CartesianMonoidalCategory.prodComparison SSet.toTop X Y
  naturality _ _ f := prodComparison_natural_whiskerRight SSet.toTop f

/-- Realization preserves product with any factor whose realization is locally compact. -/
theorem realizationProductComparison_isIso_of_locallyCompact
    (X Y : SSet.{u}) [LocallyCompactSpace |Y|] :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Y) := by
  let K := Presheaf.functorToRepresentables X
  let η := realizationProductComparisonRightNatTrans Y
  have : ∀ j, IsIso ((Functor.whiskerLeft K η).app j) := by
    intro j
    change IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop (SSet.stdSimplex.obj j.unop.obj.unop) Y)
    exact realizationProductComparison_isIso_swap _ _
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft K η)
  have : PreservesColimitsOfShape X.Elementsᵒᵖ (tensorRight Y) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight Y)
  let := (topologicalProductMappingSpaceAdjunction |Y|).isLeftAdjoint
  have : PreservesColimit K (tensorRight Y) := by infer_instance
  have : PreservesColimit (K ⋙ tensorRight Y) SSet.toTop := by infer_instance
  have : PreservesColimit K SSet.toTop := by infer_instance
  have : PreservesColimit (K ⋙ SSet.toTop) (tensorRight |Y|) := by infer_instance
  exact isIso_app_coconePt_of_preservesColimit K η
    (Presheaf.coconeOfRepresentable X) (Presheaf.colimitOfRepresentable X)

instance realizationProductComparison_boundary_isIso (X : SSet.{u}) (n : ℕ) :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop X (∂Δ[n] : SSet.{u})) :=
  realizationProductComparison_isIso_of_locallyCompact X _

/-- The realized product with a boundary, in ordinary geometric coordinates. -/
def realizationProductBoundaryHomeomorph (X : SSet.{u}) (n : ℕ) :
    |X ⊗ (∂Δ[n] : SSet.{u})| ≃ₜ |X| × simplexBoundary n :=
  (TopCat.homeoOfIso (asIso (CartesianMonoidalCategory.prodComparison SSet.toTop X
      (∂Δ[n] : SSet.{u})))).trans
    ((Homeomorph.refl _).prodCongr (realizationBoundaryHomeomorph n))

/-- The realized product with a simplex, allowing an arbitrary simplicial parameter. -/
def realizationProductSimplexParameterHomeomorph (X : SSet.{u}) (n : ℕ) :
    |X ⊗ Δ[n]| ≃ₜ |X| × StdSimplex ℝ (Fin (n + 1)) :=
  (TopCat.homeoOfIso (realizationProductSimplexIso X n)).trans
    ((Homeomorph.refl _).prodCongr (SimplexCategory.toTopHomeo ⦋n⦌))

namespace TheoremA

/-- The product comparisons identify the actual simplicial boundary map with
its ordinary parameterized topological boundary inclusion. -/
theorem realizationProductBoundary_square (X : SSet.{u}) (n : ℕ) :
    SSet.toTop.map (X ◁ ∂Δ[n].ι) ≫
        (TopCat.isoOfHomeo (realizationProductSimplexParameterHomeomorph X n)).hom =
      (TopCat.isoOfHomeo (realizationProductBoundaryHomeomorph X n)).hom ≫
        parameterizedSimplexBoundaryInclusion |X| n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  have h := ConcreteCategory.congr_hom
    (prodComparison_natural_whiskerLeft (A := X) SSet.toTop ∂Δ[n].ι) x
  apply Prod.ext
  · exact congrArg (fun z : |X| × |(Δ[n] : SSet.{u})| ↦ z.1) h
  · exact congrArg (fun z ↦ SimplexCategory.toTopHomeo ⦋n⦌ z.2) h

/-- Homotopy extension is invariant under an isomorphism of arrows. -/
theorem homotopyExtensionProperty_of_iso_square
    {A B C D : TopCat.{u}} (i : A ⟶ B) (j : C ⟶ D)
    (eA : A ≅ C) (eB : B ≅ D) (h : i ≫ eB.hom = eA.hom ≫ j)
    (hj : homotopyExtensionProperty j) : homotopyExtensionProperty i := by
  have hi : i = eA.hom ≫ j ≫ eB.inv := by
    rw [← Category.assoc, ← h]
    simp
  rw [hi]
  exact homotopyExtensionProperty_comp (homotopyExtensionProperty_of_isIso eA.hom)
    (homotopyExtensionProperty_comp hj (homotopyExtensionProperty_of_isIso eB.inv))

/-- Realized simplicial products with a standard boundary have genuine HEP. -/
theorem homotopyExtensionProperty_realizationProductBoundary (X : SSet.{u}) (n : ℕ) :
    homotopyExtensionProperty (SSet.toTop.map (X ◁ ∂Δ[n].ι)) :=
  homotopyExtensionProperty_of_iso_square _ _
    (TopCat.isoOfHomeo (realizationProductBoundaryHomeomorph X n))
    (TopCat.isoOfHomeo (realizationProductSimplexParameterHomeomorph X n))
    (realizationProductBoundary_square X n)
    (homotopyExtensionProperty_simplexBoundary |X| n)

/-- The actual enriched boundary map used in replacement skeleta has HEP. -/
theorem homotopyExtensionProperty_enrichedBoundary (X : SSet.{u}) (n : ℕ) :
    homotopyExtensionProperty
      (SSet.toTop.map (diagonalMap (outerProductMap (X := X) ∂Δ[n].ι))) := by
  apply homotopyExtensionProperty_of_iso_square _ (SSet.toTop.map (X ◁ ∂Δ[n].ι))
    (SSet.toTop.mapIso (diagonalOuterProductIso (∂Δ[n] : SSet.{u}) X))
    (SSet.toTop.mapIso (diagonalOuterProductIso Δ[n] X))
  · simpa only [Functor.mapIso_hom, ← Functor.map_comp] using
      congrArg SSet.toTop.map (diagonalOuterProductIso_naturality (X := X) ∂Δ[n].ι)
  · exact homotopyExtensionProperty_realizationProductBoundary X n

/-- In particular every single enriched cell boundary in the replacement has HEP. -/
theorem homotopyExtensionProperty_replacementCellBoundary
    {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})
    {n : ℕ} (s : (nerve D).nonDegenerate n) :
    homotopyExtensionProperty (SSet.toTop.map (diagonalMap (replacementCellBoundaryι H s))) :=
  homotopyExtensionProperty_enrichedBoundary (H.obj (s.1.obj 0)) n

end TheoremA

end Quillen
