import Quillen.Topology.Realization.ProductSimplex
import Quillen.Topology.Realization.SimplexHomotopy
import Quillen.CategoryTheory.TheoremB.Naturality

/-! Two-simplex coherence for inverse natural-isomorphism homotopies. -/
noncomputable section
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- A chain of functors and natural transformations gives its actual simplex family. -/
def functorChainNerveCylinder {n : ℕ} (A : ComposableArrows (C ⥤ D) n) :
    nerve C ⊗ Δ[n] ⟶ nerve D where
  app k := ↾fun z ↦
    (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙ Functor.uncurry.obj A
  naturality _ _ _ := by ext z; rfl

@[simp] theorem functorChainNerveCylinder_one {F G : C ⥤ D} (α : F ⟶ G) :
    functorChainNerveCylinder (ComposableArrows.mk₁ α) = naturalTransformationNerveCylinder α := rfl

/-- Restricting the parameter simplex restricts the chain of transformations. -/
theorem functorChainNerveCylinder_precomp {n m : ℕ}
    (A : ComposableArrows (C ⥤ D) n) (f : ⦋m⦌ ⟶ ⦋n⦌) :
    ((𝟙 (nerve C)) ⊗ₘ SSet.stdSimplex.map f) ≫ functorChainNerveCylinder A =
      functorChainNerveCylinder (f.toOrderHom.monotone.functor ⋙ A) := by
  ext k z : 4
  rfl

/-- The complete continuous simplex family over the source classifying space. -/
def functorChainRealization {n : ℕ} (A : ComposableArrows (C ⥤ D) n) :
    C(ClassifyingSpace C × |(Δ[n] : SSet.{u})|, ClassifyingSpace D) :=
  (SSet.toTop.map (functorChainNerveCylinder A)).hom.comp
    (realizationProductSimplexIso (nerve C) n).inv.hom

/-- Naturality of inverse product-with-simplex realization. -/
@[reassoc] theorem realizationProductSimplexIso_inv_naturality {X Y : SSet.{u}}
    (f : X ⟶ Y) {m n : ℕ} (g : ⦋m⦌ ⟶ ⦋n⦌) :
    (realizationProductSimplexIso X m).inv ≫ SSet.toTop.map (f ⊗ₘ SSet.stdSimplex.map g) =
      (SSet.toTop.map f ⊗ₘ SSet.toTop.map (SSet.stdSimplex.map g)) ≫
        (realizationProductSimplexIso Y n).inv :=
  (CommSq.vert_inv (CommSq.mk (realizationProductSimplexIso_naturality f g))).w.symm

/-- Restriction of a realized simplex family agrees exactly with the realized subchain. -/
theorem functorChainRealization_precomp {n m : ℕ}
    (A : ComposableArrows (C ⥤ D) n) (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : ClassifyingSpace C) (z : |(Δ[m] : SSet.{u})|) :
    functorChainRealization A (x, SSet.toTop.map (SSet.stdSimplex.map f) z) =
      functorChainRealization (f.toOrderHom.monotone.functor ⋙ A) (x, z) := by
  have h := realizationProductSimplexIso_inv_naturality (𝟙 (nerve C)) f
  have hp := ConcreteCategory.congr_hom h (x, z)
  change SSet.toTop.map (functorChainNerveCylinder A)
    ((realizationProductSimplexIso (nerve C) n).inv
      (x, SSet.toTop.map (SSet.stdSimplex.map f) z)) = _
  have hv : (SSet.toTop.map (𝟙 (nerve C)) ⊗ₘ SSet.toTop.map (SSet.stdSimplex.map f))
      (x, z) = (x, SSet.toTop.map (SSet.stdSimplex.map f) z) := by simp
  rw [TopCat.comp_app, TopCat.comp_app, hv] at hp
  rw [← hp]
  change (SSet.toTop.map ((𝟙 (nerve C)) ⊗ₘ SSet.stdSimplex.map f) ≫
    SSet.toTop.map (functorChainNerveCylinder A)) _ = _
  rw [← SSet.toTop.map_comp, functorChainNerveCylinder_precomp]
  rfl
/-- At dimension one, the product-simplex and interval-cylinder comparisons agree. -/
theorem realizationProductSimplexIso_one (X : SSet.{u}) :
    (realizationProductSimplexIso X 1).hom ≫
      (|X| ◁ SSet.stdSimplex.toTopObjIsoI.hom) = (realizationCylinderIso X).hom := by
  change prodComparison SSet.toTop X Δ[1] ≫
      (|X| ◁ SSet.stdSimplex.toTopObjIsoI.hom) = realizationCylinderComparison X
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [realizationCylinderComparison]

theorem realizationProductSimplexIso_one_inv (X : SSet.{u}) :
    (|X| ◁ SSet.stdSimplex.toTopObjIsoI.inv) ≫
      (realizationProductSimplexIso X 1).inv = (realizationCylinderIso X).inv := by
  have he : realizationProductSimplexIso X 1 ≪≫
      MonoidalCategory.whiskerLeftIso |X| SSet.stdSimplex.toTopObjIsoI = realizationCylinderIso X :=
    Iso.ext (realizationProductSimplexIso_one X)
  exact congrArg Iso.inv he

/-- The one-simplex family is exactly the already defined transformation homotopy. -/
theorem functorChainRealization_one {F G : C ⥤ D} (α : F ⟶ G)
    (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainRealization (ComposableArrows.mk₁ α) (x, realizationInterval t) =
      classifyingSpaceNaturalTransformationHomotopy α (t, x) := by
  have hp := ConcreteCategory.congr_hom (realizationProductSimplexIso_one_inv (nerve C))
    (x, ULift.up t)
  exact congrArg (SSet.toTop.map (naturalTransformationNerveCylinder α)) hp

/-- The three edges of a realized chain of two transformations. -/
theorem functorChainRealization_two_face {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (i : Fin 3) (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainRealization (ComposableArrows.mk₂ α β)
      (x, SSet.toTop.map (SSet.stdSimplex.δ i) (realizationInterval t)) =
    functorChainRealization ((nerve (C ⥤ D)).δ i (ComposableArrows.mk₂ α β))
      (x, realizationInterval t) :=
  functorChainRealization_precomp _ (SimplexCategory.δ i) x _

/-- The realized homotopy of the identity transformation is constant at every source point. -/
theorem classifyingHomotopy_id (F : C ⥤ D) (x : ClassifyingSpace C) (t : unitInterval) :
    classifyingSpaceNaturalTransformationHomotopy (𝟙 F) (t, x) = classifyingSpaceMap F x := by
  have he : naturalTransformationCylinderFunctor (𝟙 F) =
      CategoryTheory.Prod.snd (Fin 2) C ⋙ F := by
    refine CategoryTheory.Functor.hext (fun X ↦ ?_) ?_
    · rcases X with ⟨i, x⟩
      fin_cases i <;> rfl
    · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨f, g⟩
      have hij := leOfHom f
      fin_cases i <;> fin_cases j
      · simp [naturalTransformationCylinderFunctor, Functor.uncurry, ComposableArrows.mk₁]
      · simp [naturalTransformationCylinderFunctor, Functor.uncurry, ComposableArrows.mk₁]
      · exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) hij |>.elim
      · simp [naturalTransformationCylinderFunctor, Functor.uncurry, ComposableArrows.mk₁]
  have hc : naturalTransformationNerveCylinder (𝟙 F) =
      fst (nerve C) Δ[1] ≫ nerveMap F := by
    ext n z : 4
    change _ ⋙ naturalTransformationCylinderFunctor (𝟙 F) = _
    rw [he]
    rfl
  change SSet.toTop.map (naturalTransformationNerveCylinder (𝟙 F))
    ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) = _
  rw [hc, SSet.toTop.map_comp, TopCat.comp_app]
  have hp := congrArg Prod.fst (ConcreteCategory.congr_hom
    (realizationCylinderIso (nerve C)).inv_hom_id (x, ULift.up t))
  exact congrArg (classifyingSpaceMap F) hp
/-- The family in ordinary barycentric simplex coordinates. -/
def functorChainBarycentric {n : ℕ} (A : ComposableArrows (C ⥤ D) n) :
    C(ClassifyingSpace C × StdSimplex ℝ (Fin (n + 1)), ClassifyingSpace D) where
  toFun z := functorChainRealization A (z.1, (SimplexCategory.toTopHomeo ⦋n⦌).symm z.2)
  continuous_toFun := by fun_prop

private theorem simplexRealization_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (z : StdSimplex ℝ (Fin (m + 1))) :
    SSet.toTop.map (SSet.stdSimplex.map f) ((SimplexCategory.toTopHomeo ⦋m⦌).symm z) =
      (SimplexCategory.toTopHomeo ⦋n⦌).symm (StdSimplex.map f.toOrderHom z) := by
  apply (SimplexCategory.toTopHomeo ⦋n⦌).injective
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  simp
  rfl

/-- The affine edge between two chosen triangle vertices. -/
def triangleEdge (i j : Fin 3) (t : unitInterval) : StdSimplex ℝ (Fin 3) :=
  StdSimplex.duple i j (unitInterval.nonneg (unitInterval.symm t))
    (unitInterval.nonneg t) (by simp)

@[fun_prop] theorem continuous_triangleEdge (i j : Fin 3) : Continuous (triangleEdge i j) :=
  StdSimplex.continuous_duple i j

@[simp] theorem triangleEdge_zero (i j : Fin 3) : triangleEdge i j 0 = StdSimplex.single i := by
  apply StdSimplex.ext
  simp [triangleEdge, StdSimplex.duple]
@[simp] theorem triangleEdge_one (i j : Fin 3) : triangleEdge i j 1 = StdSimplex.single j := by
  apply StdSimplex.ext
  simp [triangleEdge, StdSimplex.duple]

private theorem triangleEdge_face (i : Fin 3) (t : unitInterval) :
    triangleEdge (i.succAbove 0) (i.succAbove 1) t =
      StdSimplex.map (SimplexCategory.δ i).toOrderHom (StdSimplex.homeomorphI.symm t) := by
  change _ = StdSimplex.map (SimplexCategory.δ i).toOrderHom
    (StdSimplex.duple 0 1 (sub_nonneg.mpr t.2.2) t.2.1 (by ring))
  rw [StdSimplex.map_duple]
  rfl

/-- The barycentric family restricts on each edge to its transformation. -/
theorem functorChainBarycentric_two_face {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (i : Fin 3) (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainBarycentric (ComposableArrows.mk₂ α β)
      (x, triangleEdge (i.succAbove 0) (i.succAbove 1) t) =
    functorChainRealization ((nerve (C ⥤ D)).δ i (ComposableArrows.mk₂ α β))
      (x, realizationInterval t) := by
  change functorChainRealization _
    (x, (SimplexCategory.toTopHomeo ⦋2⦌).symm _) = _
  rw [triangleEdge_face, ← simplexRealization_map]
  exact functorChainRealization_two_face α β i x t

/-- Fill the triangle between the inverse arrow and the reversed original arrow.
The other endpoint moves only along their composite edge. -/
def inverseTriangleParameter (s t : unitInterval) : StdSimplex ℝ (Fin 3) :=
  convexCombPair (R := ℝ) (unitInterval.symm s) s
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
    (triangleEdge 1 2 t) (triangleEdge 0 1 (unitInterval.symm t))

@[fun_prop] theorem continuous_inverseTriangleParameter :
    Continuous (fun z : unitInterval × unitInterval ↦ inverseTriangleParameter z.1 z.2) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff]
  unfold Function.comp
  refine continuous_pi (fun i ↦ ?_)
  simp only [inverseTriangleParameter, StdSimplex.weights_convexCombPair,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    unitInterval.coe_symm_eq]
  simp only [triangleEdge, StdSimplex.duple, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> fun_prop

@[simp] theorem inverseTriangleParameter_zero (t : unitInterval) :
    inverseTriangleParameter 0 t = triangleEdge 1 2 t := by simp [inverseTriangleParameter]
@[simp] theorem inverseTriangleParameter_one (t : unitInterval) :
    inverseTriangleParameter 1 t = triangleEdge 0 1 (unitInterval.symm t) := by
  simp [inverseTriangleParameter]
@[simp] theorem inverseTriangleParameter_source (s : unitInterval) :
    inverseTriangleParameter s 0 = StdSimplex.single 1 := by simp [inverseTriangleParameter]
@[simp] theorem inverseTriangleParameter_target (s : unitInterval) :
    inverseTriangleParameter s 1 = triangleEdge 0 2 (unitInterval.symm s) := by
  apply StdSimplex.ext
  simp [inverseTriangleParameter, triangleEdge, StdSimplex.weights_convexCombPair,
    StdSimplex.duple, add_comm]
theorem functorChainBarycentric_two_first {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainBarycentric (ComposableArrows.mk₂ α β) (x, triangleEdge 0 1 t) =
      classifyingSpaceNaturalTransformationHomotopy α (t, x) := by
  have h := functorChainBarycentric_two_face α β 2 x t
  rw [nerve.δ₂_mk₂_eq, functorChainRealization_one] at h
  exact h

theorem functorChainBarycentric_two_second {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainBarycentric (ComposableArrows.mk₂ α β) (x, triangleEdge 1 2 t) =
      classifyingSpaceNaturalTransformationHomotopy β (t, x) := by
  have h := functorChainBarycentric_two_face α β 0 x t
  rw [nerve.δ₀_mk₂_eq, functorChainRealization_one] at h
  exact h

theorem functorChainBarycentric_two_composite {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainBarycentric (ComposableArrows.mk₂ α β) (x, triangleEdge 0 2 t) =
      classifyingSpaceNaturalTransformationHomotopy (α ≫ β) (t, x) := by
  have h := functorChainBarycentric_two_face α β 1 x t
  rw [nerve.δ₁_mk₂_eq, functorChainRealization_one] at h
  exact h

/-- The homotopy from an inverse natural isomorphism agrees with the reversed
forward homotopy through an actual two-parameter homotopy, relative to both
ends of the path parameter. It is jointly continuous in every source point. -/
def naturalIsoInverseHomotopy {F G : C ⥤ D} (e : F ≅ G) :
    (classifyingSpaceNaturalTransformationHomotopy e.inv).toContinuousMap.HomotopyRel
      (classifyingSpaceNaturalTransformationHomotopy e.hom).symm.toContinuousMap
      (fun z : unitInterval × ClassifyingSpace C ↦ z.1 = 0 ∨ z.1 = 1) where
  toFun z := functorChainBarycentric (ComposableArrows.mk₂ e.hom e.inv)
    (z.2.2, inverseTriangleParameter z.1 z.2.1)
  continuous_toFun := by fun_prop
  map_zero_left z := by
    change functorChainBarycentric _ (z.2, inverseTriangleParameter 0 z.1) = _
    rw [inverseTriangleParameter_zero, functorChainBarycentric_two_second]
    rfl
  map_one_left z := by
    change functorChainBarycentric _ (z.2, inverseTriangleParameter 1 z.1) = _
    rw [inverseTriangleParameter_one, functorChainBarycentric_two_first]
    rfl
  prop' s z hz := by
    rcases z with ⟨t, x⟩
    rcases hz with ht | ht
    · change t = 0 at ht
      subst t
      change functorChainBarycentric _ (x, inverseTriangleParameter s 0) = _
      rw [inverseTriangleParameter_source, ← triangleEdge_zero 1 2,
        functorChainBarycentric_two_second]
      rfl
    · change t = 1 at ht
      subst t
      change functorChainBarycentric _ (x, inverseTriangleParameter s 1) = _
      rw [inverseTriangleParameter_target, functorChainBarycentric_two_composite,
        e.hom_inv_id, classifyingHomotopy_id]
      exact (classifyingSpaceNaturalTransformationHomotopy e.inv).map_one_left x |>.symm

/-- Pathwise form of the inverse-isomorphism coherence, with endpoints fixed. -/
def naturalIsoInversePathHomotopy {F G : C ⥤ D} (e : F ≅ G) (x : ClassifyingSpace C) :
    ((classifyingSpaceNaturalTransformationHomotopy e.inv).evalAt x).Homotopy
      ((classifyingSpaceNaturalTransformationHomotopy e.hom).evalAt x).symm where
  toFun z := naturalIsoInverseHomotopy e (z.1, (z.2, x))
  continuous_toFun := by fun_prop
  map_zero_left t := (naturalIsoInverseHomotopy e).map_zero_left (t, x)
  map_one_left t := (naturalIsoInverseHomotopy e).map_one_left (t, x)
  prop' s t ht := (naturalIsoInverseHomotopy e).prop' s (t, x) (by
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr (Set.mem_singleton_iff.mp ht))
/-- Endpoint-relative homotopies between nullhomotopies induce homotopies
between their actual path-space fiber lifts. -/
def fiberLiftNullhomotopyHomotopy {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(A, X)) (y : Y)
    (H K : (f.comp g).Homotopy (ContinuousMap.const A y))
    (R : H.toContinuousMap.HomotopyRel K.toContinuousMap
      (fun z : unitInterval × A ↦ z.1 = 0 ∨ z.1 = 1)) :
    (HomotopyFiber.lift f y g H).Homotopy (HomotopyFiber.lift f y g K) where
  toFun z := ⟨(g z.2, ⟨fun t ↦ R (z.1, (t, z.2)), by fun_prop⟩),
    (R.prop' z.1 (0, z.2) (Or.inl rfl)).trans (H.map_zero_left z.2),
    (R.prop' z.1 (1, z.2) (Or.inr rfl)).trans (H.map_one_left z.2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (unitInterval × A) × unitInterval ↦ R (z.1.1, (z.2, z.1.2)))
      fun_prop
  map_zero_left x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact R.map_zero_left (t, x)
  map_one_left x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact R.map_one_left (t, x)

/-- A natural isomorphism to a constant functor gives the direct nullhomotopy. -/
def naturalIsoNullhomotopy {A : Type u} [SmallCategory A]
    (P : A ⥤ C) (F : C ⥤ D) (d : D) (e : P ⋙ F ≅ (Functor.const A).obj d) :
    ((classifyingSpaceMap F).hom.comp (classifyingSpaceMap P).hom).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint d)) :=
  (classifyingSpaceNaturalTransformationHomotopy e.hom).cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
    (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- The inverse natural isomorphism gives a second, reversed nullhomotopy. -/
def naturalIsoInverseNullhomotopy {A : Type u} [SmallCategory A]
    (P : A ⥤ C) (F : C ⥤ D) (d : D) (e : P ⋙ F ≅ (Functor.const A).obj d) :
    ((classifyingSpaceMap F).hom.comp (classifyingSpaceMap P).hom).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint d)) :=
  (classifyingSpaceNaturalTransformationHomotopy e.inv).symm.cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
    (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- Forward and reversed-inverse natural isomorphisms define canonically
homotopic actual fiber maps. This comparison fixes the source coordinate. -/
def naturalIsoFiberLiftHomotopy {A : Type u} [SmallCategory A]
    (P : A ⥤ C) (F : C ⥤ D) (d : D) (e : P ⋙ F ≅ (Functor.const A).obj d) :
    (HomotopyFiber.lift (classifyingSpaceMap F).hom (classifyingSpacePoint d)
      (classifyingSpaceMap P).hom (naturalIsoNullhomotopy P F d e)).Homotopy
    (HomotopyFiber.lift (classifyingSpaceMap F).hom (classifyingSpacePoint d)
      (classifyingSpaceMap P).hom (naturalIsoInverseNullhomotopy P F d e)) :=
  fiberLiftNullhomotopyHomotopy _ _ _ _ _ (naturalIsoInverseHomotopy e.symm)
@[simp] theorem naturalIsoFiberLiftHomotopy_projection {A : Type u} [SmallCategory A]
    (P : A ⥤ C) (F : C ⥤ D) (d : D) (e : P ⋙ F ≅ (Functor.const A).obj d)
    (s : unitInterval) (x : ClassifyingSpace A) :
    (naturalIsoFiberLiftHomotopy P F d e (s, x)).1.1 = classifyingSpaceMap P x := rfl

end Quillen.TheoremB
