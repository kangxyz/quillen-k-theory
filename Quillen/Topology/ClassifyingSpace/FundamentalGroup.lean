/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.ClassifyingSpace.Groupoid
public import Quillen.Topology.ClassifyingSpace.DiscretePoints
public import Quillen.CategoryTheory.TheoremB.Naturality
public import Quillen.KTheory.FundamentalGroup.Basic

/-!
# The original groupoid fundamental-group comparison

The actual point-comma comparison in degree zero identifies original arrows
with components of the genuine loop space. Its path-preserving fiber
homeomorphism retains each realized arrow. The original map on vertex
endomorphisms is therefore bijective and gives a multiplicative equivalence.
Actual nerve lifts preserve the arrow paths and extend the result to independent
category universes, including noncommutative groups in every universe.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace Quillen.GroupoidClassifying
variable {C : Type u} [SmallCategory C] (c : C)

lemma comma_vertex_zeroPointClass_bijective :
    Function.Bijective (fun g : c ⟶ c ↦
      zeroPointClass
        (classifyingSpacePoint (CostructuredArrow.mk (S := pointFunctor c)
          (Y := Discrete.mk PUnit.unit) (𝟙 c)))
        (classifyingSpacePoint (CostructuredArrow.mk (S := pointFunctor c)
          (Y := Discrete.mk PUnit.unit) g))) := by
  let x₀ := CostructuredArrow.mk (S := pointFunctor c) (Y := Discrete.mk PUnit.unit) (𝟙 c)
  let e := equivalenceClassifyingHomotopyEquiv (pointCommaEquivalence c c)
  have h₀ : e.toFun (classifyingSpacePoint x₀) = classifyingSpacePoint (Discrete.mk (𝟙 c)) :=
    classifyingSpaceMap_point (pointCommaProjection c c) x₀
  let f := homotopyGroupMap (N := Fin 0) e.toFun h₀
  have hf : Function.Bijective f := homotopyGroupMap_bijective_of_homotopyEquiv e h₀ 0
  have he (g : c ⟶ c) : f (zeroPointClass (classifyingSpacePoint x₀)
      (classifyingSpacePoint (CostructuredArrow.mk (S := pointFunctor c)
        (Y := Discrete.mk PUnit.unit) g))) =
      zeroPointClass (classifyingSpacePoint (Discrete.mk (𝟙 c)))
        (classifyingSpacePoint (Discrete.mk g)) := by
    dsimp only [f]
    rw [homotopyGroupMap_zeroPointClass]
    exact congrArg (zeroPointClass _) (classifyingSpaceMap_point (pointCommaProjection c c) _)
  have hg := discrete_vertex_zeroPointClass_bijective (c ⟶ c) (𝟙 c)
  constructor
  · intro a b h
    apply hg.injective
    exact (he a).symm.trans ((congrArg f h).trans (he b))
  · intro b
    obtain ⟨g, h⟩ := hg.surjective (f b)
    exact ⟨g, hf.injective ((he g).trans h)⟩

lemma pointSpace_subsingleton : Subsingleton (ClassifyingSpace (Discrete PUnit.{u+1})) := by
  let : Subsingleton (TopCat.discrete.obj PUnit.{u+1}) := inferInstanceAs (Subsingleton PUnit.{u+1})
  exact (TopCat.homeoOfIso (discreteClassifyingIso PUnit.{u+1})).injective.subsingleton

lemma pointMap_constant (z : ClassifyingSpace (Discrete PUnit.{u + 1})) :
    classifyingSpaceMap (pointFunctor c) z = classifyingSpacePoint c := by
  rw [show pointFunctor c = (Functor.const _).obj c from rfl, classifyingSpaceMap_const_direct]
  rfl

/-- Original point-inclusion fibers are their original loop spaces, with unchanged paths. -/
def pointFiberLoopHomeomorph :
    HomotopyFiber (classifyingSpaceMap (pointFunctor c)).hom (classifyingSpacePoint c) ≃ₜ
      Path (classifyingSpacePoint c) (classifyingSpacePoint c) where
  toFun z := {
    toContinuousMap := z.1.2
    source' := z.2.1.trans (pointMap_constant c z.1.1)
    target' := z.2.2 }
  invFun γ := HomotopyFiber.loopInclusion _ _
    (classifyingSpacePoint (Discrete.mk PUnit.unit))
    (classifyingSpaceMap_point (pointFunctor c) _) γ
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · let := pointSpace_subsingleton
      exact Subsingleton.elim _ _
    · rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : HomotopyFiber (classifyingSpaceMap (pointFunctor c)).hom
      (classifyingSpacePoint c) × unitInterval ↦ z.1.1.2 z.2)
    fun_prop
  continuous_invFun := (HomotopyFiber.loopInclusion _ _ _ _).continuous

lemma pointFiberLoopHomeomorph_basepoint :
    pointFiberLoopHomeomorph c
      (HomotopyFiber.basepoint (classifyingSpaceMap (pointFunctor c)).hom
        (classifyingSpacePoint c) (classifyingSpacePoint (Discrete.mk PUnit.unit))
        (classifyingSpaceMap_point (pointFunctor c) _)) = Path.refl _ := rfl

lemma pointFiberLoopHomeomorph_vertex (g : c ⟶ c) :
    pointFiberLoopHomeomorph c (TheoremB.fiberComparison (pointFunctor c) c
      (classifyingSpacePoint (CostructuredArrow.mk (S := pointFunctor c)
        (Y := Discrete.mk PUnit.unit) g))) = classifyingSpacePath g := by
  ext t
  simpa only [TheoremB.fiberComparison_path] using
    TheoremB.commaNullhomotopy_vertex (pointFunctor c) c _ t

end Quillen.GroupoidClassifying

namespace Quillen.GroupoidClassifying
variable {C : Type u} [SmallCategory C] [IsGroupoid C] (c : C)

/-- Original categorical loops biject onto actual path components of the original loop space. -/
lemma arrow_zeroLoopClass_bijective :
    Function.Bijective (fun g : c ⟶ c ↦
      zeroPointClass (Path.refl (classifyingSpacePoint c)) (classifyingSpacePath g)) := by
  let pt : Discrete PUnit.{u+1} := .mk PUnit.unit
  let F := pointFunctor c
  let x₀ := CostructuredArrow.mk (S := F) (Y := pt) (𝟙 c)
  let k := homotopyGroupMap (N := Fin 0) (TheoremB.fiberComparison F c)
    (TheoremB.fiberComparison_identity F pt)
  have hk : Function.Bijective k := TheoremB.fiberComparison_bijective F
    (TheoremB.transitionHomotopyEquivalences_of_groupoid F) pt 0
  let e := pointFiberLoopHomeomorph c
  let l := homotopyGroupMap (N := Fin 0) e.toHomotopyEquiv.toFun
    (pointFiberLoopHomeomorph_basepoint c)
  have hl : Function.Bijective l := homotopyGroupMap_bijective_of_homotopyEquiv
    e.toHomotopyEquiv (pointFiberLoopHomeomorph_basepoint c) 0
  let a := fun g : c ⟶ c ↦ zeroPointClass (classifyingSpacePoint x₀)
    (classifyingSpacePoint (CostructuredArrow.mk (S := F) (Y := pt) g))
  have ha : Function.Bijective a := comma_vertex_zeroPointClass_bijective c
  have he : l ∘ k ∘ a = fun g : c ⟶ c ↦
      zeroPointClass (Path.refl (classifyingSpacePoint c)) (classifyingSpacePath g) := by
    funext g
    dsimp only [Function.comp_def, k, l, a]
    change zeroPointClass (Path.refl (classifyingSpacePoint c))
      (pointFiberLoopHomeomorph c (TheoremB.fiberComparison (pointFunctor c) c
        (classifyingSpacePoint (CostructuredArrow.mk (S := pointFunctor c)
          (Y := Discrete.mk PUnit.unit) g)))) = _
    exact congrArg (zeroPointClass _) (pointFiberLoopHomeomorph_vertex c g)
  exact he ▸ hl.comp (hk.comp ha)

end Quillen.GroupoidClassifying

namespace Quillen
variable {X : Type u} [TopologicalSpace X] (x : X)

/-- Identify the fundamental group at `x` with the zeroth homotopy set of
the loop space `Path x x` based at the constant loop, using the first
homotopy-group comparison and the loop-shift equivalence. -/
def fundamentalGroupLoopComponentEquiv :
    FundamentalGroup X x ≃ HomotopyGroup.Pi 0 (Path x x) (Path.refl x) :=
  (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)).symm.trans (loopShiftEquiv 0)

lemma fundamentalGroupLoopComponentEquiv_path (γ : Path x x) :
    fundamentalGroupLoopComponentEquiv x (Path.Homotopic.Quotient.mk γ) =
      zeroPointClass (Path.refl x) γ := by
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro z
  rfl

end Quillen

namespace Quillen.GroupoidClassifying
variable {C : Type u} [SmallCategory C] [IsGroupoid C] (c : C)

/-- The original realized-arrow map computes the genuine fundamental group. -/
theorem fundamentalGroupMap_bijective :
    Function.Bijective ((classifyingFundamentalGroupoidFunctor C).mapEnd c) := by
  have h := arrow_zeroLoopClass_bijective c
  let e := fundamentalGroupLoopComponentEquiv (classifyingSpacePoint c)
  have he (g : c ⟶ c) : e ((classifyingFundamentalGroupoidFunctor C).mapEnd c g) =
      zeroPointClass (Path.refl (classifyingSpacePoint c)) (classifyingSpacePath g) :=
    fundamentalGroupLoopComponentEquiv_path _ _
  constructor
  · intro a b hab
    apply h.injective
    exact (he a).symm.trans ((congrArg e hab).trans (he b))
  · intro z
    obtain ⟨g, hg⟩ := h.surjective (e z)
    exact ⟨g, e.injective ((he g).trans hg)⟩

end Quillen.GroupoidClassifying

namespace Quillen
private lemma fundamental_mapOfEq_bijective_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {x : X} {y : Y} (h : e x = y) :
    Function.Bijective (FundamentalGroup.mapOfEq e.toHomotopyEquiv.toFun h) := by
  let a := HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)
  let b := HomotopyGroup.pi1MulEquivFundamentalGroup (X := Y) (x := y)
  let f := homotopyGroupMap (N := Fin 1) e.toHomotopyEquiv.toFun h
  let g := FundamentalGroup.mapOfEq e.toHomotopyEquiv.toFun h
  have hf : Function.Bijective f :=
    homotopyGroupMap_bijective_of_homotopyEquiv e.toHomotopyEquiv h 1
  have hn (z) : b (f z) = g (a z) := by
    induction z using Quotient.inductionOn with | _ p =>
      rw [FundamentalGroup.mapOfEq_apply]
      change (⟦genLoopEquivOfUnique (Fin 1) (genLoopPostcomp e.toHomotopyEquiv.toFun h p)⟧ :
          FundamentalGroup Y y) =
        ⟦((genLoopEquivOfUnique (Fin 1) p).map e.continuous).cast h.symm h.symm⟧
      congr 1
  constructor
  · intro z w heq
    obtain ⟨z, rfl⟩ := a.surjective z
    obtain ⟨w, rfl⟩ := a.surjective w
    exact congrArg a (hf.injective (b.injective ((hn z).trans (heq.trans (hn w).symm))))
  · intro z
    obtain ⟨w, hw⟩ := hf.surjective (b.symm z)
    exact ⟨a w, (hn w).symm.trans ((congrArg b hw).trans (b.apply_symm_apply z))⟩
end Quillen

namespace Quillen.GroupoidClassifying
variable {C : Type u} [Category.{v} C]

lemma asSmallClassifyingHomeomorph_path {c d : C} (g : c ⟶ d) :
    ((classifyingSpacePath g).map (asSmallClassifyingHomeomorph C).continuous).cast
      (asSmallClassifyingHomeomorph_point C c).symm
      (asSmallClassifyingHomeomorph_point C d).symm =
      classifyingSpacePath (AsSmall.up.map g : AsSmall.up.obj c ⟶ AsSmall.up.obj d) := by
  ext t
  change SSet.toTop.map (asSmallNerveIso C).hom
    (realizationEdgePath (CategoryTheory.nerve.edgeMk g) t) = _
  rw [realizationEdgePath_naturality_apply]
  simp only [realizationEdgePath_apply, SSet.Edge.map_edge, CategoryTheory.nerve.edgeMk_edge]
  have he : (asSmallNerveIso C).hom.app (op ⦋1⦌) (ComposableArrows.mk₁ g) =
      ComposableArrows.mk₁ (AsSmall.up.map g) :=
    ComposableArrows.ext₁ rfl rfl (by simp [asSmallNerveIso])
  rw [he]
  rfl

lemma asSmall_fundamental_map (c : C) (g : c ⟶ c) :
    FundamentalGroup.mapOfEq (asSmallClassifyingHomeomorph C).toHomotopyEquiv.toFun
      (asSmallClassifyingHomeomorph_point C c)
      ((classifyingFundamentalGroupoidFunctor C).mapEnd c g) =
      (classifyingFundamentalGroupoidFunctor (AsSmall.{0} C)).mapEnd (AsSmall.up.obj c)
        (AsSmall.up.map g) := by
  rw [FundamentalGroup.mapOfEq_apply]
  change (Path.Homotopic.Quotient.mk _ : FundamentalGroup _ _) = Path.Homotopic.Quotient.mk _
  exact congrArg Path.Homotopic.Quotient.mk (asSmallClassifyingHomeomorph_path g)

/-- The original arrow-to-fundamental-group map is bijective in independent category universes. -/
theorem fundamentalGroupMap_bijective_general [IsGroupoid C] (c : C) :
    Function.Bijective ((classifyingFundamentalGroupoidFunctor C).mapEnd c) := by
  let : (AsSmall.down : AsSmall.{0} C ⥤ C).IsEquivalence :=
    (AsSmall.equiv : C ≌ AsSmall.{0} C).isEquivalence_inverse
  let : IsGroupoid (AsSmall.{0} C) := isGroupoid_of_reflects_iso AsSmall.down
  have ht := fundamentalGroupMap_bijective (AsSmall.up.obj c)
  let e := asSmallClassifyingHomeomorph C
  let f := FundamentalGroup.mapOfEq e.toHomotopyEquiv.toFun (asSmallClassifyingHomeomorph_point C c)
  have hf : Function.Bijective f := fundamental_mapOfEq_bijective_of_homeomorph e _
  constructor
  · intro a b h
    have hu : AsSmall.up.map a = AsSmall.up.map b := ht.injective
      ((asSmall_fundamental_map c a).symm.trans ((congrArg f h).trans (asSmall_fundamental_map c
        b)))
    exact congrArg AsSmall.down.map hu
  · intro z
    obtain ⟨g, hg⟩ := ht.surjective (f z)
    refine ⟨AsSmall.down.map g, hf.injective ?_⟩
    exact (asSmall_fundamental_map c (AsSmall.down.map g)).trans hg

/-- The actual realized-arrow homomorphism is a multiplicative equivalence. -/
def fundamentalGroupEquiv [IsGroupoid C] (c : C) :
    End c ≃* FundamentalGroup (ClassifyingSpace C) (classifyingSpacePoint c) :=
  MulEquiv.ofBijective ((classifyingFundamentalGroupoidFunctor C).mapEnd c)
    (fundamentalGroupMap_bijective_general c)

@[simp] lemma fundamentalGroupEquiv_apply [IsGroupoid C] (c : C) (g : End c) :
    fundamentalGroupEquiv c g = Path.Homotopic.Quotient.mk (classifyingSpacePath g) := rfl

/-- The original one-object group nerve has its original group as fundamental group. -/
def singleObjFundamentalGroupEquiv (G : Type u) [Group G] :
    G ≃* FundamentalGroup (ClassifyingSpace (SingleObj G)) (classifyingSpacePoint
      (SingleObj.star G)) :=
  (SingleObj.toEnd G).trans (fundamentalGroupEquiv (SingleObj.star G))

end Quillen.GroupoidClassifying

namespace Quillen.GroupoidClassifying
/-- Original group elements give their original homotopy-theoretic degree-one loops. -/
def singleObjPiOneEquiv (G : Type u) [Group G] :
    G ≃* HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj G))
      (classifyingSpacePoint (SingleObj.star G)) :=
  (singleObjFundamentalGroupEquiv G).trans HomotopyGroup.pi1MulEquivFundamentalGroup.symm

@[simp] lemma singleObjPiOneEquiv_apply (G : Type u) [Group G] (g : G) :
    singleObjPiOneEquiv G g = HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (Path.Homotopic.Quotient.mk (classifyingSpacePath (SingleObj.toEnd G g))) := rfl
end Quillen.GroupoidClassifying
