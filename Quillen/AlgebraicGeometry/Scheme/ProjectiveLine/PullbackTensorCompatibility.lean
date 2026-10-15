/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.Tensor.Symmetry
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.OpenBaseChange
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological

/-!
# Native pullback-tensor comparison for the original tautological line

For every scheme morphism into the original two-chart projective line and every module sheaf,
pullback commutes with tensor by the actual tautological line. The forward arrow is the mate of
the original two adjunction units and tensor-pushforward map. Its naturality, unit equation,
section formula, braiding square and cartesian open-restriction square retain the original maps.
The inverse-image chart cover reduces invertibility to the original unit comparison. The other
module sheaf is arbitrary, and the scheme morphism has no flatness hypothesis.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original adjunction and tensor-pushforward comparison determine the forward tensor mate. -/
def modulePullbackTensorMap (M N : Y.Modules) :
    (pullback f).obj ((moduleTensorLeftFunctor Y M).obj N) ⟶
      (moduleTensorLeftFunctor X ((pullback f).obj M)).obj ((pullback f).obj N) :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm
    ((moduleTensorLeftFunctor Y M).map ((pullbackPushforwardAdjunction f).unit.app N) ≫
      projectionFormulaMap f M ((pullback f).obj N))

/-- The forward mate retains the original projection-formula map and second adjunction unit. -/
lemma modulePullbackTensorMap_homEquiv (M N : Y.Modules) :
    (pullbackPushforwardAdjunction f).homEquiv _ _ (modulePullbackTensorMap f M N) =
      (moduleTensorLeftFunctor Y M).map ((pullbackPushforwardAdjunction f).unit.app N) ≫
        projectionFormulaMap f M ((pullback f).obj N) :=
  Equiv.apply_symm_apply _ _

/-- Equivalently, its adjoint is exactly both original units followed by tensor pushforward. -/
lemma modulePullbackTensorMap_homEquiv_eq (M N : Y.Modules) :
    (pullbackPushforwardAdjunction f).homEquiv _ _ (modulePullbackTensorMap f M N) =
      (moduleTensorCoefficientMap Y ((pullbackPushforwardAdjunction f).unit.app M)).app N ≫
        (moduleTensorLeftFunctor Y ((pushforward f).obj ((pullback f).obj M))).map
          ((pullbackPushforwardAdjunction f).unit.app N) ≫
            modulePushforwardTensorMap f ((pullback f).obj M) ((pullback f).obj N) := by
  rw [modulePullbackTensorMap_homEquiv, projectionFormulaMap, ← Category.assoc]
  have hn := (moduleTensorCoefficientMap Y
    ((pullbackPushforwardAdjunction f).unit.app M)).naturality
    ((pullbackPushforwardAdjunction f).unit.app N)
  change (moduleTensorLeftFunctor Y M).map ((pullbackPushforwardAdjunction f).unit.app N) ≫
      (moduleTensorCoefficientMap Y ((pullbackPushforwardAdjunction f).unit.app M)).app
        ((pushforward f).obj ((pullback f).obj N)) =
    (moduleTensorCoefficientMap Y ((pullbackPushforwardAdjunction f).unit.app M)).app N ≫
      (moduleTensorLeftFunctor Y ((pushforward f).obj ((pullback f).obj M))).map
        ((pullbackPushforwardAdjunction f).unit.app N) at hn
  rw [hn, Category.assoc]

/-- The canonical mate is natural in the original second module arrows. -/
lemma modulePullbackTensorMap_naturality_right (M : Y.Modules) {N N' : Y.Modules}
    (g : N ⟶ N') :
    (pullback f).map ((moduleTensorLeftFunctor Y M).map g) ≫
      modulePullbackTensorMap f M N' =
    modulePullbackTensorMap f M N ≫
      (moduleTensorLeftFunctor X ((pullback f).obj M)).map ((pullback f).map g) := by
  let A := pullbackPushforwardAdjunction f
  apply (A.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    modulePullbackTensorMap_homEquiv, modulePullbackTensorMap_homEquiv]
  have hu := A.unit.naturality g
  change g ≫ A.unit.app N' = A.unit.app N ≫ (pushforward f).map ((pullback f).map g) at hu
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc]
  rw [projectionFormulaMap_naturality f M ((pullback f).map g), Category.assoc]

/-- The canonical mate is natural in the original first module arrows. -/
lemma modulePullbackTensorMap_naturality_left {M M' : Y.Modules} (g : M ⟶ M')
    (N : Y.Modules) :
    (pullback f).map ((moduleTensorCoefficientMap Y g).app N) ≫
      modulePullbackTensorMap f M' N =
    modulePullbackTensorMap f M N ≫
      (moduleTensorCoefficientMap X ((pullback f).map g)).app ((pullback f).obj N) := by
  let A := pullbackPushforwardAdjunction f
  apply (A.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    modulePullbackTensorMap_homEquiv, modulePullbackTensorMap_homEquiv]
  have hc := (moduleTensorCoefficientMap Y g).naturality (A.unit.app N)
  change (moduleTensorLeftFunctor Y M).map (A.unit.app N) ≫
      (moduleTensorCoefficientMap Y g).app ((pushforward f).obj ((pullback f).obj N)) =
    (moduleTensorCoefficientMap Y g).app N ≫
      (moduleTensorLeftFunctor Y M').map (A.unit.app N) at hc
  rw [← Category.assoc, ← hc, Category.assoc]
  have hn := (projectionFormulaNatTrans f ((pullback f).obj N)).naturality g
  change (moduleTensorCoefficientMap Y g).app ((pushforward f).obj ((pullback f).obj N)) ≫
      projectionFormulaMap f M' ((pullback f).obj N) =
    projectionFormulaMap f M ((pullback f).obj N) ≫
      (pushforward f).map
        ((moduleTensorCoefficientMap X ((pullback f).map g)).app ((pullback f).obj N)) at hn
  rw [hn, Category.assoc]

/-- The native mate retains the original pullback-unit and tensor-left-unit comparison. -/
lemma modulePullbackTensorMap_leftUnit (N : Y.Modules) :
    modulePullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) N ≫
      (moduleTensorCoefficientMap X (pullbackUnitIso f).hom).app ((pullback f).obj N) ≫
        (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).hom.app ((pullback f).obj N) =
      (pullback f).map ((SheafOfModulesOfCommRing.tensorLeftUnitIso Y.sheaf).hom.app N) := by
  let A := pullbackPushforwardAdjunction f
  let e : (moduleTensorLeftFunctor X ((pullback f).obj
      (SheafOfModules.unit Y.ringCatSheaf))).obj ((pullback f).obj N) ≅
        (pullback f).obj N :=
    ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso (pullbackUnitIso f)).app
      ((pullback f).obj N) ≪≫
        (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app ((pullback f).obj N)
  change modulePullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) N ≫ e.hom = _
  apply (A.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right,
    modulePullbackTensorMap_homEquiv f (SheafOfModules.unit Y.ringCatSheaf) N, Category.assoc]
  change (moduleTensorLeftFunctor Y (SheafOfModules.unit Y.ringCatSheaf)).map (A.unit.app N) ≫
    (projectionFormulaMap f (SheafOfModules.unit Y.ringCatSheaf) ((pullback f).obj N) ≫
      (pushforward f).map
        ((moduleTensorCoefficientMap X (pullbackUnitIso f).hom).app ((pullback f).obj N) ≫
          (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).hom.app ((pullback f).obj N))) = _
  have hp := projectionFormulaMap_unit f ((pullback f).obj N)
  change projectionFormulaMap f (SheafOfModules.unit Y.ringCatSheaf) ((pullback f).obj N) ≫
    (pushforward f).map
      ((moduleTensorCoefficientMap X (pullbackUnitIso f).hom).app ((pullback f).obj N) ≫
        (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).hom.app ((pullback f).obj N)) =
      (SheafOfModulesOfCommRing.tensorLeftUnitIso Y.sheaf).hom.app
        ((pushforward f).obj ((pullback f).obj N)) at hp
  rw [hp]
  have h := (SheafOfModulesOfCommRing.tensorLeftUnitIso Y.sheaf).hom.naturality
    (A.unit.app N)
  change (moduleTensorLeftFunctor Y (SheafOfModules.unit Y.ringCatSheaf)).map
      (A.unit.app N) ≫ (SheafOfModulesOfCommRing.tensorLeftUnitIso Y.sheaf).hom.app
        ((pushforward f).obj ((pullback f).obj N)) =
    (SheafOfModulesOfCommRing.tensorLeftUnitIso Y.sheaf).hom.app N ≫ A.unit.app N at h
  rw [h]
  rw [Adjunction.homEquiv_unit]
  exact A.unit.naturality ((SheafOfModulesOfCommRing.tensorLeftUnitIso Y.sheaf).hom.app N)

/-- The canonical mate is invertible when its first module is the original structure module. -/
instance modulePullbackTensorMap_leftUnit_isIso (N : Y.Modules) :
    IsIso (modulePullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) N) := by
  let e : (moduleTensorLeftFunctor X ((pullback f).obj
      (SheafOfModules.unit Y.ringCatSheaf))).obj ((pullback f).obj N) ≅
        (pullback f).obj N :=
    ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso (pullbackUnitIso f)).app
      ((pullback f).obj N) ≪≫
        (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app ((pullback f).obj N)
  have : IsIso (modulePullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) N ≫ e.hom) := by
    change IsIso (modulePullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) N ≫
      (moduleTensorCoefficientMap X (pullbackUnitIso f).hom).app ((pullback f).obj N) ≫
        (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).hom.app ((pullback f).obj N))
    rw [modulePullbackTensorMap_leftUnit]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

section OpenBaseChange
variable {W U V Z : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (g : U ⟶ Z) (j : V ⟶ Z)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : CategoryTheory.IsPullback a b g j)

/-- The actual open-base-change mate retains the original transposition of every module arrow. -/
lemma pullbackTensor_open_homEquiv {M : Z.Modules} {N : U.Modules}
    (q : (pullback g).obj M ⟶ N) :
    (pullbackPushforwardAdjunction b).homEquiv _ _
      ((cartesianPullbackBaseChangeMate a b g j h).app M ≫ (restrictFunctor a).map q) =
      (restrictFunctor j).map ((pullbackPushforwardAdjunction g).homEquiv _ _ q) ≫
        (cartesianOpenBaseChange a b g j h).hom.app N := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← cartesianOpenBaseChange_pullback_unit a b g j h M, Category.assoc]
  have hn := (cartesianOpenBaseChange a b g j h).hom.naturality q
  change (restrictFunctor j).map ((pushforward g).map q) ≫
      (cartesianOpenBaseChange a b g j h).hom.app N =
    (cartesianOpenBaseChange a b g j h).hom.app ((pullback g).obj M) ≫
      (pushforward b).map ((restrictFunctor a).map q) at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp]
  rfl

/-- The tensor mate commutes with the actual cartesian open-restriction and pullback maps. -/
lemma modulePullbackTensorMap_openBaseChange (M N : Z.Modules) :
    (pullback b).map (tensorRestrictionIso j M N).hom ≫
      (cartesianPullbackBaseChangeMate a b g j h).app ((moduleTensorLeftFunctor Z M).obj N) ≫
        (restrictFunctor a).map (modulePullbackTensorMap g M N) =
    modulePullbackTensorMap b (M.restrict j) (N.restrict j) ≫
      (moduleTensorLeftFunctor W ((pullback b).obj (M.restrict j))).map
        ((cartesianPullbackBaseChangeMate a b g j h).app N) ≫
      (moduleTensorCoefficientMap W ((cartesianPullbackBaseChangeMate a b g j h).app M)).app
        (((pullback g).obj N).restrict a) ≫
      (tensorRestrictionIso a ((pullback g).obj M) ((pullback g).obj N)).hom := by
  let A := pullbackPushforwardAdjunction b
  let F := restrictFunctor j
  let T := moduleTensorLeftFunctor V (M.restrict j)
  let K := cartesianPullbackBaseChangeMate a b g j h
  let B := cartesianOpenBaseChange a b g j h
  apply (A.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, pullbackTensor_open_homEquiv a b g j h,
    modulePullbackTensorMap_homEquiv g M N]
  rw [Functor.map_comp, ← Category.assoc]
  have hn := (tensorRestrictionNatIso j M).hom.naturality
    ((pullbackPushforwardAdjunction g).unit.app N)
  change T.map (F.map ((pullbackPushforwardAdjunction g).unit.app N)) ≫
      (tensorRestrictionIso j M ((pushforward g).obj ((pullback g).obj N))).hom =
    (tensorRestrictionIso j M N).hom ≫
      F.map ((moduleTensorLeftFunctor Z M).map
        ((pullbackPushforwardAdjunction g).unit.app N)) at hn
  rw [← reassoc_of% hn]
  simp only [Category.assoc]
  rw [projectionFormulaMap_openBaseChange a b g j h M ((pullback g).obj N)]
  rw [← Category.assoc, ← Functor.map_comp,
    cartesianOpenBaseChange_pullback_unit a b g j h N, Functor.map_comp, Category.assoc]
  have hp := projectionFormulaMap_naturality b (M.restrict j) (K.app N)
  change T.map ((pushforward b).map (K.app N)) ≫
      projectionFormulaMap b (M.restrict j) (((pullback g).obj N).restrict a) =
    projectionFormulaMap b (M.restrict j) ((pullback b).obj (N.restrict j)) ≫
      (pushforward b).map
        ((moduleTensorLeftFunctor W ((pullback b).obj (M.restrict j))).map (K.app N)) at hp
  rw [reassoc_of% hp]
  rw [Adjunction.homEquiv_naturality_right,
    modulePullbackTensorMap_homEquiv b (M.restrict j) (N.restrict j)]
  simp only [Functor.map_comp, Category.assoc]
  rfl
end OpenBaseChange

/-- A specified actual unit trivialization proves invertibility of the canonical tensor mate. -/
lemma modulePullbackTensorMap_isIso_of_unitIso (M N : Y.Modules)
    (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) : IsIso (modulePullbackTensorMap f M N) := by
  let eY := ((SheafOfModulesOfCommRing.tensorFunctor Y.sheaf).mapIso e).app N
  let eX := ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso
    ((pullback f).mapIso e)).app ((pullback f).obj N)
  have hn : (pullback f).map eY.hom ≫
      modulePullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) N =
    modulePullbackTensorMap f M N ≫ eX.hom :=
      modulePullbackTensorMap_naturality_left f e.hom N
  have : IsIso (modulePullbackTensorMap f M N ≫ eX.hom) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ eX.hom

/-- Specified unit charts covering the first module prove invertibility on their inverse images. -/
lemma modulePullbackTensorMap_isIso_of_trivializingCover {ι : Type v}
    (V : ι → Scheme.{u}) (j : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hc : ∀ y : Y, ∃ i v, j i v = y) (L N : Y.Modules)
    (e : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (V i).ringCatSheaf) :
    IsIso (modulePullbackTensorMap f L N) := by
  let W (i : ι) := CategoryTheory.Limits.pullback f (j i)
  let a (i : ι) : W i ⟶ X := CategoryTheory.Limits.pullback.fst f (j i)
  let b (i : ι) : W i ⟶ V i := CategoryTheory.Limits.pullback.snd f (j i)
  have ha : ∀ i, IsOpenImmersion (a i) := fun i => inferInstanceAs
    (IsOpenImmersion (CategoryTheory.Limits.pullback.fst f (j i)))
  let := ha
  apply isIso_of_restrict_openCover W a
  · intro x
    obtain ⟨i, v, hv⟩ := hc (f x)
    have hx : x ∈ (a i).opensRange := by
      change x ∈ (CategoryTheory.Limits.pullback.fst f (j i)).opensRange
      rw [Scheme.Hom.opensRange_pullbackFst]
      exact ⟨v, hv⟩
    obtain ⟨w, hw⟩ := hx
    exact ⟨i, w, hw⟩
  · intro i
    let h : CategoryTheory.IsPullback (a i) (b i) f (j i) :=
      CategoryTheory.IsPullback.of_hasPullback _ _
    let K := cartesianPullbackBaseChangeMate (a i) (b i) f (j i) h
    let : IsIso K := inferInstanceAs
      (IsIso (cartesianPullbackBaseChangeMate (a i) (b i) f (j i) h))
    let : IsIso (modulePullbackTensorMap (b i) (L.restrict (j i)) (N.restrict (j i))) :=
      modulePullbackTensorMap_isIso_of_unitIso (b i) _ _ (e i)
    let : IsIso ((moduleTensorCoefficientMap (W i) (K.app L)).app
        (((pullback f).obj N).restrict (a i))) := by
      change IsIso (((SheafOfModulesOfCommRing.tensorFunctor (W i).sheaf).map
        (K.app L)).app _)
      infer_instance
    have he := modulePullbackTensorMap_openBaseChange (a i) (b i) f (j i) h L N
    have : IsIso ((pullback (b i)).map (tensorRestrictionIso (j i) L N).hom ≫
        K.app ((moduleTensorLeftFunctor Y L).obj N) ≫
          (restrictFunctor (a i)).map (modulePullbackTensorMap f L N)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((pullback (b i)).map (tensorRestrictionIso (j i) L N).hom ≫
        K.app ((moduleTensorLeftFunctor Y L).obj N)) _

/-- The original sheafified braiding switches the two original tensor generators. -/
lemma moduleTensorSymmetry_section (Z : Scheme.{u}) (M N : Z.Modules) (O : Z.Opens)
    (m : Γ(M, O)) (n : Γ(N, O)) :
    (moduleTensorSymmetry Z M N).hom.val.app (op O)
        (moduleTensorSection Z M N O m n) = moduleTensorSection Z N M O n m := by
  have h := (SheafOfModulesOfCommRing.associatedSheafUnit Z.sheaf).naturality
    (β_ ((SheafOfModulesOfCommRing.toPresheaf Z.sheaf).obj M)
      ((SheafOfModulesOfCommRing.toPresheaf Z.sheaf).obj N)).hom
  exact (congrArg (fun f => f.app (op O) (m ⊗ₜ[Γ(Z, O)] n)) h).symm

/-- The adjoint of the tensor mate sends both original generators to their actual unit images. -/
lemma modulePullbackTensorMap_homEquiv_section (M N : Y.Modules) (O : Y.Opens)
    (m : Γ(M, O)) (n : Γ(N, O)) :
    ((pullbackPushforwardAdjunction f).homEquiv _ _ (modulePullbackTensorMap f M N)).app O
      (moduleTensorSection Y M N O m n) =
    moduleTensorSection X ((pullback f).obj M) ((pullback f).obj N) (f ⁻¹ᵁ O)
      (((pullbackPushforwardAdjunction f).unit.app M).app O m)
      (((pullbackPushforwardAdjunction f).unit.app N).app O n) := by
  rw [modulePullbackTensorMap_homEquiv_eq f M N]
  change (modulePushforwardTensorMap f ((pullback f).obj M) ((pullback f).obj N)).app O
    (((moduleTensorLeftFunctor Y ((pushforward f).obj ((pullback f).obj M))).map
      ((pullbackPushforwardAdjunction f).unit.app N)).app O
      (((moduleTensorCoefficientMap Y ((pullbackPushforwardAdjunction f).unit.app M)).app N).app O
        (moduleTensorSection Y M N O m n))) = _
  let m' : Γ((pushforward f).obj ((pullback f).obj M), O) :=
    ((pullbackPushforwardAdjunction f).unit.app M).app O m
  let n' : Γ((pushforward f).obj ((pullback f).obj N), O) :=
    ((pullbackPushforwardAdjunction f).unit.app N).app O n
  have h₁ := moduleTensorCoefficientMap_section
    ((pullbackPushforwardAdjunction f).unit.app M) N O m n
  change ((moduleTensorCoefficientMap Y ((pullbackPushforwardAdjunction f).unit.app M)).app N).app O
    (moduleTensorSection Y M N O m n) =
      moduleTensorSection Y ((pushforward f).obj ((pullback f).obj M)) N O m' n at h₁
  rw [h₁]
  have h₂ := moduleTensorLeftFunctor_map_section ((pushforward f).obj ((pullback f).obj M))
    ((pullbackPushforwardAdjunction f).unit.app N) O m' n
  change ((moduleTensorLeftFunctor Y ((pushforward f).obj ((pullback f).obj M))).map
      ((pullbackPushforwardAdjunction f).unit.app N)).app O
        (moduleTensorSection Y ((pushforward f).obj ((pullback f).obj M)) N O m' n) =
    moduleTensorSection Y ((pushforward f).obj ((pullback f).obj M))
      ((pushforward f).obj ((pullback f).obj N)) O m' n' at h₂
  rw [h₂]
  exact modulePushforwardTensorMap_section f ((pullback f).obj M) ((pullback f).obj N) O m' n'

/-- The native mate preserves the original braiding under actual geometric pullback. -/
lemma modulePullbackTensorMap_symmetry (M N : Y.Modules) :
    (pullback f).map (moduleTensorSymmetry Y M N).hom ≫ modulePullbackTensorMap f N M =
      modulePullbackTensorMap f M N ≫
        (moduleTensorSymmetry X ((pullback f).obj M) ((pullback f).obj N)).hom := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply moduleTensor_hom_ext
  intro O m n
  change ((pullbackPushforwardAdjunction f).homEquiv _ _
    (modulePullbackTensorMap f N M)).app O
      ((moduleTensorSymmetry Y M N).hom.val.app (op O)
        (moduleTensorSection Y M N O m n)) =
    (moduleTensorSymmetry X ((pullback f).obj M) ((pullback f).obj N)).hom.val.app (op (f ⁻¹ᵁ O))
      (((pullbackPushforwardAdjunction f).homEquiv _ _ (modulePullbackTensorMap f M N)).app O
        (moduleTensorSection Y M N O m n))
  rw [moduleTensorSymmetry_section Y M N O m n,
    modulePullbackTensorMap_homEquiv_section f N M O n m,
    modulePullbackTensorMap_homEquiv_section f M N O m n,
    moduleTensorSymmetry_section]

/-- The same canonical mate is invertible when the second module has specified unit charts. -/
lemma modulePullbackTensorMap_isIso_of_trivializingCover_right {ι : Type v}
    (V : ι → Scheme.{u}) (j : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hc : ∀ y : Y, ∃ i v, j i v = y) (M L : Y.Modules)
    (e : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (V i).ringCatSheaf) :
    IsIso (modulePullbackTensorMap f M L) := by
  let := modulePullbackTensorMap_isIso_of_trivializingCover f V j hc L M e
  have : IsIso (modulePullbackTensorMap f M L ≫
      (moduleTensorSymmetry X ((pullback f).obj M) ((pullback f).obj L)).hom) := by
    rw [← modulePullbackTensorMap_symmetry]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (moduleTensorSymmetry X ((pullback f).obj M) ((pullback f).obj L)).hom

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u}) {Z : Scheme.{u}} (f : Z ⟶ twoChartLine R)

/-- The original tautological line charts prove invertibility for every other module sheaf. -/
instance tautologicalPullbackTensorMap_isIso (E : (twoChartLine R).Modules) :
    IsIso (modulePullbackTensorMap f E (tautologicalLine R)) := by
  apply modulePullbackTensorMap_isIso_of_trivializingCover_right f
    (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R) (polynomialChart_cover R)
    E (tautologicalLine R)
  intro b
  cases b
  · exact tautologicalLineMinusIso R
  · exact tautologicalLinePlusIso R

/-- The actual pullback-tensor mate with the original tautological line is invertible. -/
def tautologicalPullbackTensorIso (E : (twoChartLine R).Modules) :
    (Scheme.Modules.pullback f).obj
        ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalLine R)) ≅
      (moduleTensorLeftFunctor Z ((Scheme.Modules.pullback f).obj E)).obj
        ((Scheme.Modules.pullback f).obj (tautologicalLine R)) :=
  asIso (modulePullbackTensorMap f E (tautologicalLine R))

/-- Pullback commutes naturally with the original right tensor by the original tautological line. -/
def tautologicalPullbackTensorNatIso :
    moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R) ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙
        moduleTensorRightFunctor Z ((Scheme.Modules.pullback f).obj (tautologicalLine R)) :=
  NatIso.ofComponents (tautologicalPullbackTensorIso R f)
    (fun g => modulePullbackTensorMap_naturality_left f g (tautologicalLine R))

/-- Every forward component is the specified native adjunction/tensor-pushforward mate. -/
lemma tautologicalPullbackTensorNatIso_hom_app (E : (twoChartLine R).Modules) :
    (tautologicalPullbackTensorNatIso R f).hom.app E =
      modulePullbackTensorMap f E (tautologicalLine R) := rfl

end AlgebraicGeometry.Scheme.ProjectiveLine
