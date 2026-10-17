/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.OpenCover
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.Vertical

/-! # Original derived homology, cover, and vertical mate consumers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
namespace QuillenTest.DerivedBaseChangeCover

/-- The exact derived homology comparison retains its literal installed unit square. -/
theorem original_homology_unit
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology] (n : ℤ) (K : CochainComplex.Plus A) :
    (DerivedCategory.Plus.homologyFunctor B n).map (F.rightDerivedFunctorPlusUnit.app K) ≫
        (F.rightDerivedFunctorPlusHomologyIso n).hom.app (DerivedCategory.Plus.Q.obj K) ≫
        F.map ((DerivedCategory.Plus.homologyFunctorFactors (A := A) n).hom.app K) =
      (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).hom.app
          (F.mapCochainComplexPlus.obj K) ≫
        (F.mapCochainComplexPlusHomologyIso n).hom.app K :=
  F.rightDerivedFunctorPlusHomologyIso_unit n K
attribute [local instance] Abelian.hasFiniteBiproducts
/-- The actual standard ambient module-sheaf derived categories. -/
local instance standard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
/-- Actual derived open restrictions yield an inverse to the original global arrow. -/
theorem original_global_inverse {X : Scheme.{u}} {ι : Type w}
    (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    {K L : DerivedCategory.Plus X.Modules} (q : K ⟶ L)
    (hq : ∀ i, IsIso ((derivedRestrictionPlus (a i)).map q)) :
    ∃ r, q ≫ r = 𝟙 K ∧ r ≫ q = 𝟙 L := by
  have := isIso_of_derivedRestriction_openCover Y a hcover q hq
  exact ⟨inv q, IsIso.hom_inv_id q, IsIso.inv_hom_id q⟩
variable {Z' Z W U V X : Scheme.{u}}
  (c : Z' ⟶ Z) (d : Z' ⟶ W) (g : Z ⟶ U)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d g a) (h : IsPullback a b f j) [Flat j]
/-- The original vertically pasted derived mate retains both original comparison directions. -/
theorem original_vertical_mate (K : DerivedCategory.Plus Z.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d g a hs
    (derivedFlatBaseChangeMap c (d ≫ b) (g ≫ f) j (hs.paste_vert h)).app K =
      (derivedFlatPullbackPlus j).map ((derivedPushforwardPlusCompIso g f).hom.app K) ≫
      (derivedFlatBaseChangeMap a b f j h).app ((derivedPushforwardPlus g).obj K) ≫
      (derivedPushforwardPlus b).map ((derivedFlatBaseChangeMap c d g a hs).app K) ≫
      (derivedPushforwardPlusCompIso d b).inv.app ((derivedFlatPullbackPlus c).obj K) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d g a hs
  rw [← derivedFlatBaseChangeMap_paste_vert c d g a b f j hs h]
  exact derivedFlatBaseChangeVerticalComposite_app c d g a b f j hs h K
/-- Vertical composition retains the literal ordinary mate in the installed unit square. -/
theorem original_vertical_unit (K : CochainComplex.Plus Z.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d g a hs
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward (g ≫ f))
        (Scheme.Modules.pullback j)).app K ≫
      (derivedFlatBaseChangeVerticalComposite c d g a b f j hs h).app
        (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus
          (cartesianBaseChangeMap c (d ≫ b) (g ≫ f) j (hs.paste_vert h))).app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback c)
        (Scheme.Modules.pushforward (d ≫ b))).app K :=
  derivedFlatBaseChangeVerticalComposite_unit c d g a b f j hs h K
/-- The original global derived mate has a two-sided inverse under the genuine local hypotheses. -/
theorem original_mate_global_inverse
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) [Flat j] {ι : Type w} (Y Z : ι → Scheme.{u})
    (k : ∀ i, Y i ⟶ V) [∀ i, IsOpenImmersion (k i)]
    (c : ∀ i, Z i ⟶ W) (d : ∀ i, Z i ⟶ Y i)
    (hs : ∀ i, IsPullback (c i) (d i) b (k i))
    (hcover : ∀ x : V, ∃ (i : ι) (y : Y i), k i y = x)
    (K : DerivedCategory.Plus U.Modules)
    (hK : ∀ i, IsIso ((derivedFlatBaseChangeMap (c i ≫ a) (d i) f (k i ≫ j)
      ((hs i).paste_horiz h)).app K)) :
    letI := flat_cartesian_baseChange a b f j h
    ∃ q, (derivedFlatBaseChangeMap a b f j h).app K ≫ q = 𝟙 _ ∧
      q ≫ (derivedFlatBaseChangeMap a b f j h).app K = 𝟙 _ := by
  let := flat_cartesian_baseChange a b f j h
  have := isIso_derivedFlatBaseChangeMap_of_openCover a b f j h Y Z k c d hs hcover K hK
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩
end QuillenTest.DerivedBaseChangeCover
