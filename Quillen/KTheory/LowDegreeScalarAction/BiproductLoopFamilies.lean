/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Automorphism.Universal
public import Quillen.KTheory.GrothendieckComparison.Basic
public import Quillen.CategoryTheory.QConstruction.SpanIsoNaturality
public import Quillen.Topology.ClassifyingSpace.UniversalComposition
public import Quillen.KTheory.Automorphism.ReturnNormalization
public import Quillen.KTheory.LowDegreeScalarAction.IdentityAutomorphism
public import Quillen.Topology.Realization.DoubleHomotopy
public import Quillen.Topology.HomotopyGroups.SelfTrackLoopShift
public import Quillen.Topology.ClassifyingSpace.FunctorChain
public import Quillen.Topology.Realization.UniverseLift
public import Quillen.Topology.Realization.HomotopyBridge
public import Quillen.Topology.ClassifyingSpace.UniverseMap
public import Quillen.Topology.ClassifyingSpace.UniverseHomotopy
public import Quillen.CategoryTheory.TheoremB.Naturality
public import Quillen.CategoryTheory.TheoremB.NaturalTransformationFiberLift
public import Quillen.Topology.HomotopyFiber.Map
public import Quillen.Aglib.CategoryTheory.Comma.UniverseLift

/-!
# Biproduct cone homotopies and their natural cylinder comparisons

Biproduct cone homotopies and their natural cylinder comparisons.

All comparisons retain the original maps and require only the stated hypotheses.
-/
@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped Topology ZeroObject

universe u v w r

namespace Quillen.LowDegreeScalarAction.BiproductLoopFamilies

section Topological
variable {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z] {x : X}

/-- Literal chronological concatenation of loop-valued source maps. -/
def concatenate (f g : C(Z, Path x x)) : C(Z, Path x x) where
  toFun z := (f z).trans (g z)
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (Path.trans_continuous_family f (Path.continuous_uncurry_iff.mpr f.continuous)
      g (Path.continuous_uncurry_iff.mpr g.continuous))

/-- A common middle cone cancels over the entire source, not only at its vertices. -/
def middleConeCancellation {f : C(Z, X)}
    (A B C : (ContinuousMap.const Z x).Homotopy f) :
    (concatenate (ConePair.loopMap A B) (ConePair.loopMap B C)).Homotopy
      (ConePair.loopMap A C) := by
  refine (ConePair.commonTailCancellation A C B.symm).cast ?_ rfl
  apply ContinuousMap.ext
  intro z
  change ((A.trans B.symm).evalAt z).trans ((C.trans B.symm).evalAt z).symm =
    ((A.evalAt z).trans (B.evalAt z).symm).trans
      ((B.evalAt z).trans (C.evalAt z).symm)
  rw [ConePair.evalAt_trans, ConePair.evalAt_trans]
  change ((A.evalAt z).trans (B.evalAt z).symm).trans
    ((C.evalAt z).trans (B.evalAt z).symm).symm = _
  rw [Path.trans_symm, Path.symm_symm]

/-- Two whole-source loop homotopies can be pasted without discarding parameters. -/
def concatenateHomotopy {f₀ f₁ g₀ g₁ : C(Z, Path x x)}
    (H : f₀.Homotopy f₁) (K : g₀.Homotopy g₁) :
    (concatenate f₀ g₀).Homotopy (concatenate f₁ g₁) where
  toFun z := (H z).trans (K z)
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (Path.trans_continuous_family H (Path.continuous_uncurry_iff.mpr H.continuous)
      K (Path.continuous_uncurry_iff.mpr K.continuous))
  map_zero_left z := by rw [H.apply_zero, K.apply_zero]; rfl
  map_one_left z := by rw [H.apply_one, K.apply_one]; rfl

end Topological

section Categorical
variable {D : Type w} [Category.{r} D] {C : Type u} [Category.{v} C]
variable {X Y Z : D ⥤ C} {c : C}

/-- The three split-conflation cone identities supply actual additivity of the
entire loop family, with each composition triangle and cancellation retained. -/
def splitConeHomotopy
    (zX fX : (Functor.const D).obj c ⟶ X)
    (zY fY : (Functor.const D).obj c ⟶ Y)
    (zZ fZ : (Functor.const D).obj c ⟶ Z)
    (i : X ⟶ Y) (p : Z ⟶ Y)
    (hz : zX ≫ i = zY) (hf : fZ ≫ p = fY) (hm : fX ≫ i = zZ ≫ p) :
    (ConePair.naturalPair zY fY).Homotopy
      (concatenate (ConePair.naturalPair zX fX) (ConePair.naturalPair zZ fZ)) := by
  let middle := fX ≫ i
  let H := middleConeCancellation (ConePair.realizedCone zY)
    (ConePair.realizedCone middle) (ConePair.realizedCone fY)
  have HX : (ConePair.naturalPair zY middle).Homotopy (ConePair.naturalPair zX fX) := by
    rw [← hz]
    exact ConePair.naturalPairSuffixHomotopy zX fX i
  have HZ : (ConePair.naturalPair middle fY).Homotopy (ConePair.naturalPair zZ fZ) := by
    dsimp only [middle]
    rw [hm, ← hf]
    exact ConePair.naturalPairSuffixHomotopy zZ fZ p
  exact H.symm.trans (concatenateHomotopy HX HZ)

end Categorical

section Biproduct
variable {D : Type w} [Category.{r} D] {C : Type u} [Category.{v} C]
  [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C) (L R : D ⥤ Core C)
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The common categorical source acts on both summands simultaneously. -/
def biprodCore : D ⥤ Core C where
  obj d := Core.mk ((L.obj d).of ⊞ (R.obj d).of)
  map f := CoreHom.mk (biprod.mapIso (L.map f).iso (R.map f).iso)
  map_id d := by
    apply Core.hom_ext
    simp only [CategoryTheory.Functor.map_id, coreCategory_id_iso, biprod.mapIso_hom, Iso.refl_hom]
    apply biprod.hom_ext <;> simp
  map_comp f g := by
    apply Core.hom_ext
    simp only [Functor.map_comp, coreCategory_comp_iso, biprod.mapIso_hom, Iso.trans_hom]
    apply biprod.hom_ext <;> simp

/-- The Q-construction functor of the left core row. -/
def leftQ : D ⥤ E.QCategory := L ⋙ Automorphism.coreQ E
/-- The Q-construction functor of the right core row. -/
def rightQ : D ⥤ E.QCategory := R ⋙ Automorphism.coreQ E
/-- The Q-construction functor of the biproduct core row. -/
def sumQ : D ⥤ E.QCategory := biprodCore L R ⋙ Automorphism.coreQ E

/-- The actual admissible subobject Q-arrow, natural on the common source. -/
def splitInclusion : leftQ E L ⟶ sumQ E L R where
  app d := E.qInflation (biprod.inl : (L.obj d).of ⟶ (L.obj d).of ⊞ (R.obj d).of)
    (E.inflation_biprod_inl _ _)
  naturality {a b} f := by
    symm
    apply E.qSpan_iso_naturality _ _ (L.map f).iso
      (biprod.mapIso (L.map f).iso (R.map f).iso) (L.map f).iso
    · simp
    · simp

/-- The actual reverse quotient Q-arrow for that same split conflation. -/
def splitProjection : rightQ E R ⟶ sumQ E L R where
  app d := E.qDeflation (biprod.snd : (L.obj d).of ⊞ (R.obj d).of ⟶ (R.obj d).of)
    (E.deflation_of_conflation (E.conflation_biprod_inl_snd _ _))
  naturality {a b} f := by
    symm
    apply E.qSpan_iso_naturality _ _ (R.map f).iso
      (biprod.mapIso (L.map f).iso (R.map f).iso)
      (biprod.mapIso (L.map f).iso (R.map f).iso)
    · simp
    · simp

/-- The zero cone pulled back along the given core row. -/
def zeroCone (A : D ⥤ Core C) : (Functor.const D).obj E.qZero ⟶ A ⋙ Automorphism.coreQ E :=
  Functor.whiskerLeft A (Automorphism.zeroCone E)

/-- The full cone pulled back along the given core row. -/
def fullCone (A : D ⥤ Core C) : (Functor.const D).obj E.qZero ⟶ A ⋙ Automorphism.coreQ E :=
  Functor.whiskerLeft A (Automorphism.fullCone E)

/-- A simultaneous isomorphism of source diagrams keeps both canonical Q-cones. -/
def coreIsoLoopHomotopy (e : L ≅ R) :
    (ConePair.naturalPair (zeroCone E L) (fullCone E L)).Homotopy
      (ConePair.naturalPair (zeroCone E R) (fullCone E R)) := by
  let r := Functor.whiskerRight e.hom (Automorphism.coreQ E)
  have hz : zeroCone E L ≫ r = zeroCone E R := by
    apply NatTrans.ext
    funext d
    exact ((Automorphism.zeroCone E).naturality (e.hom.app d)).symm.trans
      (Category.id_comp _)
  have hf : fullCone E L ≫ r = fullCone E R := by
    apply NatTrans.ext
    funext d
    exact ((Automorphism.fullCone E).naturality (e.hom.app d)).symm.trans
      (Category.id_comp _)
  have H := ConePair.naturalPairSuffixHomotopy (zeroCone E L) (fullCone E L) r
  rw [hz, hf] at H
  exact H.symm

theorem zeroCone_splitInclusion :
    zeroCone E L ≫ splitInclusion E L R = zeroCone E (biprodCore L R) := by
  apply NatTrans.ext
  funext d
  exact E.fromZero_qInflation _ _

theorem fullCone_splitProjection :
    fullCone E R ≫ splitProjection E L R = fullCone E (biprodCore L R) := by
  apply NatTrans.ext
  funext d
  exact E.fromZeroTotal_qDeflation _ _

theorem split_middle_cone :
    fullCone E L ≫ splitInclusion E L R = zeroCone E R ≫ splitProjection E L R := by
  apply NatTrans.ext
  funext d
  exact (E.conflation_q_relation (E.conflation_biprod_inl_snd (L.obj d).of (R.obj d).of)).symm

/-- Entire canonical zero-first Q-cone loops split along the actual biproduct,
uniformly on every simplex and every loop coordinate of the common source. -/
def biprodCoreLoopHomotopy :
    (ConePair.naturalPair (zeroCone E (biprodCore L R))
      (fullCone E (biprodCore L R))).Homotopy
    (concatenate (ConePair.naturalPair (zeroCone E L) (fullCone E L))
      (ConePair.naturalPair (zeroCone E R) (fullCone E R))) :=
  splitConeHomotopy (zeroCone E L) (fullCone E L)
    (zeroCone E (biprodCore L R)) (fullCone E (biprodCore L R))
    (zeroCone E R) (fullCone E R) (splitInclusion E L R) (splitProjection E L R)
    (zeroCone_splitInclusion E L R) (fullCone_splitProjection E L R)
    (split_middle_cone E L R)

/-- Normalize the whole splitting along its own original basepoint track.
This keeps the cancellation family at every splitting time. -/
def normalizedBiprodCoreLoopHomotopy (d : ClassifyingSpace D) :
    (Automorphism.rightNormalizedLoopMap
      (ConePair.naturalPair (zeroCone E (biprodCore L R))
        (fullCone E (biprodCore L R))) d).Homotopy
    (Automorphism.rightNormalizedLoopMap
      (concatenate (ConePair.naturalPair (zeroCone E L) (fullCone E L))
        (ConePair.naturalPair (zeroCone E R) (fullCone E R))) d) :=
  Automorphism.rightNormalizedHomotopy (biprodCoreLoopHomotopy E L R) d

end Biproduct

end Quillen.LowDegreeScalarAction.BiproductLoopFamilies

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open MonoidalCategory CartesianMonoidalCategory
open scoped ZeroObject Simplicial Topology unitInterval

universe u v
namespace Quillen.LowDegreeScalarAction.BiproductLoopFamilies.Equivariance
open LowDegreeScalarAction

/- The cylinder interchange and normalized-Q conjugation below are adapted
from the private proofs in LowDegreeScalarAction/ObjectClass.lean, with
independent object/morphism universes. The new consumer keeps the entire
core source rather than specializing the cylinder to one object vertex. -/

private theorem ordinalInterchange
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    {X Y : C} (f : X ⟶ Y) (a b c d : Fin 2) (hab : a ≤ b) (hcd : c ≤ d) :
    HEq
      (((ComposableArrows.mk₁ η).map (homOfLE hcd)).app
          (((ComposableArrows.mk₁ α).obj a).obj X) ≫
        ((ComposableArrows.mk₁ η).obj d).map
          (((ComposableArrows.mk₁ α).map (homOfLE hab)).app X ≫
            ((ComposableArrows.mk₁ α).obj b).map f))
      (((ComposableArrows.mk₁ β).map (homOfLE hab)).app
          (((ComposableArrows.mk₁ η).obj c).obj X) ≫
        ((ComposableArrows.mk₁ β).obj b).map
          (((ComposableArrows.mk₁ η).map (homOfLE hcd)).app X ≫
            ((ComposableArrows.mk₁ η).obj d).map f)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals try exact ((by decide : ¬ (1 : Fin 2) ≤ 0) hab).elim
  all_goals try exact ((by decide : ¬ (1 : Fin 2) ≤ 0) hcd).elim
  all_goals
    simp_all only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ComposableArrows.mk₁_obj,
      ComposableArrows.Mk₁.obj, Functor.id_obj, Fin.mk_one, homOfLE_leOfHom,
      ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map, Functor.id_map, Functor.map_comp,
      heq_eq_eq, NatTrans.id_app, Category.id_comp]
  exact β.naturality_assoc (η.app X) (G.map f)

private theorem nerveInterchange
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X)) :
    naturalTransformationNerveCylinder α ▷ Δ[1] ≫
        naturalTransformationNerveCylinder η =
      simplicialCylinderSwap (nerve C) ≫ naturalTransformationNerveCylinder η ▷ Δ[1] ≫
        naturalTransformationNerveCylinder β := by
  ext n z
  change
    (z.2.down.toOrderHom.monotone.functor.prod'
      ((z.1.2.down.toOrderHom.monotone.functor.prod' z.1.1) ⋙
        naturalTransformationCylinderFunctor α)) ⋙
      naturalTransformationCylinderFunctor η =
    (z.1.2.down.toOrderHom.monotone.functor.prod'
      ((z.2.down.toOrderHom.monotone.functor.prod' z.1.1) ⋙
        naturalTransformationCylinderFunctor η)) ⋙
      naturalTransformationCylinderFunctor β
  refine CategoryTheory.Functor.hext (fun p => ?_) ?_
  · dsimp [naturalTransformationNerveCylinder, naturalTransformationCylinderFunctor,
      Functor.uncurry, Functor.prod', simplicialCylinderSwap]
    generalize hτ : z.1.2.down.toOrderHom p = t
    generalize hθ : z.2.down.toOrderHom p = s
    fin_cases t <;> fin_cases s <;> rfl
  · intro p q f
    exact ordinalInterchange η α β hF hG (z.1.1.map f)
      (z.1.2.down.toOrderHom p) (z.1.2.down.toOrderHom q)
      (z.2.down.toOrderHom p) (z.2.down.toOrderHom q)
      (z.1.2.down.toOrderHom.monotone (leOfHom f))
      (z.2.down.toOrderHom.monotone (leOfHom f))

private theorem homotopyInterchange
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    (s t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy η
        (s, classifyingSpaceNaturalTransformationHomotopy α (t, x)) =
      classifyingSpaceNaturalTransformationHomotopy β
        (t, classifyingSpaceNaturalTransformationHomotopy η (s, x)) :=
  realizationSimplicialHomotopy_interchange
    (naturalTransformationNerveHomotopy η) (naturalTransformationNerveHomotopy α)
    (naturalTransformationNerveHomotopy η) (naturalTransformationNerveHomotopy β)
    (nerveInterchange η α β hF hG) s t x

private def castSelfIso {A : Type u} [Category.{v} A]
    {F : A ⥤ A} (h : F = 𝟭 A) (α : F ≅ F) : 𝟭 A ≅ 𝟭 A :=
  (eqToIso h.symm) ≪≫ α ≪≫ eqToIso h

private theorem castSelfIso_homotopy {A : Type u} [Category.{v} A]
    {F : A ⥤ A} (h : F = 𝟭 A) (α : F ≅ F)
    (t : unitInterval) (z : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy (castSelfIso h α).hom (t, z) =
      classifyingSpaceNaturalTransformationHomotopy α.hom (t, z) := by
  subst F
  simp [castSelfIso]

private theorem castSelfIso_conjugate {A : Type u} [Category.{v} A]
    {F G : A ⥤ A} (hF : F = 𝟭 A) (hG : G = 𝟭 A)
    (e : F ≅ G) (α : F ≅ F) :
    castSelfIso hG (e.symm ≪≫ α ≪≫ e) = castSelfIso hF α := by
  subst F
  subst G
  simp only [castSelfIso, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
  apply Iso.ext
  apply NatTrans.ext
  funext A
  change e.inv.app A ≫ α.hom.app A ≫ e.hom.app A = α.hom.app A
  have hn := α.hom.naturality (e.hom.app A)
  change e.hom.app A ≫ α.hom.app A = α.hom.app A ≫ e.hom.app A at hn
  rw [← hn, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

variable {C : Type (max u v)} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

private def identityQAut (u : 𝟭 C ≅ 𝟭 C) : 𝟭 E.QCategory ≅ 𝟭 E.QCategory :=
  NatIso.ofComponents (fun A => E.qIsoOfIso (u.app A.obj.of)) (by
    rintro ⟨⟨A⟩⟩ ⟨⟨B⟩⟩ f
    have h := (ExactFunctor.mapQIso (F := ExactFunctor.id E)
      (G := ExactFunctor.id E) u).hom.naturality f
    change (ExactFunctor.id E).mapQ.map f ≫ (E.qIsoOfIso (u.app B)).hom =
      (E.qIsoOfIso (u.app A)).hom ≫ (ExactFunctor.id E).mapQ.map f at h
    have hf : (ExactFunctor.id E).mapQ.map f = f := by
      cases f using Quotient.inductionOn
      rfl
    rw [hf] at h
    exact h)

private theorem cast_mapQIso (u : 𝟭 C ≅ 𝟭 C) :
    castSelfIso (ExactFunctor.mapQ_id E)
      (ExactFunctor.mapQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u) =
        identityQAut E u := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  simp [castSelfIso, identityQAut, ExactFunctor.mapQIso]

private theorem cast_normalizedQIso (u : 𝟭 C ≅ 𝟭 C) :
    castSelfIso (IdentityAutomorphism.normalizedIdentityQ E)
      (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u) =
        identityQAut E u := by
  unfold ExactFunctor.normalizedQIso rebaseFunctorNatIso
  exact (castSelfIso_conjugate (ExactFunctor.mapQ_id E)
    (IdentityAutomorphism.normalizedIdentityQ E) _ _).trans (cast_mapQIso E u)

private theorem identityQAut_homotopy (u : 𝟭 C ≅ 𝟭 C)
    (t : unitInterval) (z : E.KSpace) :
    classifyingSpaceNaturalTransformationHomotopy (identityQAut E u).hom (t, z) =
      IdentityAutomorphism.homotopy E u (t, z) := by
  rw [← cast_normalizedQIso E u, castSelfIso_homotopy]
  rfl

/-- The action of an identity-functor automorphism on the core category. -/
def identityCoreAction (u : 𝟭 C ≅ 𝟭 C) : 𝟭 (Core C) ⟶ 𝟭 (Core C) where
  app A := CoreHom.mk (u.app A.of)
  naturality {A B} f := by
    apply Core.hom_ext
    exact u.hom.naturality f.iso.hom

private theorem universalInterchange
    {A : Type u} [Category.{v} A] {B : Type (max u v)} [SmallCategory B]
    {F G : A ⥤ B} (η : F ⟶ G) (α : 𝟭 A ⟶ 𝟭 A) (β : 𝟭 B ⟶ 𝟭 B)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    (s t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceUniversalHomotopy η
        (s, classifyingSpaceUniversalHomotopy α (t, x)) =
      classifyingSpaceNaturalTransformationHomotopy β
        (t, classifyingSpaceUniversalHomotopy η (s, x)) := by
  let U : A ⥤ AsSmall.{max u v} A := AsSmall.up
  let V : AsSmall.{max u v} A ⥤ A := AsSmall.down
  let η' := Functor.whiskerLeft V η
  let α' : 𝟭 (AsSmall.{max u v} A) ⟶ 𝟭 (AsSmall.{max u v} A) :=
    Functor.whiskerLeft V (Functor.whiskerRight α U)
  have hU (z : ClassifyingSpace A) (r : unitInterval) :
      classifyingSpaceNaturalTransformationHomotopy α'
          (r, classifyingSpaceMapUniversal U z) =
        classifyingSpaceMapUniversal U (classifyingSpaceUniversalHomotopy α (r,z)) := by
    rw [← classifyingSpaceUniversalHomotopy_eq]
    rw [← universalHomotopy_whiskerLeft U]
    change classifyingSpaceUniversalHomotopy (Functor.whiskerRight α U) (r,z) = _
    exact universalHomotopy_whiskerRight α U r z
  have hη (z : ClassifyingSpace A) (r : unitInterval) :
      classifyingSpaceNaturalTransformationHomotopy η'
          (r, classifyingSpaceMapUniversal U z) =
        classifyingSpaceUniversalHomotopy η (r,z) := by
    rw [← classifyingSpaceUniversalHomotopy_eq, ← universalHomotopy_whiskerLeft U]
    rfl
  have hh := homotopyInterchange η' α' β
    (fun X => hF (V.obj X)) (fun X => hG (V.obj X))
    s t (classifyingSpaceMapUniversal U x)
  rw [hU, hη, hη] at hh
  exact hh

/-- Both cone time and automorphism time survive on every point of the full core source. -/
theorem wholeConeInterchange (u : 𝟭 C ≅ 𝟭 C)
    (η : (Functor.const (Core C)).obj E.qZero ⟶ Automorphism.coreQ E)
    (z : ClassifyingSpace (Core C)) (s t : unitInterval) :
    IdentityAutomorphism.homotopy E u
        (t, classifyingSpaceUniversalHomotopy η (s, z)) =
      classifyingSpaceUniversalHomotopy η
        (s, classifyingSpaceUniversalHomotopy (identityCoreAction u) (t, z)) := by
  let α := identityCoreAction u
  let β := (identityQAut E u).hom
  have hF (A : Core C) :
      ((Functor.const (Core C)).obj E.qZero).map (α.app A) = β.app E.qZero := by
    apply @Subsingleton.elim _
      (E.qHom_subsingleton_of_isZero E.qZero E.qZero (isZero_zero C))
  have hG (A : Core C) : (Automorphism.coreQ E).map (α.app A) =
      β.app ((Automorphism.coreQ E).obj A) := rfl
  exact (identityQAut_homotopy E u t _).symm.trans
    (universalInterchange η α β hF hG s t z).symm

/-- The entire original core loop is equivariant for the actual normalized scalar track. -/
theorem wholeCoreLoopInterchange (u : 𝟭 C ≅ 𝟭 C)
    (z : ClassifyingSpace (Core C)) (s t : unitInterval) :
    IdentityAutomorphism.homotopy E u (t, Automorphism.universalCoreLoopMap E z s) =
      Automorphism.universalCoreLoopMap E
        (classifyingSpaceUniversalHomotopy (identityCoreAction u) (t, z)) s := by
  change IdentityAutomorphism.homotopy E u
      (t, ((ConePair.realizedCone (Automorphism.zeroCone E)).evalAt z).trans
        ((ConePair.realizedCone (Automorphism.fullCone E)).evalAt z).symm s) =
    ((ConePair.realizedCone (Automorphism.zeroCone E)).evalAt
      (classifyingSpaceUniversalHomotopy (identityCoreAction u) (t,z))).trans
        ((ConePair.realizedCone (Automorphism.fullCone E)).evalAt
          (classifyingSpaceUniversalHomotopy (identityCoreAction u) (t,z))).symm s
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact wholeConeInterchange E u (Automorphism.zeroCone E) z _ t
  · exact wholeConeInterchange E u (Automorphism.fullCone E) z _ t

/-- The precise inverse sign needed when the scalar operation is compared in loop space. -/
theorem originalScalar_loopShift (u : 𝟭 C ≅ 𝟭 C) (a : E.K 1) :
    (loopShiftMulEquiv (x := E.kBasepoint) 1).symm
      (IdentityTrack.operation
        (IdentityTrack.loopedHomotopy (IdentityAutomorphism.homotopy E u).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E u))
        (IdentityTrack.loopedHomotopy_based (IdentityAutomorphism.homotopy E u).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E u)) 0
        (loopShiftMulEquiv 0 a)) = (IdentityAutomorphism.kOneAction E u a)⁻¹ :=
  IdentityTrack.operation_loopShift_symm (IdentityAutomorphism.homotopy E u).toHomotopy
    (IdentityAutomorphism.homotopy_fixed E u) a

end Quillen.LowDegreeScalarAction.BiproductLoopFamilies.Equivariance

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped Topology ZeroObject

universe u v w r

namespace Quillen.LowDegreeScalarAction.BiproductLoopFamilies
open Quillen.LowDegreeScalarAction.BiproductLoopFamilies

variable {D : Type w} [Category.{r} D] {C : Type u} [Category.{v} C]
  [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C) (L R : D ⥤ Core C)
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The actual biproduct braiding acts simultaneously on the whole common source. -/
def biprodSwapIso : biprodCore L R ≅ biprodCore R L :=
  NatIso.ofComponents (fun d => Core.isoMk (biprod.braiding (L.obj d).of (R.obj d).of))
    (by
      intro a b f
      apply Core.hom_ext
      change biprod.map (L.map f).iso.hom (R.map f).iso.hom ≫
          (biprod.braiding (L.obj b).of (R.obj b).of).hom =
        (biprod.braiding (L.obj a).of (R.obj a).of).hom ≫
          biprod.map (R.map f).iso.hom (L.map f).iso.hom
      apply biprod.hom_ext <;> simp)

/-- The entire loop-family commutation homotopy retains the braiding's actual
vertex track. It makes no stationarity claim at the common source vertex. -/
def coreLoopCommutation :
    (concatenate
      (ConePair.naturalPair (zeroCone E L) (fullCone E L))
      (ConePair.naturalPair (zeroCone E R) (fullCone E R))).Homotopy
    (concatenate
      (ConePair.naturalPair (zeroCone E R) (fullCone E R))
      (ConePair.naturalPair (zeroCone E L) (fullCone E L))) :=
  (biprodCoreLoopHomotopy E L R).symm.trans
    ((coreIsoLoopHomotopy E (biprodCore L R) (biprodCore R L)
      (biprodSwapIso L R)).trans (biprodCoreLoopHomotopy E R L))

/-- Normalize the actual commutation homotopy along its own vertex track. -/
def normalizedCoreLoopCommutation (d : ClassifyingSpace D) :
    (Automorphism.rightNormalizedLoopMap
      (concatenate (ConePair.naturalPair (zeroCone E L) (fullCone E L))
        (ConePair.naturalPair (zeroCone E R) (fullCone E R))) d).Homotopy
    (Automorphism.rightNormalizedLoopMap
      (concatenate (ConePair.naturalPair (zeroCone E R) (fullCone E R))
        (ConePair.naturalPair (zeroCone E L) (fullCone E L))) d) :=
  Automorphism.rightNormalizedHomotopy (coreLoopCommutation E L R) d

end Quillen.LowDegreeScalarAction.BiproductLoopFamilies

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.LowDegreeScalarAction.BiproductLoopFamilies.Cylinder

/- The four naturality proofs retain the original nerve-cylinder argument
from TheoremB/Naturality, with independent object and morphism universes. -/
/-- The categorical nerve-cylinder construction commutes with precomposition. -/
theorem naturalTransformationNerveCylinder_whiskerLeft
    {A C D : Type u} [Category.{v} A] [Category.{v} C] [Category.{v} D]
    (K : A ⥤ C) {F G : C ⥤ D} (α : F ⟶ G) :
    naturalTransformationNerveCylinder (Functor.whiskerLeft K α) =
      nerveMap K ▷ Δ[1] ≫ naturalTransformationNerveCylinder α := by
  have hc : naturalTransformationCylinderFunctor (Functor.whiskerLeft K α) =
      (𝟭 (Fin 2)).prod K ⋙ naturalTransformationCylinderFunctor α := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ rfl rfl ?_
    ext a
    simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
      ComposableArrows.mk₁, ComposableArrows.hom]
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (Functor.whiskerLeft K α) =
    _ ⋙ naturalTransformationCylinderFunctor α
  rw [hc]
  rfl

/-- The categorical nerve-cylinder construction commutes with postcomposition. -/
theorem naturalTransformationNerveCylinder_whiskerRight
    {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    {F G : C ⥤ D} (α : F ⟶ G) (K : D ⥤ E) :
    naturalTransformationNerveCylinder (Functor.whiskerRight α K) =
      naturalTransformationNerveCylinder α ≫ nerveMap K := by
  have hc : naturalTransformationCylinderFunctor (Functor.whiskerRight α K) =
      naturalTransformationCylinderFunctor α ⋙ K := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ ?_ ?_ ?_
    · refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁]
    · refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁]
    · ext a
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁, ComposableArrows.hom]
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (Functor.whiskerRight α K) =
    (_ ⋙ naturalTransformationCylinderFunctor α) ⋙ K
  rw [hc]
  rfl

/-- Precomposing a natural transformation precomposes its actual realized homotopy. -/
theorem classifyingSpaceNaturalTransformationHomotopy_whiskerLeft
    {A C D : Type u} [Category.{v} A] [Category.{v} C] [Category.{v} D]
    (K : A ⥤ C) {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerLeft K α) (t, x) =
      classifyingSpaceNaturalTransformationHomotopy α (t, classifyingSpaceMap K x) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (Functor.whiskerLeft K α))
    ((realizationCylinderIso (nerve A)).inv (x, ULift.up t)) = _
  rw [naturalTransformationNerveCylinder_whiskerLeft, Functor.map_comp, TopCat.comp_app]
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (nerveMap K)) (x, ULift.up t)
  exact congrArg (SSet.toTop.map (naturalTransformationNerveCylinder α)) hn

/-- Postcomposing a natural transformation postcomposes its actual realized homotopy. -/
theorem classifyingSpaceNaturalTransformationHomotopy_whiskerRight
    {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    {F G : C ⥤ D} (α : F ⟶ G) (K : D ⥤ E)
    (t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerRight α K) (t, x) =
      classifyingSpaceMap K (classifyingSpaceNaturalTransformationHomotopy α (t, x)) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (Functor.whiskerRight α K))
    ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) = _
  rw [naturalTransformationNerveCylinder_whiskerRight, Functor.map_comp, TopCat.comp_app]
  rfl


/-- The identity cylinder is the literal projection at every simplex. -/
theorem identity_cylinder {C : Type u} [Category.{v} C] :
    naturalTransformationNerveCylinder (𝟙 (𝟭 C)) = fst (nerve C) Δ[1] := by
  have hc : naturalTransformationCylinderFunctor (𝟙 (𝟭 C)) =
      CategoryTheory.Prod.snd (Fin 2) C := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ ?_ ?_ ?_
    · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
        Functor.uncurry, ComposableArrows.mk₁]
    · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
        Functor.uncurry, ComposableArrows.mk₁]
    · ext X
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
        Functor.uncurry, ComposableArrows.mk₁, ComposableArrows.hom]
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (𝟙 (𝟭 C)) = z.1
  rw [hc]
  rfl

/-- The identity transformation has the actual stationary realized track. -/
theorem identity_track {C : Type u} [Category.{v} C]
    (t : unitInterval) (z : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy (𝟙 (𝟭 C)) (t,z) = z := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (𝟙 (𝟭 C)))
    ((realizationCylinderIso (nerve C)).inv (z,ULift.up t)) = z
  rw [identity_cylinder]
  exact congrArg Prod.fst (ConcreteCategory.congr_hom
    (realizationCylinderIso (nerve C)).inv_hom_id (z,ULift.up t))

end Quillen.LowDegreeScalarAction.BiproductLoopFamilies.Cylinder

end

section

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/


/-!
# Whole natural-transformation cylinders across universe promotion

Lifting a small category into a larger common universe preserves the entire
original realized natural-transformation homotopy, including its interval
parameter. The proof compares the two projections of the actual cylinder
isomorphism on original simplices, then retains the categorical cylinder.

The current consumer is the original SmallModel localization boundary:
its canonical zero-nullhomotopy must survive the lower-to-upper Q-row lift.
No boundary comparison or equality inferred only from vertices is assumed.
-/


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Convexity
open scoped Simplicial Topology unitInterval
namespace Quillen.LowDegreeScalarAction.BiproductLoopFamilies.Promotion

/-- Lift a simplicial cylinder without changing its original interval simplex. -/
private def cylinderUniverseMap {X : SSet.{u}} {Y : SSet.{v}} (f : SimplicialUniverseMap X Y) :
    SimplicialUniverseMap (X ⊗ (Δ[1] : SSet.{u})) (Y ⊗ (Δ[1] : SSet.{v})) where
  app n z := (f.app n z.1, ULift.up z.2.down)
  naturality a z := Prod.ext (f.naturality a z.1) rfl

/-- Ordinary realization retains the original characteristic map of each simplex. -/
private theorem realizationMap_simplex {X Y : SSet.{u}} (f : X ⟶ Y) (n : SimplexCategory)
    (x : X.obj (op n)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    SSet.toTop.map f (realizationSimplex x t) = realizationSimplex (f.app (op n) x) t := by
  have h := realizationUniverseMap_simplex (SimplicialUniverseMap.ofHom f) n x t
  rw [realizationUniverseMap_ofHom] at h
  exact h

/-- The original realized interval coordinate is independent of its ambient universe. -/
private theorem intervalCoordinate_simplex (n : SimplexCategory)
    (a : (Δ[1] : SSet.{u}).obj (op n)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    (SSet.stdSimplex.toTopObjIsoI.hom (realizationSimplex a t)).down =
      StdSimplex.homeomorphI (StdSimplex.map a.down.toOrderHom t) := by
  have ha : SSet.yonedaEquiv.symm a = SSet.stdSimplex.map a.down := by
    ext m b
    rfl
  change (SSet.stdSimplex.toTopObjIsoI.hom
    (SSet.toTop.map (SSet.yonedaEquiv.symm a) ((SimplexCategory.toTopHomeo n).symm t))).down = _
  rw [ha]
  change StdSimplex.homeomorphI (SimplexCategory.toTopHomeo ⦋1⦌
    (SSet.toTop.map (SSet.stdSimplex.map a.down) ((SimplexCategory.toTopHomeo n).symm t))) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply, Homeomorph.apply_symm_apply]
  rfl

/-- The actual cylinder comparison preserves both original product coordinates across
universes. -/
private theorem cylinderComparison_universe {X : SSet.{u}} {Y : SSet.{v}}
    (f : SimplicialUniverseMap X Y) (z : |X ⊗ (Δ[1] : SSet.{u})|) :
    (realizationCylinderIso Y).hom (realizationUniverseMap (cylinderUniverseMap f) z) =
      (realizationUniverseMap f ((realizationCylinderIso X).hom z).1,
        ULift.up (((realizationCylinderIso X).hom z).2.down)) := by
  have h : (fun z : |X ⊗ (Δ[1] : SSet.{u})| =>
      (realizationCylinderIso Y).hom (realizationUniverseMap (cylinderUniverseMap f) z)) =
    (fun z : |X ⊗ (Δ[1] : SSet.{u})| =>
      (realizationUniverseMap f ((realizationCylinderIso X).hom z).1,
        ULift.up (((realizationCylinderIso X).hom z).2.down))) := by
    apply realization_ext
    intro n x t
    rw [realizationUniverseMap_simplex]
    apply Prod.ext
    · change SSet.toTop.map (fst Y Δ[1])
        (realizationSimplex ((cylinderUniverseMap f).app (op n) x) t) =
      realizationUniverseMap f (SSet.toTop.map (fst X Δ[1]) (realizationSimplex x t))
      rw [realizationMap_simplex, realizationMap_simplex, realizationUniverseMap_simplex]
      rfl
    · apply ULift.ext
      change (SSet.stdSimplex.toTopObjIsoI.hom
        (SSet.toTop.map (snd Y Δ[1])
          (realizationSimplex ((cylinderUniverseMap f).app (op n) x) t))).down =
        (SSet.stdSimplex.toTopObjIsoI.hom
          (SSet.toTop.map (snd X Δ[1]) (realizationSimplex x t))).down
      rw [realizationMap_simplex, realizationMap_simplex,
        intervalCoordinate_simplex, intervalCoordinate_simplex]
      rfl
  exact congrFun h z


/-- The inverse cylinder comparison retains the whole original interval parameter across
universes. -/
private theorem cylinderInverse_universe {X : SSet.{u}} {Y : SSet.{v}}
    (f : SimplicialUniverseMap X Y) (x : |X|) (t : unitInterval) :
    realizationUniverseMap (cylinderUniverseMap f)
      ((realizationCylinderIso X).inv (x, ULift.up t)) =
      (realizationCylinderIso Y).inv (realizationUniverseMap f x, ULift.up t) := by
  apply (TopCat.homeoOfIso (realizationCylinderIso Y)).injective
  change (realizationCylinderIso Y).hom
      (realizationUniverseMap (cylinderUniverseMap f)
        ((realizationCylinderIso X).inv (x, ULift.up t))) =
    (realizationCylinderIso Y).hom
      ((realizationCylinderIso Y).inv (realizationUniverseMap f x, ULift.up t))
  have hx := ConcreteCategory.congr_hom (realizationCylinderIso X).inv_hom_id (x, ULift.up t)
  have hy := ConcreteCategory.congr_hom (realizationCylinderIso Y).inv_hom_id
    (realizationUniverseMap f x, ULift.up t)
  change (realizationCylinderIso X).hom ((realizationCylinderIso X).inv (x, ULift.up t)) =
    (x, ULift.up t) at hx
  change (realizationCylinderIso Y).hom
      ((realizationCylinderIso Y).inv (realizationUniverseMap f x, ULift.up t)) =
    (realizationUniverseMap f x, ULift.up t) at hy
  rw [cylinderComparison_universe, hx, hy]

end Quillen.LowDegreeScalarAction.BiproductLoopFamilies.Promotion


namespace Quillen.LowDegreeScalarAction.BiproductLoopFamilies.Promotion
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The original natural transformation with both categorical universes lifted. -/
def liftTransformation {F G : C ⥤ D} (α : F ⟶ G) :
    universeLiftFunctor.{u,v,u,v,max u v w} F ⟶ universeLiftFunctor.{u,v,u,v,max u v w} G :=
  Functor.whiskerLeft AsSmall.down (Functor.whiskerRight α AsSmall.up)

/-- The actual categorical cylinder commutes with the displayed universe lift. -/
private theorem liftedCylinderFunctorSquare {F G : C ⥤ D} (α : F ⟶ G) :
    ((𝟭 (Fin 2)).prod (AsSmall.up : C ⥤ AsSmall.{max u v w} C)) ⋙
      naturalTransformationCylinderFunctor (liftTransformation.{u,v,w} α) =
    naturalTransformationCylinderFunctor α ⋙ (AsSmall.up : D ⥤ AsSmall.{max u v w} D) := by
  apply Functor.curry_obj_injective
  refine ComposableArrows.ext₁ rfl rfl ?_
  ext a
  apply ULift.ext
  simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
    Functor.uncurry, ComposableArrows.mk₁, ComposableArrows.hom,
    liftTransformation, universeLiftFunctor, AsSmall.down, AsSmall.up, down_comp]

/-- The complete realized nerve cylinder commutes with the original universe maps. -/
private theorem naturalCylinder_lift_map {F G : C ⥤ D} (α : F ⟶ G) :
    (classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v w} D)).comp
      (SSet.toTop.map (naturalTransformationNerveCylinder α)).hom =
    (SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v,w} α))).hom.comp
      (realizationUniverseMap (cylinderUniverseMap
        (nerveUniverseMap (AsSmall.up : C ⥤ AsSmall.{max u v w} C)))) := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n z t
  change realizationUniverseMap (nerveUniverseMap (AsSmall.up : D ⥤ AsSmall.{max u v w} D))
      (SSet.toTop.map (naturalTransformationNerveCylinder α) (realizationSimplex z t)) =
    SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v,w} α))
      (realizationUniverseMap (cylinderUniverseMap
        (nerveUniverseMap (AsSmall.up : C ⥤ AsSmall.{max u v w} C))) (realizationSimplex z t))
  rw [realizationMap_simplex, realizationUniverseMap_simplex,
    realizationUniverseMap_simplex, realizationMap_simplex]
  apply congrArg (fun b => realizationSimplex b t)
  change (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
      (naturalTransformationCylinderFunctor α ⋙ AsSmall.up) =
    (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
      (((𝟭 (Fin 2)).prod (AsSmall.up : C ⥤ AsSmall.{max u v w} C)) ⋙
        naturalTransformationCylinderFunctor (liftTransformation.{u,v,w} α))
  rw [liftedCylinderFunctorSquare]

/-- Lifting preserves every point of the original natural-transformation homotopy and its
interval parameter. -/
theorem naturalTransformationHomotopy_up {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy (liftTransformation.{u,v,w} α)
      (t,classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v w} C) x) =
    classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v w} D)
      (classifyingSpaceNaturalTransformationHomotopy α (t,x)) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v,w} α))
      ((realizationCylinderIso (nerve (AsSmall.{max u v w} C))).inv
        (realizationUniverseMap (nerveUniverseMap (AsSmall.up : C ⥤ AsSmall.{max u v w} C)) x,
          ULift.up t)) =
    classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v w} D)
      (SSet.toTop.map (naturalTransformationNerveCylinder α)
        ((realizationCylinderIso (nerve C)).inv (x,ULift.up t)))
  rw [← cylinderInverse_universe]
  exact (ContinuousMap.congr_fun (naturalCylinder_lift_map.{u,v,w} α)
    ((realizationCylinderIso (nerve C)).inv (x,ULift.up t))).symm

end Quillen.LowDegreeScalarAction.BiproductLoopFamilies.Promotion


namespace Quillen.LowDegreeScalarAction.BiproductLoopFamilies.Promotion
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The universal construction retains the original whole cylinder even when
object and morphism universes differ. -/
theorem universal_eq {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (z : ClassifyingSpace C) :
    classifyingSpaceUniversalHomotopy α (t,z) =
      classifyingSpaceNaturalTransformationHomotopy α (t,z) := by
  change classifyingSpaceMapUniversal (AsSmall.down : AsSmall.{max u v} D ⥤ D)
    (classifyingSpaceNaturalTransformationHomotopy (liftTransformation.{u,v,0} α)
      (t,classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v} C) z)) = _
  rw [naturalTransformationHomotopy_up]
  change ((classifyingSpaceMapUniversal (AsSmall.down : AsSmall.{max u v} D ⥤ D)).comp
    (classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D))) _ = _
  rw [← classifyingSpaceMapUniversal_comp]
  change classifyingSpaceMapUniversal (𝟭 D) _ = _
  rw [classifyingSpaceMapUniversal_id]
  rfl

end Quillen.LowDegreeScalarAction.BiproductLoopFamilies.Promotion

end
