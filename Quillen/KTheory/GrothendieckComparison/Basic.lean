/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.ClassifyingSpace.ArrowPaths
public import Quillen.CategoryTheory.QConstruction.Connected
public import Quillen.KTheory.GrothendieckGroup.Basic
public import Quillen.Topology.ClassifyingSpace.PointedFunctor
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Canonical object classes in homotopical Quillen K₀

An object supplies two specific Q-arrows from zero, with apex zero and apex
the object itself. Their realized paths form its canonical based K₀ loop.
We work with the genuine fundamental groupoid and the standard π₁ group
isomorphism. The full Grothendieck comparison is not assumed.
-/
@[expose] public section


noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The second canonical Q-arrow from zero to an object, represented by the
span with the whole object as apex. -/
def fromZeroTotal (X : E.QCategory) : E.qZero ⟶ X :=
  Q.mkHom E.deflation E.inflation
    { apex := X.obj.of
      l := 0
      r := 𝟙 _
      wl := E.deflation_zero _
      wr := E.inflation_id _ }

/-- The forward Q-arrow associated to an admissible monomorphism. -/
def qInflation {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    Q.of E.deflation E.inflation X ⟶ Q.of E.deflation E.inflation Y :=
  Q.mkHom E.deflation E.inflation
    { apex := X, l := 𝟙 _, r := i, wl := E.deflation_id _, wr := hi }

/-- The reverse Q-arrow associated to an admissible epimorphism. -/
def qDeflation {X Y : C} (p : X ⟶ Y) (hp : E.deflation p) :
    Q.of E.deflation E.inflation Y ⟶ Q.of E.deflation E.inflation X :=
  Q.mkHom E.deflation E.inflation
    { apex := X, l := p, r := 𝟙 _, wl := hp, wr := E.inflation_id _ }

/-- Span composition may be calculated using any actual pullback square. -/
lemma q_comp_of_isPullback {X Y Z P : C}
    (s : Span E.deflation E.inflation X Y)
    (t : Span E.deflation E.inflation Y Z)
    (a : P ⟶ s.apex) (b : P ⟶ t.apex) (h : IsPullback a b s.r t.l)
    (r : Span E.deflation E.inflation X Z)
    (e : P ≅ r.apex) (hl : e.hom ≫ r.l = a ≫ s.l)
    (hr : e.hom ≫ r.r = b ≫ t.r) :
    Q.mkHom E.deflation E.inflation s ≫ Q.mkHom E.deflation E.inflation t =
      Q.mkHom E.deflation E.inflation r := by
  refine Q.mkHom_eq_of_apexIso E.deflation E.inflation (Span.comp s t) r
    (h.isoPullback.symm ≪≫ e) ?_ ?_
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hl, Span.comp_l]
    simp only [h.isoPullback_inv_fst_assoc]
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hr, Span.comp_r]
    simp only [h.isoPullback_inv_snd_assoc]

/-- The zero-apex arrow is preserved by admissible inclusions. -/
lemma fromZero_qInflation {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    E.fromZero (Q.of E.deflation E.inflation X) ≫ E.qInflation i hi =
      E.fromZero (Q.of E.deflation E.inflation Y) := by
  have h : IsPullback (𝟙 (0 : C)) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  apply E.q_comp_of_isPullback _ _ _ _ h _ (Iso.refl _)
  · simp [Q.of]
  · simp [Q.of]

/-- The whole-apex arrow is preserved by admissible quotient maps. -/
lemma fromZeroTotal_qDeflation {X Y : C} (p : X ⟶ Y) (hp : E.deflation p) :
    E.fromZeroTotal (Q.of E.deflation E.inflation Y) ≫ E.qDeflation p hp =
      E.fromZeroTotal (Q.of E.deflation E.inflation X) := by
  apply E.q_comp_of_isPullback _ _ p (𝟙 X)
    (IsPullback.of_horiz_isIso (fst := 𝟙 X) (g := 𝟙 Y) ⟨by simp⟩).flip
    _ (Iso.refl _)
  · simp [Q.of]
  · simp [Q.of]

/-- The kernel universal property gives the pullback square against zero. -/
lemma conflation_kernel_isPullback {S : ShortComplex C} (hS : E.conflation S) :
    IsPullback (0 : S.X₁ ⟶ 0) S.f (0 : 0 ⟶ S.X₃) S.g := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp [S.zero])
    (fun s => (E.kernel S hS).lift
      (KernelFork.ofι s.snd (by rw [← s.condition]; simp))) ?_ ?_ ?_)
  · intro s
    exact Subsingleton.elim _ _
  · intro s
    exact Fork.IsLimit.lift_ι _
  · intro s m hm hn
    apply Fork.IsLimit.hom_ext (E.kernel S hS)
    apply hn.trans
    simpa using ((E.kernel S hS).fac
      (KernelFork.ofι s.snd (by rw [← s.condition]; simp)) WalkingParallelPair.zero).symm

/-- The whole-apex arrow followed by an inflation represents its subobject. -/
lemma fromZeroTotal_qInflation {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    E.fromZeroTotal (Q.of E.deflation E.inflation X) ≫ E.qInflation i hi =
      Q.mkHom E.deflation E.inflation
        { apex := X, l := 0, r := i, wl := E.deflation_zero _, wr := hi } := by
  have h : IsPullback (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  apply E.q_comp_of_isPullback _ _ _ _ h _ (Iso.refl _)
  · simp [Q.of]
  · simp [Q.of]

/-- The crucial Q-construction relation for a conflation, obtained from its
kernel pullback square. -/
lemma conflation_q_relation {S : ShortComplex C} (hS : E.conflation S) :
    E.fromZero (Q.of E.deflation E.inflation S.X₃) ≫
        E.qDeflation S.g (E.deflation_of_conflation hS) =
      E.fromZeroTotal (Q.of E.deflation E.inflation S.X₁) ≫
        E.qInflation S.f (E.inflation_of_conflation hS) := by
  rw [E.fromZeroTotal_qInflation]
  apply E.q_comp_of_isPullback _ _ _ _ (E.conflation_kernel_isPullback hS) _ (Iso.refl _)
  · simp [Q.of]
  · simp [Q.of]

/-- The algebraic loop of an object under any groupoid-valued functor on Q.
The application of interest is the actual realized fundamental groupoid. -/
def qObjectClass {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D) (X : C) :
    End (F.obj E.qZero) :=
  F.map (E.fromZeroTotal (Q.of E.deflation E.inflation X)) ≫
    inv (F.map (E.fromZero (Q.of E.deflation E.inflation X)))

/-- Exact sequences impose the genuine object-loop relation in every
Q-groupoid target, without commutativity being assumed. -/
lemma qObjectClass_conflation {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {S : ShortComplex C} (hS : E.conflation S) :
    E.qObjectClass F S.X₂ = E.qObjectClass F S.X₁ * E.qObjectClass F S.X₃ := by
  have h₁ := congrArg F.map (E.fromZero_qInflation S.f (E.inflation_of_conflation hS))
  have h₂ := congrArg F.map (E.fromZeroTotal_qDeflation S.g (E.deflation_of_conflation hS))
  have h₃ := congrArg F.map (E.conflation_q_relation hS)
  simp only [Functor.map_comp] at h₁ h₂ h₃
  change _ = (_ ≫ _) ≫ (_ ≫ _)
  dsimp only [qObjectClass]
  apply (cancel_mono (F.map (E.fromZero (Q.of E.deflation E.inflation S.X₂)))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h₁]
  simp only [IsIso.inv_hom_id_assoc]
  rw [← h₃, ← h₂]
  simp

/-- Any chosen cokernel of an admissible inclusion belongs to the exact
structure, by uniqueness of cokernels. -/
lemma conflation_of_inflation_of_isCokernel {S : ShortComplex C}
    (hf : E.inflation S.f) (hg : IsColimit (CokernelCofork.ofπ S.g S.zero)) :
    E.conflation S := by
  obtain ⟨Z, p, hp, hT⟩ := hf
  let hTg := E.cokernel (ShortComplex.mk S.f p hp) hT
  let e := hTg.coconePointUniqueUpToIso hg
  let eS : ShortComplex.mk S.f p hp ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by
      simpa using (hTg.comp_coconePointUniqueUpToIso_hom hg WalkingParallelPair.one).symm)
  exact E.iso_closed eS hT

/-- The biproduct inclusions are admissible in every exact structure. -/
lemma inflation_biprod_inl (X Y : C) : E.inflation (biprod.inl : X ⟶ X ⊞ Y) := by
  have h : IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr := by
    have h := IsPushout.of_is_coproduct (BinaryBiproduct.isColimit X Y)
      (isZero_zero C).isInitial
    change IsPushout ((isZero_zero C).isInitial.to X) ((isZero_zero C).isInitial.to Y)
      (biprod.inl : X ⟶ X ⊞ Y) biprod.inr at h
    have hX : (isZero_zero C).isInitial.to X = (0 : 0 ⟶ X) := Subsingleton.elim _ _
    have hY : (isZero_zero C).isInitial.to Y = (0 : 0 ⟶ Y) := Subsingleton.elim _ _
    simpa only [hX, hY] using h
  exact E.inflation.of_isPushout h (E.inflation_zero Y)

/-- The second biproduct inclusion is admissible as well. -/
lemma inflation_biprod_inr (X Y : C) : E.inflation (biprod.inr : Y ⟶ X ⊞ Y) := by
  have h : IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr := by
    have h := IsPushout.of_is_coproduct (BinaryBiproduct.isColimit X Y)
      (isZero_zero C).isInitial
    change IsPushout ((isZero_zero C).isInitial.to X) ((isZero_zero C).isInitial.to Y)
      (biprod.inl : X ⟶ X ⊞ Y) biprod.inr at h
    have hX : (isZero_zero C).isInitial.to X = (0 : 0 ⟶ X) := Subsingleton.elim _ _
    have hY : (isZero_zero C).isInitial.to Y = (0 : 0 ⟶ Y) := Subsingleton.elim _ _
    simpa only [hX, hY] using h
  exact E.inflation.of_isPushout h.flip (E.inflation_zero X)

/-- The standard split short complex is a conflation in every exact category. -/
lemma conflation_biprod_inl_snd (X Y : C) :
    E.conflation (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.snd (by simp)) :=
  E.conflation_of_inflation_of_isCokernel (E.inflation_biprod_inl X Y)
    (biprod.isCokernelInlCokernelFork X Y)

/-- The reverse-order split short complex is also a conflation. -/
lemma conflation_biprod_inr_fst (X Y : C) :
    E.conflation (ShortComplex.mk (biprod.inr : Y ⟶ X ⊞ Y) biprod.fst (by simp)) :=
  E.conflation_of_inflation_of_isCokernel (E.inflation_biprod_inr X Y)
    (biprod.isCokernelInrCokernelFork X Y)

/-- Canonical object loops pairwise commute in every Q-groupoid target.
This does not assert that arbitrary topological loops are generated by them. -/
lemma qObjectClass_commute {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D) (X Y : C) :
    Commute (E.qObjectClass F X) (E.qObjectClass F Y) := by
  exact (E.qObjectClass_conflation F (E.conflation_biprod_inl_snd X Y)).symm.trans
    (E.qObjectClass_conflation F (E.conflation_biprod_inr_fst X Y))


/-- The canonical based loop representing an object: whole-apex edge followed
by the reverse of the zero-apex edge. -/
def kZeroObjectLoop (X : C) : Path E.kBasepoint E.kBasepoint :=
  (classifyingSpacePath (E.fromZeroTotal (Q.of E.deflation E.inflation X))).trans
    (classifyingSpacePath (E.fromZero (Q.of E.deflation E.inflation X))).symm

/-- The genuine first homotopy group is identified with the path-quotient
fundamental group, including its group multiplication. -/
def kZeroFundamentalGroupEquiv :
    E.K 0 ≃* FundamentalGroup E.KSpace E.kBasepoint :=
  HomotopyGroup.pi1MulEquivFundamentalGroup

/-- The canonical object class in the actual homotopical Quillen K₀. -/
def kZeroObjectClass (X : C) : E.K 0 :=
  E.kZeroFundamentalGroupEquiv.symm ⟦E.kZeroObjectLoop X⟧

@[simp] lemma kZeroFundamentalGroupEquiv_objectClass (X : C) :
    E.kZeroFundamentalGroupEquiv (E.kZeroObjectClass X) = ⟦E.kZeroObjectLoop X⟧ :=
  E.kZeroFundamentalGroupEquiv.apply_symm_apply _

/-- The topological object loop is exactly the object endomorphism under the
canonical realized fundamental-groupoid functor. -/
lemma kZeroObjectLoop_eq_qObjectClass (X : C) :
    (⟦E.kZeroObjectLoop X⟧ : FundamentalGroup E.KSpace E.kBasepoint) =
      E.qObjectClass (classifyingFundamentalGroupoidFunctor E.QCategory) X := by
  dsimp only [qObjectClass, classifyingFundamentalGroupoidFunctor]
  rw [← Groupoid.inv_eq_inv]
  rfl

/-- Canonical classes satisfy the conflation relation in actual homotopical K₀. -/
lemma kZeroObjectClass_conflation {S : ShortComplex C} (hS : E.conflation S) :
    E.kZeroObjectClass S.X₂ = E.kZeroObjectClass S.X₁ * E.kZeroObjectClass S.X₃ := by
  apply E.kZeroFundamentalGroupEquiv.injective
  simp only [map_mul, E.kZeroFundamentalGroupEquiv_objectClass,
    E.kZeroObjectLoop_eq_qObjectClass]
  exact E.qObjectClass_conflation _ hS

/-- Canonical object classes pairwise commute in the actual homotopical K₀. -/
lemma kZeroObjectClass_commute (X Y : C) :
    Commute (E.kZeroObjectClass X) (E.kZeroObjectClass Y) := by
  apply E.kZeroFundamentalGroupEquiv.injective
  simp only [map_mul, E.kZeroFundamentalGroupEquiv_objectClass,
    E.kZeroObjectLoop_eq_qObjectClass]
  exact E.qObjectClass_commute _ X Y

/-- The subgroup of actual K₀ generated by the canonical object loops. -/
def kZeroObjectSubgroup : Subgroup (E.K 0) :=
  Subgroup.closure (Set.range E.kZeroObjectClass)

instance kZeroObjectSubgroup_isMulCommutative : IsMulCommutative E.kZeroObjectSubgroup := by
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩ _
  exact E.kZeroObjectClass_commute X Y

open scoped IsMulCommutative in
/-- The canonical-generator subgroup is unconditionally commutative. -/
instance instCommGroupKZeroObjectSubgroup : CommGroup E.kZeroObjectSubgroup := inferInstance

/-- An object class regarded as an element of the canonical-generator subgroup. -/
def kZeroObjectClassInSubgroup (X : C) : E.kZeroObjectSubgroup :=
  ⟨E.kZeroObjectClass X, Subgroup.subset_closure ⟨X, rfl⟩⟩

/-- The Grothendieck group maps to the genuine canonical-generator subgroup
by its universal property, with no assumed comparison isomorphism. -/
def grothendieckToKZeroSubgroup : Multiplicative E.GrothendieckGroup →* E.kZeroObjectSubgroup :=
  AddMonoidHom.toMultiplicativeLeft
    (E.grothendieckLift (fun X => Additive.ofMul (E.kZeroObjectClassInSubgroup X)) (by
      intro S hS
      apply Subtype.ext
      exact E.kZeroObjectClass_conflation hS))

/-- The canonical comparison homomorphism from the algebraic Grothendieck
group to the actual first homotopy group defining Quillen K₀. -/
def grothendieckToKZero : Multiplicative E.GrothendieckGroup →* E.K 0 :=
  E.kZeroObjectSubgroup.subtype.comp E.grothendieckToKZeroSubgroup

@[simp] lemma grothendieckToKZeroSubgroup_class (X : C) :
    E.grothendieckToKZeroSubgroup (Multiplicative.ofAdd (E.grothendieckClass X)) =
      E.kZeroObjectClassInSubgroup X := by
  simp [grothendieckToKZeroSubgroup, AddMonoidHom.toMultiplicativeLeft]

/-- The comparison preserves the canonical generator of every object exactly. -/
@[simp] lemma grothendieckToKZero_class (X : C) :
    E.grothendieckToKZero (Multiplicative.ofAdd (E.grothendieckClass X)) =
      E.kZeroObjectClass X := by
  exact congrArg Subtype.val (E.grothendieckToKZeroSubgroup_class X)

/-- Its image is precisely the subgroup generated by the canonical object loops.
No assertion that this subgroup is all of K₀ is used here. -/
theorem grothendieckToKZero_range : E.grothendieckToKZero.range = E.kZeroObjectSubgroup := by
  apply le_antisymm
  · rintro y ⟨g, rfl⟩
    exact (E.grothendieckToKZeroSubgroup g).property
  · apply (Subgroup.closure_le _).2
    rintro y ⟨X, rfl⟩
    exact ⟨Multiplicative.ofAdd (E.grothendieckClass X), E.grothendieckToKZero_class X⟩

/-- Isomorphic objects determine identical genuine K₀ classes. -/
lemma kZeroObjectClass_iso {X Y : C} (e : X ≅ Y) :
    E.kZeroObjectClass X = E.kZeroObjectClass Y := by
  rw [← E.grothendieckToKZero_class X, ← E.grothendieckToKZero_class Y,
    E.grothendieckClass_iso e]

/-- The zero object determines the neutral element of the genuine K₀ group. -/
@[simp] lemma kZeroObjectClass_zero : E.kZeroObjectClass (0 : C) = 1 := by
  rw [← E.grothendieckToKZero_class, E.grothendieckClass_zero]
  exact E.grothendieckToKZero.map_one

end Quillen.ExactStructure
