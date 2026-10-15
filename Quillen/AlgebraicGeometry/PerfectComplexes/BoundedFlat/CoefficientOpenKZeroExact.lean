/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenCofinality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Cylinder
public import Quillen.Waldhausen.Fibration.Rows.EquivalenceJoint
public import Quillen.Waldhausen.Cofinality.GeneralKZeroValue

/-!
# Honest K-zero exactness of the original global C/F/G section maps

The original native fine evaluation equivalence transports actual bounded-flat
joint data. Its quotient grading therefore has an injective original coarse
value map. The accepted grading lift and original perfect evaluation identify
the composite of that value with q as the unchanged raw-perfect image quotient.

Original C/F evaluation and the original r square transport the algebraic
quotient's exactness, rather than assuming a K-zero image condition. Compactness
of the open suffices for q-zero surjectivity; compactness of both endpoints
suffices for image equals kernel. Quasi-separatedness is used only to combine
these facts with the separate global injectivity of r.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes

section QuotientTransport
variable {A B C A' B' C' : Type (u + 1)}
  [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']

/-- Original image-kernel exactness transports through actual endpoint equivalences. -/
private theorem range_ker_of_exact_comparison (r : A →* B) (q : B →* C)
    (r' : A' →* B') (q' : B' →* C') (eA : A ≃* A') (eB : B ≃* B')
    (c : C →* C') (hc : Function.Injective c)
    (hr : ∀ x, eB (r x) = r' (eA x)) (hq : ∀ x, c (q x) = q' (eB x))
    (he : r'.range = q'.ker) : r.range = q.ker := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    change q (r w) = 1
    apply hc
    rw [map_one, hq, hr]
    have hm : r' (eA w) ∈ q'.ker := by
      rw [← he]
      exact ⟨eA w, rfl⟩
    exact hm
  · intro hx
    change q x = 1 at hx
    have hm : eB x ∈ r'.range := by
      rw [he]
      change q' (eB x) = 1
      rw [← hq, hx, map_one]
    obtain ⟨z, hz⟩ := hm
    refine ⟨eA.symm z, ?_⟩
    apply eB.injective
    rw [hr, MulEquiv.apply_symm_apply]
    exact hz

/-- Quotient surjectivity transfers through actual evaluation and an injective value map. -/
private theorem surjective_of_quotient_comparison (q : B →* C) (q' : B' →* C')
    (eB : B ≃* B') (c : C →* C') (hc : Function.Injective c)
    (hq : ∀ x, c (q x) = q' (eB x)) (hs : Function.Surjective q') :
    Function.Surjective q := by
  intro y
  obtain ⟨z, hz⟩ := hs (c y)
  refine ⟨eB.symm z, hc ?_⟩
  rw [hq, MulEquiv.apply_symm_apply]
  exact hz

end QuotientTransport

private theorem multiplicativeQuotient_range_ker {A B : Type (u + 1)}
    [AddCommGroup A] [AddCommGroup B] (m : A →+ B) :
    m.toMultiplicative.range = (QuotientAddGroup.mk' m.range).toMultiplicative.ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change Multiplicative.ofAdd ((QuotientAddGroup.mk' m.range) (m a.toAdd)) = 1
    apply congrArg Multiplicative.ofAdd
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨a.toAdd, rfl⟩
  · intro hx
    have hz : (QuotientAddGroup.mk' m.range) x.toAdd = 0 :=
      congrArg Multiplicative.toAdd hx
    obtain ⟨a, ha⟩ := (QuotientAddGroup.eq_zero_iff _).mp hz
    exact ⟨Multiplicative.ofAdd a, congrArg Multiplicative.ofAdd ha⟩

private theorem multiplicativeQuotient_surjective {B : Type (u + 1)}
    [AddCommGroup B] (H : AddSubgroup B) :
    Function.Surjective (QuotientAddGroup.mk' H).toMultiplicative := by
  intro y
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective H y.toAdd
  exact ⟨Multiplicative.ofAdd x, congrArg Multiplicative.ofAdd hx⟩

variable {R : CommRingCat.{u}}

/-- Actual bounded-flat joint cylinders transport along the original native evaluation inverse. -/
def boundedFlatCoefficientSectionJointData (i : Index R) :
    Fibration.RowFactorization.JointData
      (Fibration.NestedWeakEquivalences.refl (boundedFlatCoefficientSectionWaldhausen i)) :=
  Fibration.RowFactorization.JointData.ofExactEquivalence
    (boundedFlatPerfectWaldhausen (space i)) (boundedFlatCoefficientSectionWaldhausen i)
    (boundedFlatCoefficientSectionEquivalence i).symm
    (boundedFlatCoefficientSectionEquivalence_inverse_exact i)
    (boundedFlatCoefficientOriginalEvaluation_exact i) (boundedFlatPerfectJointData (space i))

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation

/-- The original graded section target has zero positive K-groups by its actual fine joint data. -/
theorem boundedFlatCoefficientGradedOpen_K_succ_subsingleton (a : Under R) (n : ℕ) :
    Subsingleton ((boundedFlatCoefficientFullOpenGrading f a).coarseStructure.K (n + 1)) :=
  (boundedFlatCoefficientFullOpenGrading f a).coarse_K_succ_subsingleton_general
    (boundedFlatCoefficientSectionJointData (op P, a)) n

/-- Original coarse K-zero values land in the unchanged actual raw-perfect image quotient. -/
def boundedFlatCoefficientOpenKZeroValueMap (a : Under R) :
    (boundedFlatCoefficientFullOpenGrading f a).coarseStructure.K 0 →*
      Multiplicative (BoundedFlatCoefficientOpenImageQuotient f a) :=
  (boundedFlatCoefficientFullOpenGrading f a).coarseKZeroValueMap
    (boundedFlatCoefficientSectionJointData (op P, a)).reflexiveSmallModel.sourceFactorization

/-- The original value map detects equality of the actual graded section K-zero classes. -/
theorem boundedFlatCoefficientOpenKZeroValueMap_injective (a : Under R) :
    Function.Injective (boundedFlatCoefficientOpenKZeroValueMap f a) :=
  (boundedFlatCoefficientFullOpenGrading f a).coarseKZeroValueMap_injective
    (boundedFlatCoefficientSectionJointData (op P, a)).reflexiveSmallModel.sourceFactorization

omit [IsOpenImmersion f.left] in
/-- Original perfect evaluation retains the inverse classical K-zero comparison on all classes. -/
theorem boundedFlatCoefficientFullOpenPerfectKEquiv_grothendieck [CompactSpace P.left]
    (a : Under R) :
    (grothendieckKZeroEquivOfSmallModel
      (perfectWaldhausen (space (op P, a)))).symm.toMonoidHom.comp
        (boundedFlatCoefficientFullOpenPerfectKEquiv f a 0).toMonoidHom =
      (AlgebraicGrothendieck.map (boundedFlatCoefficientSectionWaldhausen (op P, a))
        (boundedFlatCoefficientFullOpenPerfectEvaluation f a)
        (boundedFlatCoefficientFullOpenPerfectEvaluation_exact f a)).toMultiplicative.comp
          (grothendieckKZeroEquivOfSmallModel
            (boundedFlatCoefficientSectionWaldhausen (op P, a))).symm.toMonoidHom := by
  apply kZero_hom_ext (boundedFlatCoefficientSectionWaldhausen (op P, a))
  intro S
  change (grothendieckKZeroEquivOfSmallModel (perfectWaldhausen (space (op P, a)))).symm
    (boundedFlatCoefficientFullOpenPerfectKEquiv f a 0
      ((boundedFlatCoefficientSectionWaldhausen (op P, a)).kZeroObjectClass S)) =
    (AlgebraicGrothendieck.map (boundedFlatCoefficientSectionWaldhausen (op P, a))
      (boundedFlatCoefficientFullOpenPerfectEvaluation f a)
      (boundedFlatCoefficientFullOpenPerfectEvaluation_exact f a)).toMultiplicative
        ((grothendieckKZeroEquivOfSmallModel
          (boundedFlatCoefficientSectionWaldhausen (op P, a))).symm
            ((boundedFlatCoefficientSectionWaldhausen (op P, a)).kZeroObjectClass S))
  rw [boundedFlatCoefficientFullOpenPerfectKEquiv_objectClass,
    grothendieckKZeroEquivOfSmallModel_symm_objectClass,
    grothendieckKZeroEquivOfSmallModel_symm_objectClass]
  exact congrArg Multiplicative.ofAdd
    (map_objectClass (boundedFlatCoefficientSectionWaldhausen (op P, a))
      (boundedFlatCoefficientFullOpenPerfectEvaluation f a)
      (boundedFlatCoefficientFullOpenPerfectEvaluation_exact f a) S).symm

/-- The original q followed by its actual coarse value is the raw quotient after evaluation. -/
theorem boundedFlatCoefficientOpenKZeroValueMap_comp_grading [CompactSpace P.left]
    (a : Under R) :
    (boundedFlatCoefficientOpenKZeroValueMap f a).comp
        (KMap (Fibration.changeWeak_exact (boundedFlatCoefficientFullOpenGrading f a).nested) 0) =
      (QuotientAddGroup.mk'
        (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (schemeMap f a))
          (perfectRestrict (schemeMap f a))
          (perfectOpenRestrict_waldhausenExact (schemeMap f a))).range).toMultiplicative.comp
        ((grothendieckKZeroEquivOfSmallModel
          (perfectWaldhausen (space (op P, a)))).symm.toMonoidHom.comp
            (boundedFlatCoefficientFullOpenPerfectKEquiv f a 0).toMonoidHom) := by
  change ((boundedFlatCoefficientFullOpenGrading f a).coarseKZeroValueMap
    (boundedFlatCoefficientSectionJointData (op P, a)).reflexiveSmallModel.sourceFactorization).comp
      _ = _
  rw [Cofinality.Grading.coarseKZeroValueMap_comp_changeWeak,
    boundedFlatCoefficientFullOpenGrading_lift,
    boundedFlatCoefficientFullOpenPerfectKEquiv_grothendieck]
  rfl

/-- The unchanged actual q map is surjective on K-zero; only the original open is compact. -/
theorem boundedFlatCoefficientOpenGrading_KMap_zero_surjective [CompactSpace P.left]
    (a : Under R) :
    Function.Surjective
      (KMap (Fibration.changeWeak_exact (boundedFlatCoefficientFullOpenGrading f a).nested) 0) := by
  let d := boundedFlatCoefficientFullOpenGrading f a
  let q := KMap (Fibration.changeWeak_exact d.nested) 0
  let m := AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (schemeMap f a))
    (perfectRestrict (schemeMap f a)) (perfectOpenRestrict_waldhausenExact (schemeMap f a))
  let e := (boundedFlatCoefficientFullOpenPerfectKEquiv f a 0).trans
    (grothendieckKZeroEquivOfSmallModel (perfectWaldhausen (space (op P, a)))).symm
  exact surjective_of_quotient_comparison q (QuotientAddGroup.mk' m.range).toMultiplicative e
    (boundedFlatCoefficientOpenKZeroValueMap f a)
    (boundedFlatCoefficientOpenKZeroValueMap_injective f a)
    (fun x => DFunLike.congr_fun (boundedFlatCoefficientOpenKZeroValueMap_comp_grading f a) x)
    (multiplicativeQuotient_surjective m.range)

/-- The original r image equals the kernel of the actual q on honest K-zero classes. -/
theorem boundedFlatCoefficientOpenGrading_KMap_zero_range_ker
    [CompactSpace P.left] [CompactSpace Q.left] (a : Under R) :
    (KMap (boundedFlatCoefficientOpenRestriction_exact f a) 0).range =
      (KMap (Fibration.changeWeak_exact
        (boundedFlatCoefficientFullOpenGrading f a).nested) 0).ker := by
  let W := perfectOpenWeakWaldhausen (schemeMap f a)
  let V := perfectWaldhausen (space (op P, a))
  let I := perfectRestrict (schemeMap f a)
  let hI := perfectOpenRestrict_waldhausenExact (schemeMap f a)
  let m := AlgebraicGrothendieck.map W I hI
  let r := KMap (boundedFlatCoefficientOpenRestriction_exact f a) 0
  let q := KMap (Fibration.changeWeak_exact (boundedFlatCoefficientFullOpenGrading f a).nested) 0
  let eW := (boundedFlatCoefficientOpenPerfectKEquiv f a 0).trans
    (grothendieckKZeroEquivOfSmallModel W).symm
  let eV := (boundedFlatCoefficientFullOpenPerfectKEquiv f a 0).trans
    (grothendieckKZeroEquivOfSmallModel V).symm
  have hr (x : (boundedFlatCoefficientOpenWaldhausen f a).K 0) :
      eV (r x) = m.toMultiplicative (eW x) := by
    change (grothendieckKZeroEquivOfSmallModel V).symm
      (boundedFlatCoefficientFullOpenPerfectKEquiv f a 0 (r x)) = _
    rw [boundedFlatCoefficientOpenRestriction_perfectKComparison]
    exact grothendieckKZeroEquivOfSmallModel_symm_natural W V I hI
      (boundedFlatCoefficientOpenPerfectKEquiv f a 0 x)
  exact range_ker_of_exact_comparison r q m.toMultiplicative
    (QuotientAddGroup.mk' m.range).toMultiplicative eW eV
    (boundedFlatCoefficientOpenKZeroValueMap f a)
    (boundedFlatCoefficientOpenKZeroValueMap_injective f a) hr
    (fun x => DFunLike.congr_fun (boundedFlatCoefficientOpenKZeroValueMap_comp_grading f a) x)
    (multiplicativeQuotient_range_ker m)

/-- The actual original r/q Model arrows form the honest short exact K-zero tail. -/
theorem boundedFlatCoefficientOpenModel_KZero_exact [CompactSpace P.left]
    [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] (a : Under R) :
    Function.Injective (KMap (boundedFlatCoefficientOpenRestrictionModelMap f a).exact 0) ∧
      (KMap (boundedFlatCoefficientOpenRestrictionModelMap f a).exact 0).range =
        (KMap (boundedFlatCoefficientOpenGradingModelMap f a).exact 0).ker ∧
      Function.Surjective (KMap (boundedFlatCoefficientOpenGradingModelMap f a).exact 0) :=
  ⟨boundedFlatCoefficientOpenRestriction_KMap_zero_injective f a,
    boundedFlatCoefficientOpenGrading_KMap_zero_range_ker f a,
    boundedFlatCoefficientOpenGrading_KMap_zero_surjective f a⟩

end Quillen.PerfectComplexes
