/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts
public import Quillen.Aglib.Algebra.Polynomial.Laurent.Pullback
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Original global sections of the two-chart projective line

The genuine scheme pushout gives a pullback of original global-section rings.
The literal projection induces an isomorphism from the base ring, whose
inverse reads the constant coefficient on the positive polynomial chart.
No higher sheaf-cohomology, twisting-sheaf, or perfect-pushforward conclusion
is asserted here. No nontriviality or noetherian hypothesis is used.
-/
@[expose] public section
open Quillen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
variable (R : CommRingCat.{u})

/-- Original restriction of a global section to the positive polynomial chart. -/
def plusSections : Γ(twoChartLine R, ⊤) ⟶ CommRingCat.of (Polynomial R) :=
  Scheme.Γ.map (plusChart R).op ≫ (Scheme.ΓSpecIso (.of (Polynomial R))).hom

/-- Original restriction of a global section to the negative polynomial chart. -/
def minusSections : Γ(twoChartLine R, ⊤) ⟶ CommRingCat.of (Polynomial R) :=
  Scheme.Γ.map (minusChart R).op ≫ (Scheme.ΓSpecIso (.of (Polynomial R))).hom

/-- The original map of rings induced by the actual projection. -/
def baseSections : R ⟶ Γ(twoChartLine R, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ Scheme.Γ.map (projection R).op

lemma baseSections_plusSections : baseSections R ≫ plusSections R =
    CommRingCat.ofHom Polynomial.C := by
  unfold baseSections plusSections
  rw [Category.assoc, ← Functor.map_comp_assoc, ← op_comp, plusChart_projection]
  change (Scheme.ΓSpecIso R).inv ≫
    (Spec.map (CommRingCat.ofHom Polynomial.C)).appTop ≫
      (Scheme.ΓSpecIso (.of (Polynomial R))).hom = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

lemma baseSections_minusSections : baseSections R ≫ minusSections R =
    CommRingCat.ofHom Polynomial.C := by
  unfold baseSections minusSections
  rw [Category.assoc, ← Functor.map_comp_assoc, ← op_comp, minusChart_projection]
  change (Scheme.ΓSpecIso R).inv ≫
    (Spec.map (CommRingCat.ofHom Polynomial.C)).appTop ≫
      (Scheme.ΓSpecIso (.of (Polynomial R))).hom = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

lemma sections_isPullback : IsPullback (plusSections R) (minusSections R)
    (CommRingCat.ofHom Polynomial.toLaurent)
    (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)) := by
  let : Scheme.Γ.rightOp.IsLeftAdjoint := ΓSpec.adjunction.isLeftAdjoint
  have h := ((IsPushout.of_hasPushout (laurentPlus R) (laurentMinus R)).map
    Scheme.Γ.rightOp).unop.flip
  exact h.of_iso (Iso.refl _) (Scheme.ΓSpecIso (.of (Polynomial R)))
    (Scheme.ΓSpecIso (.of (Polynomial R))) (Scheme.ΓSpecIso (.of (LaurentPolynomial R)))
    (by simp [plusSections, plusChart]) (by simp [minusSections, minusChart])
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)))
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent :
        Polynomial R →+* LaurentPolynomial R)))

/-- The genuine global-section isomorphism obtained from the two original chart rings. -/
def globalSectionsIso : R ≅ Γ(twoChartLine R, ⊤) :=
  (IsPullback.of_isLimit (Quillen.PolynomialLaurentCech.constantConeIsLimit R)).isoIsPullback
    _ _ (sections_isPullback R)

/-- Its forward map is precisely the map induced by the actual projection. -/
lemma globalSectionsIso_hom : (globalSectionsIso R).hom = baseSections R := by
  apply (sections_isPullback R).hom_ext
  · rw [baseSections_plusSections]
    exact (IsPullback.of_isLimit (Quillen.PolynomialLaurentCech.constantConeIsLimit
      R)).isoIsPullback_hom_fst
      _ _ (sections_isPullback R)
  · rw [baseSections_minusSections]
    exact (IsPullback.of_isLimit (Quillen.PolynomialLaurentCech.constantConeIsLimit
      R)).isoIsPullback_hom_snd
      _ _ (sections_isPullback R)

instance : IsIso (baseSections R) := by
  rw [← globalSectionsIso_hom]
  infer_instance

/-- The inverse reads the actual constant coefficient on the positive chart. -/
lemma globalSectionsIso_inv : (globalSectionsIso R).inv =
    plusSections R ≫ CommRingCat.ofHom Polynomial.constantCoeff := by
  apply (cancel_epi (globalSectionsIso R).hom).mp
  rw [Iso.hom_inv_id, ← Category.assoc, globalSectionsIso_hom, baseSections_plusSections]
  apply CommRingCat.hom_ext
  ext r
  simp

end AlgebraicGeometry.Scheme.ProjectiveLine
