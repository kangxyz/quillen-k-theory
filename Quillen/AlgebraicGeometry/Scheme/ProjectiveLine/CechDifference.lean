/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.GlobalSections

/-!
# Surjectivity of the genuine two-chart section difference

The signed difference of the original section restrictions along the two
Laurent overlap morphisms is surjective. The proof transports the explicit
Laurent polynomial splitting through the natural global-section isomorphisms
of affine schemes. The inputs and output are original scheme section rings,
not replacement coefficient modules.

This proves the degree-one cokernel vanishes for the two-term chart complex
of the structure sheaf. It does not identify that complex with right-derived
global sections. The base is an arbitrary commutative ring.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.Scheme.ProjectiveLine
open PolynomialLaurent
variable (R : CommRingCat.{u})

/-- The original signed restriction from polynomial-chart sections to Laurent
intersection sections. -/
def chartSectionsDifference :
    Γ(Spec (.of (Polynomial R)), ⊤) × Γ(Spec (.of (Polynomial R)), ⊤) →+
      Γ(Spec (.of (LaurentPolynomial R)), ⊤) :=
  ((laurentPlus R).appTop.hom.toAddMonoidHom.comp (AddMonoidHom.fst _ _)) -
    ((laurentMinus R).appTop.hom.toAddMonoidHom.comp (AddMonoidHom.snd _ _))

/-- Affine global-section naturality identifies the original geometric
restriction difference with the signed Laurent polynomial difference. -/
lemma chartSectionsDifference_coordinates
    (a b : Γ(Spec (.of (Polynomial R)), ⊤)) :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
        (chartSectionsDifference R (a, b)) =
      Quillen.PolynomialLaurentCech.difference R 0
        ((Scheme.ΓSpecIso (.of (Polynomial R))).hom.hom a,
          (Scheme.ΓSpecIso (.of (Polynomial R))).hom.hom b) := by
  have hp := congrArg (fun f => CommRingCat.Hom.hom f a) (Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)))
  have hm := congrArg (fun f => CommRingCat.Hom.hom f b) (Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent :
      Polynomial R →+* LaurentPolynomial R)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hp hm
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
    ((laurentPlus R).appTop.hom a - (laurentMinus R).appTop.hom b) = _
  rw [map_sub]
  simpa [laurentPlus, laurentMinus, Quillen.PolynomialLaurentCech.difference_apply] using
    congrArg₂ (fun x y => x - y) hp hm

/-- Every original section on the Laurent overlap is a difference of original
sections on the two polynomial charts. -/
theorem chartSectionsDifference_surjective : Function.Surjective (chartSectionsDifference R) := by
  intro z
  obtain ⟨⟨a, b⟩, hab⟩ := Quillen.PolynomialLaurentCech.difference_surjective R 0
    (by decide) ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom z)
  refine ⟨((Scheme.ΓSpecIso (.of (Polynomial R))).inv a,
    (Scheme.ΓSpecIso (.of (Polynomial R))).inv b), ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom).1
  rw [chartSectionsDifference_coordinates]
  simpa using hab

end Quillen.Scheme.ProjectiveLine
