/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Matrix.IdempotentAutomorphismClass

/-!
# Stable automorphism classes and split extensions

Extending an automorphism of a retract by the identity on its complementary
summand preserves its original stable elementary-quotient class.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Idempotents
namespace Quillen.RightMatrix
variable {R : Type u} [Ring R]

/-- A retract inside another matrix summand has its actual composite idempotent presentation. -/
def retractPresentation {P Q : ProjectiveMatrices R} (i : P ⟶ Q) (r : Q ⟶ P)
    (hr : i ≫ r = 𝟙 P) : ProjectiveMatrices R where
  X := Q.X
  p := homMatrix i * homMatrix r
  idem := by
    have h : homMatrix r * homMatrix i = idempotentMatrix P := congrArg homMatrix hr
    have hi : homMatrix i * idempotentMatrix P = homMatrix i := Karoubi.p_comp i
    change (homMatrix i * homMatrix r) * (homMatrix i * homMatrix r) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (homMatrix r), h, ← Matrix.mul_assoc, hi]

/-- The original retract maps identify it with its composite-idempotent image. -/
def retractPresentationIso {P Q : ProjectiveMatrices R} (i : P ⟶ Q) (r : Q ⟶ P)
    (hr : i ≫ r = 𝟙 P) : P ≅ retractPresentation i r hr := by
  have h : homMatrix r * homMatrix i = idempotentMatrix P := congrArg homMatrix hr
  have hi : homMatrix i * idempotentMatrix P = homMatrix i := Karoubi.p_comp i
  have hr' : idempotentMatrix P * homMatrix r = homMatrix r := Karoubi.comp_p r
  refine ⟨⟨i.f, ?_⟩, ⟨r.f, ?_⟩, ?_, ?_⟩
  · change ((homMatrix i * homMatrix r) * homMatrix i) * idempotentMatrix P = homMatrix i
    rw [Matrix.mul_assoc (homMatrix i) (homMatrix r) (homMatrix i), h, hi, hi]
  · change (idempotentMatrix P * homMatrix r) * (homMatrix i * homMatrix r) = homMatrix r
    rw [hr', ← Matrix.mul_assoc, h, hr']
  · apply Karoubi.Hom.ext
    exact h
  · apply Karoubi.Hom.ext
    rfl

/-- Identity extension along a genuine retract preserves the stable automorphism class. -/
theorem automorphismClass_splitExtension {P Q : ProjectiveMatrices R}
    (i : P ⟶ Q) (r : Q ⟶ P) (hr : i ≫ r = 𝟙 P) (g : Aut P) (h : Aut Q)
    (hh : homMatrix h.hom = homMatrix i * homMatrix g.hom * homMatrix r +
      idempotentMatrix Q - homMatrix i * homMatrix r) :
    automorphismClass Q h = automorphismClass P g := by
  let e := retractPresentationIso i r hr
  let g' := Aut.autMulEquivOfIso e g
  have he : extendAut h = extendAut g' := by
    apply Units.ext
    change homMatrix h.hom + (1 - idempotentMatrix Q) =
      homMatrix i * homMatrix g.hom * homMatrix r +
        ((1 : Matrix (Fin Q.X.rank) (Fin Q.X.rank) R) - homMatrix i * homMatrix r)
    rw [hh]
    abel
  change StableGeneralLinear.finiteClass R Q.X.rank (extendAut h) = _
  rw [he]
  exact automorphismClass_conjugate e g

end Quillen.RightMatrix
