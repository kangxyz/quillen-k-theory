/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Category.ModuleCat.MatrixAutomorphisms
public import Quillen.Algebra.Group.StableQuotientInvariance
public import Quillen.Aglib.Algebra.Category.ModuleCat.MatrixBaseChange

/-!
# Stable classes of automorphisms of matrix summands

An automorphism of an idempotent image extends by the identity on its actual
complement. The resulting stable elementary-quotient class is invariant under
isomorphisms of presentations, with no restriction on their labelled ranks.
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

/-- Stable matrix class of an actual automorphism of a chosen idempotent image. -/
def automorphismClass (P : ProjectiveMatrices R) :
    Aut P →* StableGeneralLinear.ElementaryQuotient R where
  toFun g := StableGeneralLinear.finiteClass R P.X.rank (extendAut g)
  map_one' := by
    have h : extendAut (1 : Aut P) = 1 := by
      apply Units.ext
      change idempotentMatrix P + (1 - idempotentMatrix P) = 1
      simp
    rw [h, map_one]
  map_mul' g h := by rw [extendAut_mul, map_mul]

/-- Changing an idempotent presentation preserves the stable quotient automorphism class. -/
theorem automorphismClass_presentation {P Q : ProjectiveMatrices R}
    (e : P ≅ Q) (g : Aut P) (h : Aut Q)
    (hc : e.inv ≫ g.hom = h.hom ≫ e.inv) :
    automorphismClass P g = automorphismClass Q h := by
  let w := presentationSwap e
  have hp : idempotentMatrix P * idempotentMatrix P = idempotentMatrix P := P.idem
  have hq : idempotentMatrix Q * idempotentMatrix Q = idempotentMatrix Q := Q.idem
  have hg : homMatrix g.hom * idempotentMatrix P = homMatrix g.hom := Karoubi.p_comp g.hom
  have hh : idempotentMatrix Q * homMatrix h.hom = homMatrix h.hom := Karoubi.comp_p h.hom
  have hpa : idempotentMatrix P * homMatrix e.inv = homMatrix e.inv := Karoubi.comp_p e.inv
  have haq : homMatrix e.inv * idempotentMatrix Q = homMatrix e.inv := Karoubi.p_comp e.inv
  have hc' : homMatrix e.inv * homMatrix h.hom = homMatrix g.hom * homMatrix e.inv :=
    (congrArg homMatrix hc).symm
  have hw : w * ElementaryMatrix.blockSum (1 : StableGeneralLinear.GL R P.X.rank)
      (extendAut h) =
      ElementaryMatrix.blockSum (extendAut g) (1 : StableGeneralLinear.GL R Q.X.rank) * w := by
    apply Units.ext
    change Matrix.fromBlocks (1 - idempotentMatrix P) (homMatrix e.inv)
      (homMatrix e.hom) (1 - idempotentMatrix Q) *
        Matrix.fromBlocks 1 0 0 (homMatrix h.hom + (1 - idempotentMatrix Q)) =
      Matrix.fromBlocks (homMatrix g.hom + (1 - idempotentMatrix P)) 0 0 1 *
        Matrix.fromBlocks (1 - idempotentMatrix P) (homMatrix e.inv)
          (homMatrix e.hom) (1 - idempotentMatrix Q)
    simp [Matrix.fromBlocks_multiply, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul,
      hp, hq, hg, hh, hpa, haq, hc']
  let c := (StableGeneralLinear.finiteClass R (P.X.rank + Q.X.rank)).comp
    (ElementaryMatrix.reindex finSumFinEquiv).toMonoidHom
  have hc := congrArg c hw
  rw [map_mul, map_mul] at hc
  have hh' : c (ElementaryMatrix.blockSum (1 : StableGeneralLinear.GL R P.X.rank)
      (extendAut h)) = automorphismClass Q h :=
    StableGeneralLinear.finiteClass_one_blockSum R _ _ _
  have hg' : c (ElementaryMatrix.blockSum (extendAut g)
      (1 : StableGeneralLinear.GL R Q.X.rank)) = automorphismClass P g :=
    StableGeneralLinear.finiteClass_blockSum_one R _ _ _
  rw [hh', hg', mul_comm (automorphismClass P g)] at hc
  exact (mul_left_cancel hc).symm

/-- The stable class is independent of the chosen isomorphic matrix-summand presentation. -/
lemma automorphismClass_conjugate {P Q : ProjectiveMatrices R}
    (e : P ≅ Q) (g : Aut P) :
    automorphismClass Q (Aut.autMulEquivOfIso e g) = automorphismClass P g := by
  apply (automorphismClass_presentation e g _ ?_).symm
  simp [Aut.autMulEquivOfIso]

/-- The summand class agrees with the original finite stable matrix class. -/
lemma automorphismClass_matrixUnitAut (n : ℕ) (g : StableGeneralLinear.GL R n) :
    automorphismClass ((toKaroubi (FreeCategory R)).obj ⟨n⟩) (matrixUnitAut n g) =
      StableGeneralLinear.finiteClass R n g := by
  change StableGeneralLinear.finiteClass R n (extendAut (matrixUnitAut n g)) = _
  congr 1
  apply Units.ext
  change g.val + (1 - 1) = g.val
  simp

end Quillen.RightMatrix
