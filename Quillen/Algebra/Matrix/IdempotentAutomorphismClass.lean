/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Group.StableQuotientInvariance
public import Quillen.Algebra.Category.ModuleCat.MatrixBaseChange

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

/-- The underlying matrix of a compatible summand morphism. -/
abbrev homMatrix {P Q : ProjectiveMatrices R} (f : P ⟶ Q) :
    Matrix (Fin Q.X.rank) (Fin P.X.rank) R := f.f

/-- The original idempotent matrix of a chosen summand presentation. -/
abbrev idempotentMatrix (P : ProjectiveMatrices R) :
    Matrix (Fin P.X.rank) (Fin P.X.rank) R := P.p

/-- Extend a summand automorphism by the identity on the complementary idempotent. -/
def extendAut {P : ProjectiveMatrices R} (g : Aut P) :
    StableGeneralLinear.GL R P.X.rank where
  val := homMatrix g.hom + (1 - idempotentMatrix P)
  inv := homMatrix g.inv + (1 - idempotentMatrix P)
  val_inv := by
    have hp : idempotentMatrix P * idempotentMatrix P = idempotentMatrix P := P.idem
    have hgi : homMatrix g.hom * homMatrix g.inv = idempotentMatrix P :=
      congrArg (fun f => homMatrix f) g.inv_hom_id
    have hg : homMatrix g.hom * idempotentMatrix P = homMatrix g.hom := Karoubi.p_comp g.hom
    have hi : idempotentMatrix P * homMatrix g.inv = homMatrix g.inv := Karoubi.comp_p g.inv
    simp [mul_add, add_mul, mul_sub, sub_mul, hp, hgi, hg, hi]
  inv_val := by
    have hp : idempotentMatrix P * idempotentMatrix P = idempotentMatrix P := P.idem
    have hgi : homMatrix g.inv * homMatrix g.hom = idempotentMatrix P :=
      congrArg (fun f => homMatrix f) g.hom_inv_id
    have hg : homMatrix g.inv * idempotentMatrix P = homMatrix g.inv := Karoubi.p_comp g.inv
    have hi : idempotentMatrix P * homMatrix g.hom = homMatrix g.hom := Karoubi.comp_p g.hom
    simp [mul_add, add_mul, mul_sub, sub_mul, hp, hgi, hg, hi]

/-- The identity-extension construction preserves multiplication of automorphisms. -/
lemma extendAut_mul {P : ProjectiveMatrices R} (g h : Aut P) :
    extendAut (g * h) = extendAut g * extendAut h := by
  apply Units.ext
  have hp : idempotentMatrix P * idempotentMatrix P = idempotentMatrix P := P.idem
  have hg : homMatrix g.hom * idempotentMatrix P = homMatrix g.hom := Karoubi.p_comp g.hom
  have hh : idempotentMatrix P * homMatrix h.hom = homMatrix h.hom := Karoubi.comp_p h.hom
  change homMatrix g.hom * homMatrix h.hom + (1 - idempotentMatrix P) =
    (homMatrix g.hom + (1 - idempotentMatrix P)) *
      (homMatrix h.hom + (1 - idempotentMatrix P))
  simp [mul_add, add_mul, mul_sub, sub_mul, hp, hg, hh]

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

/-- Isomorphic summand presentations yield an explicit stable matrix involution. -/
def presentationSwap {P Q : ProjectiveMatrices R} (e : P ≅ Q) :
    (Matrix (Fin P.X.rank ⊕ Fin Q.X.rank) (Fin P.X.rank ⊕ Fin Q.X.rank) R)ˣ := by
  let p := idempotentMatrix P
  let q := idempotentMatrix Q
  let a := homMatrix e.inv
  let b := homMatrix e.hom
  have hp : p * p = p := P.idem
  have hq : q * q = q := Q.idem
  have hab : a * b = p := congrArg homMatrix e.hom_inv_id
  have hba : b * a = q := congrArg homMatrix e.inv_hom_id
  have hpa : p * a = a := Karoubi.comp_p e.inv
  have haq : a * q = a := Karoubi.p_comp e.inv
  have hqb : q * b = b := Karoubi.comp_p e.hom
  have hbp : b * p = b := Karoubi.p_comp e.hom
  have hw : Matrix.fromBlocks (1 - p) a b (1 - q) *
      Matrix.fromBlocks (1 - p) a b (1 - q) = 1 := by
    simp [Matrix.fromBlocks_multiply, Matrix.mul_sub, Matrix.sub_mul,
      hp, hq, hab, hba, hpa, haq, hqb, hbp]
  exact ⟨Matrix.fromBlocks (1 - p) a b (1 - q),
    Matrix.fromBlocks (1 - p) a b (1 - q), hw, hw⟩

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

/-- An original matrix unit as an automorphism of the identity-idempotent presentation. -/
def matrixUnitAut (n : ℕ) (g : StableGeneralLinear.GL R n) :
    Aut ((toKaroubi (FreeCategory R)).obj ⟨n⟩) where
  hom := ⟨g.val, by
    change (1 : Matrix (Fin n) (Fin n) R) * (g.val : Matrix (Fin n) (Fin n) R) *
      (1 : Matrix (Fin n) (Fin n) R) = g.val
    simp⟩
  inv := ⟨g.inv, by
    change (1 : Matrix (Fin n) (Fin n) R) * (g.inv : Matrix (Fin n) (Fin n) R) *
      (1 : Matrix (Fin n) (Fin n) R) = g.inv
    simp⟩
  hom_inv_id := by apply Karoubi.Hom.ext; exact g.inv_val
  inv_hom_id := by apply Karoubi.Hom.ext; exact g.val_inv

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
