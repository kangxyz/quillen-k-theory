/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Category.Ring.Basic

/-!
The genuine polynomial and Laurent ring endofunctors and their original coefficient, plus-coordinate
and inverse-coordinate natural transformations.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.Bass

/-- The genuine coefficient-wise Laurent ring map. -/
def laurentMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    LaurentPolynomial R →+* LaurentPolynomial S := AddMonoidAlgebra.mapRingHom ℤ f

@[simp] lemma laurentMap_C {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) : laurentMap f (LaurentPolynomial.C r) = LaurentPolynomial.C (f r) :=
  AddMonoidAlgebra.mapRingHom_single f 0 r

@[simp] lemma laurentMap_T {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℤ) : laurentMap f (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  unfold laurentMap LaurentPolynomial.T
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

@[simp] lemma laurentMap_invert {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : LaurentPolynomial R) :
    laurentMap f (LaurentPolynomial.invert p) = LaurentPolynomial.invert (laurentMap f p) := by
  apply LaurentPolynomial.ext
  intro n
  simp [laurentMap]

lemma toLaurent_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (p : Polynomial R) :
    Polynomial.toLaurent (p.map f) = laurentMap f (Polynomial.toLaurent p) := by
  have h : (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S).comp (Polynomial.mapRingHom
    f) =
      (laurentMap f).comp Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp
  exact RingHom.congr_fun h p

/-- The ordinary polynomial ring construction with its original coefficient maps. -/
def polynomialFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := .of (Polynomial R)
  map f := CommRingCat.ofHom (Polynomial.mapRingHom f.hom)
  map_id R := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact Polynomial.map_id
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact (Polynomial.map_map f.hom g.hom p).symm

/-- The ordinary Laurent ring construction with its literal coefficient-wise maps. -/
def laurentFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := .of (LaurentPolynomial R)
  map f := CommRingCat.ofHom (laurentMap f.hom)
  map_id R := by
    apply CommRingCat.hom_ext
    exact AddMonoidAlgebra.mapRingHom_id
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact AddMonoidAlgebra.mapRingHom_comp g.hom f.hom

/-- The literal plus-coordinate map R[t] → R[t,t⁻¹]. -/
def plus : polynomialFunctor.{u} ⟶ laurentFunctor.{u} where
  app R := CommRingCat.ofHom Polynomial.toLaurent
  naturality {R S} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact toLaurent_map f.hom p

/-- The literal inverse-coordinate map R[t] → R[t,t⁻¹]. -/
def minus : polynomialFunctor.{u} ⟶ laurentFunctor.{u} where
  app R := CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)
  naturality {R S} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change LaurentPolynomial.invert (Polynomial.toLaurent (p.map f.hom)) =
      laurentMap f.hom (LaurentPolynomial.invert (Polynomial.toLaurent p))
    rw [toLaurent_map,laurentMap_invert]

/-- The genuine polynomial coefficient inclusion. -/
def coefficientPolynomial : 𝟭 CommRingCat.{u} ⟶ polynomialFunctor.{u} where
  app R := CommRingCat.ofHom Polynomial.C
  naturality {R S} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (Polynomial.map_C f.hom).symm

/-- The genuine Laurent coefficient inclusion. -/
def coefficientLaurent : 𝟭 CommRingCat.{u} ⟶ laurentFunctor.{u} where
  app R := CommRingCat.ofHom LaurentPolynomial.C
  naturality {R S} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (laurentMap_C f.hom r).symm

@[simp] lemma coefficientPolynomial_plus : coefficientPolynomial.{u} ≫ plus = coefficientLaurent :=
  by
  apply NatTrans.ext
  funext R
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact Polynomial.toLaurent_C r

@[simp] lemma coefficientPolynomial_minus : coefficientPolynomial.{u} ≫ minus = coefficientLaurent
  := by
  apply NatTrans.ext
  funext R
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (congrArg LaurentPolynomial.invert (Polynomial.toLaurent_C r)).trans
    (LaurentPolynomial.invert_C r)

end Quillen.Bass

end
