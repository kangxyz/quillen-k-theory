/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Polynomial.LaurentBaseChange
public import Mathlib.RingTheory.RingHom.Flat

/-! # Flatness of the original polynomial and Laurent coefficient maps

Both maps are actual cobase changes of the given ring map, using the original coefficient pushouts.
-/
@[expose] public section

open CategoryTheory

universe u

namespace Quillen.PolynomialBaseChange

/-- Polynomial coefficient extension preserves flatness by its actual ring pushout. -/
lemma polynomialMap_flat {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    (polynomialMap f).hom.Flat :=
  CommRingCat.flat.of_isPushout (polynomial_isPushout f).flip hf

/-- Laurent coefficient extension preserves flatness by its actual ring pushout. -/
lemma laurentMap_flat {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    (laurentMap f).hom.Flat :=
  CommRingCat.flat.of_isPushout (laurent_isPushout f).flip hf

end Quillen.PolynomialBaseChange
