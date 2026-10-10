/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Devissage.Homotopical

/-!
# Dévissage comparison examples

Constructs the K-theory equivalence for an object property satisfying the stated
closure conditions and finite-filtration hypothesis. The forward-map statement
identifies this equivalence with the canonical subcategory inclusion map.
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Quillen
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Consumer
variable {C : Type u} [SmallCategory C] [Abelian C]
  (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts]

-- The finite-filtration hypothesis produces an actual multiplicative equivalence.
def devissageEquivalence (h : Devissage.FiltrationHypothesis P) (n : ℕ) :
    (Devissage.subcategoryExactStructure P).K n ≃* (abelianExactStructure C).K n :=
  Devissage.KEquiv P h n

theorem devissage_forward_map (h : Devissage.FiltrationHypothesis P) (n : ℕ) :
    (devissageEquivalence P h n).toMonoidHom = Devissage.KMap P n := rfl
end Consumer
