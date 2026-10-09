import Quillen.Scheme.Coherent.Affine.FinitePresentation
import Quillen.Scheme.Coherent.Basic

/-!
# The global coherent category on an affine scheme

Finite global generating sections restrict to finite global generating
sections under every open immersion. On an affine target, quasicoherence
turns these into finite global sections. Consequently the all-affine-chart
coherence condition on `Spec R` agrees with the earlier actual affine
finite-module condition.

The equivalence below changes neither the underlying sheaves nor their
morphisms. In particular it identifies the two genuine abelian exact
categories, and gives the global affine category a small model in the base
ring's universe.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

variable (R : CommRingCat.{u})

/-- The all-affine-chart coherence predicate agrees with finite global
sections and quasicoherence on an affine scheme, over any ring. -/
theorem coherent_spec_iff (M : (Spec R).Modules) :
    coherent (Spec R) M ↔ affineFiniteSheaf R M := by
  constructor
  · intro hM
    exact (affineFiniteSheaf R).prop_of_iso (Scheme.Modules.restrictFunctorId.app M)
      (hM R (𝟙 (Spec R)))
  · intro hM S j _
    exact affineFiniteSheaf_restrict R j hM

/-- Equality of the two actual object properties on affine module sheaves. -/
theorem coherent_spec_eq_affineFiniteSheaf : coherent (Spec R) = affineFiniteSheaf R := by
  funext M
  exact propext (coherent_spec_iff R M)

variable [IsNoetherianRing R]

/-- The global coherent category on `Spec R` is equivalent to the actual
affine coherent category. Both directions preserve the underlying sheaf and
all morphisms definitionally. -/
def coherentAffineEquivalence : Coherent (Spec R) ≌ AffineCoherent R where
  functor :=
    { obj M :=
        let h := (coherent_spec_iff R M.obj).mp M.property
        ⟨⟨M.obj, h.1⟩, h.2⟩
      map f := ObjectProperty.homMk (ObjectProperty.homMk f.hom) }
  inverse :=
    { obj M := ⟨M.obj.obj, (coherent_spec_iff R M.obj.obj).mpr ⟨M.obj.property, M.property⟩⟩
      map f := ObjectProperty.homMk f.hom.hom }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by intro M; rfl

/-- The affine comparison commutes with actual sheaf inclusions. -/
theorem coherentAffineEquivalence_comp_inclusion :
    (coherentAffineEquivalence R).functor ⋙ affineCoherentToSheaves R =
      coherentToSheaves (Spec R) := rfl

/-- The global coherent category of an affine noetherian scheme is already
essentially small in the base ring's universe. -/
instance coherentSpec_essentiallySmall : EssentiallySmall.{u} (Coherent (Spec R)) :=
  essentiallySmall_of_fully_faithful (coherentAffineEquivalence R).functor

/-- The explicit affine equivalence also identifies global coherent sheaves
with finite modules over the base ring. -/
def coherentSpecModuleEquivalence : Coherent (Spec R) ≌ FiniteModule.{u, u} R :=
  (coherentAffineEquivalence R).trans (affineCoherentEquivalence R)

instance coherentAffineEquivalence_additive : (coherentAffineEquivalence R).functor.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentAffineEquivalence R).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

instance coherentAffineEquivalence_inverse_additive :
    (coherentAffineEquivalence R).inverse.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentAffineEquivalence R).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The comparison is an exact functor for the actual abelian exact structures. -/
def coherentToAffineExact :
    ExactFunctor (coherentExactStructure (Spec R)) (affineCoherentExactStructure R) where
  toFunctor := (coherentAffineEquivalence R).functor
  map_conflation _ h := h.map_of_exact _

/-- Its inverse is exact as well. -/
def affineToCoherentExact :
    ExactFunctor (affineCoherentExactStructure R) (coherentExactStructure (Spec R)) where
  toFunctor := (coherentAffineEquivalence R).inverse
  map_conflation _ h := h.map_of_exact _

end Quillen.CoherentScheme
