/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.Property
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.Exact
public import Quillen.CategoryTheory.SmallModel.Abelian
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Affine-locally quasicoherent sheaves of finite type

The predicate is imposed on every actual affine open chart: its restriction
is quasicoherent with finite global sections. All affine charts are tested;
no noetherianity condition is used to filter the charts. When the ambient
scheme is locally noetherian, chart rings are proved noetherian, and closure
under ambient finite limits and colimits follows from the affine theorem.

Under local noetherianity, the resulting full category is abelian and its
exact sequences are actual sheaf exact sequences. The initial G-theory definition uses a small model
  in
the upper universe `u+1`; lowest-universe essential smallness and comparison
with the earlier affine small model are separate results.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

/-- A sheaf is affine-locally quasicoherent of finite type. The condition is
tested on every affine open chart, without any hypothesis on its ring. -/
def affineLocallyFiniteType (X : Scheme.{u}) : ObjectProperty X.Modules := fun M =>
  ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
    affineFiniteSheaf R ((Scheme.Modules.restrictFunctor j).obj M)

instance affineLocallyFiniteType_isoClosed (X : Scheme.{u}) : (affineLocallyFiniteType
  X).IsClosedUnderIsomorphisms where
  of_iso e h R j _ :=
    (affineFiniteSheaf R).prop_of_iso ((Scheme.Modules.restrictFunctor j).mapIso e) (h R j)

/-- Every affine chart of a locally noetherian scheme has a noetherian ring. -/
theorem noetherian_affineChart {X : Scheme.{u}} [IsLocallyNoetherian X]
    (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j] : IsNoetherianRing R := by
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion j
  exact isLocallyNoetherian_Spec.mp this

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

instance affineLocallyFiniteType_containsZero : (affineLocallyFiniteType X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun R j _ => by
    let : IsNoetherianRing R := noetherian_affineChart R j
    exact (affineFiniteSheaf R).prop_of_isZero
      ((Scheme.Modules.restrictFunctor j).map_isZero (isZero_zero _))⟩

instance affineLocallyFiniteType_finiteLimits : (affineLocallyFiniteType
  X).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ :=
    { limitsOfShape_le := by
        rintro M ⟨p⟩ R j _
        let : IsNoetherianRing R := noetherian_affineChart R j
        exact (affineFiniteSheaf R).prop_of_isLimit
          (isLimitOfPreserves (Scheme.Modules.restrictFunctor j) p.isLimit)
          (fun i => p.prop_diag_obj i R j) }

instance affineLocallyFiniteType_finiteColimits : (affineLocallyFiniteType
  X).IsClosedUnderFiniteColimits where
  isClosedUnderColimitsOfShape J _ _ :=
    { colimitsOfShape_le := by
        rintro M ⟨p⟩ R j _
        let : IsNoetherianRing R := noetherian_affineChart R j
        exact (affineFiniteSheaf R).prop_of_isColimit
          (isColimitOfPreserves (Scheme.Modules.restrictFunctor j) p.isColimit)
          (fun i => p.prop_diag_obj i R j) }

instance affineLocallyFiniteType_kernels : (affineLocallyFiniteType X).IsClosedUnderKernels where
  kernels_le := by
    rintro M ⟨f, k, hk, h⟩
    exact (affineLocallyFiniteType X).prop_of_isLimit hk
      (by rintro (_ | _) <;> first | exact h.1 | exact h.2)

instance affineLocallyFiniteType_cokernels : (affineLocallyFiniteType X).IsClosedUnderCokernels
  where
  cokernels_le := by
    rintro M ⟨f, k, hk, h⟩
    exact (affineLocallyFiniteType X).prop_of_isColimit hk
      (by rintro (_ | _) <;> first | exact h.1 | exact h.2)

/-- Sheaves whose restriction to every affine open chart is quasicoherent of
finite type, with their actual sheaf morphisms. The category is defined over
every scheme; the abelian and exact structures below assume local noetherianity. -/
abbrev FiniteTypeSheaves (X : Scheme.{u}) := (affineLocallyFiniteType X).FullSubcategory

instance instAbelianCoherent : Abelian (FiniteTypeSheaves X) := inferInstance

/-- The initial size bound uses the genuine sheaf-object universe. -/
instance finiteTypeSheaves_essentiallySmall : EssentiallySmall.{u+1} (FiniteTypeSheaves X) :=
  inferInstance

/-- Inclusion of affine-locally finite-type sheaves into module sheaves. -/
abbrev finiteTypeSheavesToModules : FiniteTypeSheaves X ⥤ X.Modules := (affineLocallyFiniteType X).ι

/-- The standard abelian exact structure on actual coherent sheaves. -/
def coherentExactStructure : ExactStructure (FiniteTypeSheaves X) := abelianExactStructure _

/-- G-theory of a locally noetherian scheme, initially formed in the upper
sheaf-object universe. No lowest-universe shrinking assertion is implicit. -/
abbrev G (n : ℕ) : Type (u+1) := CategoryTheory.ExactCategory.ExactStructure.SmallK.{u+1}
  (coherentExactStructure X) n

/-- Actual coherent inclusion is exact. -/
def coherentInclusion : ExactFunctor (coherentExactStructure X) (abelianExactStructure X.Modules)
  where
  toFunctor := finiteTypeSheavesToModules X
  map_conflation _ h := h.map_of_exact _

/-- Coherent exact sequences are precisely actual sheaf exact sequences. -/
theorem coherent_shortExact_iff (S : ShortComplex (FiniteTypeSheaves X)) :
    S.ShortExact ↔ (S.map (finiteTypeSheavesToModules X)).ShortExact := by
  constructor
  · exact fun h => h.map_of_exact _
  · intro h
    exact { exact := Functor.reflects_exact_of_faithful (finiteTypeSheavesToModules X) S h.exact
            mono_f := (finiteTypeSheavesToModules X).mono_of_mono_map h.mono_f
            epi_g := (finiteTypeSheavesToModules X).epi_of_epi_map h.epi_g }

end Quillen.CoherentScheme
