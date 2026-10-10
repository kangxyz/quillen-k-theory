/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.InjectiveCounit
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.InjectiveRestriction


/-!
# Semantic consumers of the original affine injective counit

These retain the actual boundary sequences, section maps, affine counit,
original homology inverse laws, unrelated source and target lower bounds,
independent derived model universes, and arbitrary open restriction.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open Quillen.SchemeSheaf.AffineCech
namespace Quillen.Tests.AffineInjectiveCounit

/-- The original two short exact sequences retain their actual quotient and inclusion maps. -/
theorem original_boundary_sequences {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    (Quillen.CochainComplex.opcycleBoundarySequence K n).ShortExact ∧
    (Quillen.CochainComplex.boundaryOpcycleSequence K n).ShortExact ∧
    cokernel.π (K.homologyι n) ≫ Quillen.CochainComplex.boundaryAfterι K n =
      K.fromOpcycles n (n + 1) :=
  ⟨Quillen.CochainComplex.opcycleBoundarySequence_shortExact K n,
    Quillen.CochainComplex.boundaryOpcycleSequence_shortExact K n,
    Quillen.CochainComplex.boundaryAfter_π_ι K n⟩

/-- Actual Γ preserves the next-boundary SES, without asserting exactness on all sheaves. -/
theorem original_global_section_sequence {R : CommRingCat.{u}}
    (I : Complex (Spec R)) (a n : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) :
    ((Quillen.CochainComplex.boundaryOpcycleSequence I n).map moduleSpecΓFunctor).ShortExact ∧
    Epi (moduleSpecΓFunctor.map (I.pOpcycles n)) :=
  ⟨globalSections_boundaryOpcycle_shortExact I a hbound hinj hqc n,
    epi_globalSections_pOpcycles I a hbound hinj hqc n⟩

/-- The actual counit naturality square retains every component, even on arbitrary complexes. -/
theorem original_counit_square {R : CommRingCat.{u}}
    {I J : Complex (Spec R)} (f : I ⟶ J) (n : ℤ) :
    (associatedSectionsCounit R I).f n = (I.X n).fromTildeΓ ∧
    (associatedComplex R).map ((sectionsComplex R).map f) ≫ associatedSectionsCounit R J =
      associatedSectionsCounit R I ≫ f :=
  ⟨rfl, associatedSectionsCounit_naturality R f⟩

/-- Both inverse laws concern the original homology map of the literal affine counit. -/
theorem original_homology_inverse {R : CommRingCat.{u}}
    (I : Complex (Spec R)) (a n : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) :
    ∃ r, homologyMap (associatedSectionsCounit R I) n ≫ r = 𝟙 _ ∧
      r ≫ homologyMap (associatedSectionsCounit R I) n = 𝟙 _ := by
  let := quasiIso_associatedSectionsCounit I a hbound hinj hqc
  exact ⟨inv (homologyMap (associatedSectionsCounit R I) n),
    IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

/-- Distinct lower term bounds are retained in the actual global-section weak-map comparison. -/
theorem original_sections_map {R : CommRingCat.{u}} {I J : Complex (Spec R)}
    (hIa : ∀ n, n < -3 → IsZero (I.X n)) (hJb : ∀ n, n < 4 → IsZero (J.X n))
    (hI : ∀ n, Injective (I.X n)) (hJ : ∀ n, Injective (J.X n))
    (hqcI : ∀ n, (I.homology n).IsQuasicoherent)
    (hqcJ : ∀ n, (J.homology n).IsQuasicoherent) (f : I ⟶ J) :
    QuasiIso ((sectionsComplex R).map f) ↔ QuasiIso f :=
  quasiIso_sections_iff_of_injective (-3) 4 hIa hJb hI hJ hqcI hqcJ f

/-- Original lower-bounded module reconstruction allows an independent derived model universe. -/
theorem original_lower_bound {R : CommRingCat.{u}}
    [HasDerivedCategory.{v} (Spec R).Modules] (K : Complex (Spec R)) (a : ℤ) [K.IsGE a]
    (hqc : ∀ n, (K.homology n).IsQuasicoherent) :
    ∃ P : ModuleComplex R, P.IsStrictlyGE a ∧
      Nonempty ((toDerived (Spec R)).obj ((associatedComplex R).obj P) ≅
        (toDerived (Spec R)).obj K) :=
  exists_lowerBounded_module_representative K a hqc

/-- Injective restriction retains an arbitrary original open and its literal complex terms. -/
theorem original_open_injective_terms {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : Complex X) (a : ℤ) [I.IsStrictlyGE a] (hI : ∀ n, Injective (I.X n)) :
    ((restrict j).obj I).IsStrictlyGE a ∧
      ∀ n, Injective (((restrict j).obj I).X n) := by
  refine ⟨?_, fun n => ?_⟩
  · dsimp only [restrict]
    infer_instance
  · let := hI n
    exact Quillen.SchemeSheaf.injective_restrict j (I.X n)

end Quillen.Tests.AffineInjectiveCounit
