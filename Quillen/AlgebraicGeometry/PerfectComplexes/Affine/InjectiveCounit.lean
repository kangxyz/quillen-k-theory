/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineInjectiveCohomology
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenInjectiveModel


/-!
# The original affine counit on lower-bounded injective complexes

The literal map from the associated sheaf complex of actual global sections
back to the original complex has degreewise components `fromTildeΓ`. It is a
quasi-isomorphism for lower-bounded injective complexes whose homology sheaves
are quasicoherent. The terms need not be quasicoherent and there is no upper
bound. The proof uses the preserved original right homology data and the
actual counit natural transformation on quasicoherent homology.

Original global sections therefore preserve and reflect weak maps between
such complexes. Genuine injective replacement also gives lower-bounded
module reconstruction in the original ambient sheaf derived category, with
the exact requested lower term bound. This does not establish quasicoherence
or upper bounds for an open direct image.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace Quillen.PerfectComplexes.Affine

/-- The literal affine adjunction counit on arbitrary complexes of module sheaves. -/
def associatedSectionsCounit (R : CommRingCat.{u}) (K : Complex (Spec R)) :
    (associatedComplex R).obj ((sectionsComplex R).obj K) ⟶ K where
  f i := (K.X i).fromTildeΓ
  comm' i j _ := (Scheme.Modules.fromTildeΓNatTrans.naturality (K.d i j)).symm

@[reassoc]
lemma associatedSectionsCounit_naturality (R : CommRingCat.{u})
    {K L : Complex (Spec R)} (f : K ⟶ L) :
    (associatedComplex R).map ((sectionsComplex R).map f) ≫ associatedSectionsCounit R L =
      associatedSectionsCounit R K ≫ f := by
  ext i : 1
  exact Scheme.Modules.fromTildeΓNatTrans.naturality (f.f i)

/-- The actual reconstruction composite preserves right homology of a lower-bounded
injective complex with quasicoherent cohomology. -/
lemma associatedSections_preservesRightHomology {R : CommRingCat.{u}}
    (I : Complex (Spec R)) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    (moduleSpecΓFunctor ⋙ tilde.functor R).PreservesRightHomologyOf (I.sc n) := by
  let : moduleSpecΓFunctor.PreservesRightHomologyOf (I.sc n) :=
    SchemeSheaf.AffineCech.globalSections_preservesRightHomology I a hbound hinj hqc n
  let : PreservesColimit (parallelPair (I.sc n).f 0) moduleSpecΓFunctor :=
    ShortComplex.RightHomologyData.IsPreservedBy.hf (I.sc n).homologyData.right _
  let : (I.sc n).homologyData.right.IsPreservedBy (moduleSpecΓFunctor ⋙ tilde.functor R) :=
    { f := inferInstance, g' := inferInstance }
  exact Functor.PreservesRightHomologyOf.mk' _ (I.sc n).homologyData.right

/-- The literal affine counit is a quasi-isomorphism on a lower-bounded injective
all-sheaf complex with quasicoherent cohomology. No termwise quasicoherence is required. -/
lemma quasiIso_associatedSectionsCounit {R : CommRingCat.{u}}
    (I : Complex (Spec R)) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) :
    QuasiIso (associatedSectionsCounit R I) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := moduleSpecΓFunctor ⋙ tilde.functor R
  let : F.PreservesRightHomologyOf (I.sc n) :=
    associatedSections_preservesRightHomology I a hbound hinj hqc n
  let h := (I.sc n).homologyData.right
  let : h.H.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso h.homologyIso (hqc n)
  let γ := ShortComplex.RightHomologyMapData.natTransApp h
    (Scheme.Modules.fromTildeΓNatTrans (R := R))
  change IsIso (ShortComplex.homologyMap ((I.sc n).mapNatTrans
    (Scheme.Modules.fromTildeΓNatTrans (R := R))))
  rw [γ.homologyMap_eq]
  change IsIso ((h.map F).homologyIso.hom ≫ h.H.fromTildeΓ ≫
    (h.map (𝟭 (Spec R).Modules)).homologyIso.inv)
  infer_instance

/-- Original global sections preserve and reflect weak maps between actual lower-bounded
injective complexes with quasicoherent cohomology. Their bounds may be different. -/
lemma quasiIso_sections_iff_of_injective {R : CommRingCat.{u}}
    {I J : Complex (Spec R)} (a b : ℤ)
    (hIa : ∀ n, n < a → IsZero (I.X n)) (hJb : ∀ n, n < b → IsZero (J.X n))
    (hI : ∀ n, Injective (I.X n)) (hJ : ∀ n, Injective (J.X n))
    (hqcI : ∀ n, (I.homology n).IsQuasicoherent)
    (hqcJ : ∀ n, (J.homology n).IsQuasicoherent) (f : I ⟶ J) :
    QuasiIso ((sectionsComplex R).map f) ↔ QuasiIso f := by
  let := quasiIso_associatedSectionsCounit I a hIa hI hqcI
  let := quasiIso_associatedSectionsCounit J b hJb hJ hqcJ
  rw [← quasiIso_associated_iff R,
    ← quasiIso_iff_comp_right _ (associatedSectionsCounit R J),
    associatedSectionsCounit_naturality]
  exact quasiIso_iff_comp_left _ _

/-- On termwise quasicoherent input this is the already established original counit. -/
lemma associatedSectionsCounit_eq_of_quasicoherent (R : CommRingCat.{u})
    (K : Complex (Spec R)) (hK : ∀ n, (K.X n).IsQuasicoherent) :
    associatedSectionsCounit R K = (associatedSectionsIsoOfQuasicoherent R K hK).hom := rfl

/-- A cohomologically lower-bounded complex with quasicoherent homology has an actual
injective replacement and the original affine counit into that same replacement. -/
lemma exists_injective_associatedSectionsCounit {R : CommRingCat.{u}}
    (K : Complex (Spec R)) (a : ℤ) [K.IsGE a]
    (hqc : ∀ n, (K.homology n).IsQuasicoherent) :
    ∃ (I : Complex (Spec R)) (q : K ⟶ I),
      I.IsStrictlyGE a ∧ (∀ n, Injective (I.X n)) ∧ QuasiIso q ∧
      (∀ n, (I.homology n).IsQuasicoherent) ∧ QuasiIso (associatedSectionsCounit R I) := by
  let : HasDerivedCategory.{u + 1} (Spec R).Modules := HasDerivedCategory.standard _
  have : QuasiIso (K.πTruncGE a) := (K.quasiIso_πTruncGE_iff a).mpr inferInstance
  obtain ⟨I, s, hs, hI, hIa⟩ :=
    _root_.CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (K.truncGE a) a
  let := hs
  let := hIa
  let q := K.πTruncGE a ≫ s
  have hq : QuasiIso q := inferInstance
  have hqcI (n : ℤ) : (I.homology n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (isoOfQuasiIsoAt q n) (hqc n)
  exact ⟨I, q, hIa, hI, hq, hqcI, quasiIso_associatedSectionsCounit I a
    (fun n hn => I.isZero_of_isStrictlyGE a n hn) hI hqcI⟩

/-- Genuine lower-bounded affine module reconstruction in the original ambient derived category.
The module complex retains the requested lower term bound. -/
lemma exists_lowerBounded_module_representative {R : CommRingCat.{u}}
    [HasDerivedCategory.{v} (Spec R).Modules]
    (K : Complex (Spec R)) (a : ℤ) [K.IsGE a]
    (hqc : ∀ n, (K.homology n).IsQuasicoherent) :
    ∃ P : ModuleComplex R, P.IsStrictlyGE a ∧
      Nonempty ((toDerived (Spec R)).obj ((associatedComplex R).obj P) ≅
        (toDerived (Spec R)).obj K) := by
  obtain ⟨I, q, hIa, hI, hq, hqcI, hε⟩ := exists_injective_associatedSectionsCounit K a hqc
  let := hIa
  let := hq
  let := hε
  refine ⟨(sectionsComplex R).obj I, inferInstance, ⟨?_⟩⟩
  exact asIso ((toDerived (Spec R)).map (associatedSectionsCounit R I)) ≪≫
    (asIso ((toDerived (Spec R)).map q)).symm

end Quillen.PerfectComplexes.Affine
