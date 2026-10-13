/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.InjectiveCounit
public import Quillen.AlgebraicGeometry.PerfectComplexes.Homology
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineBoundedDerivedPushforward
public import Quillen.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.InjectivePushforwardAdjunction
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TwoOpenSheafSequence
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.InjectiveRestriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.AffineSectionsGlobal
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.ChartAffineness
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedStructure
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPerfect

/-! # Bounded quasicoherent sources for original affine injective counits -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace Quillen.PerfectComplexes.ProjectiveLine

local instance qcRepresentativeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- Good upper truncation of the actual affine associated-sections complex. -/
def affineBoundedQCSource (R : CommRingCat.{u}) (I : Complex (Spec R)) (b : ℤ) :
    Complex (Spec R) :=
  ((Affine.associatedComplex R).obj ((Affine.sectionsComplex R).obj I)).truncLE b

/-- The original truncated associated-sections counit, into the same actual complex. -/
def affineBoundedQCCounit (R : CommRingCat.{u}) (I : Complex (Spec R)) (b : ℤ) :
    affineBoundedQCSource R I b ⟶ I :=
  ((Affine.associatedComplex R).obj ((Affine.sectionsComplex R).obj I)).ιTruncLE b ≫
    Affine.associatedSectionsCounit R I

/-- Every term of the truncated affine source is quasicoherent, with no
quasicoherence requirement on the original complex terms. -/
theorem affineBoundedQCSource_quasicoherent (R : CommRingCat.{u})
    (I : Complex (Spec R)) (b i : ℤ) :
    ((affineBoundedQCSource R I b).X i).IsQuasicoherent := by
  let F := (Affine.associatedComplex R).obj ((Affine.sectionsComplex R).obj I)
  let Q := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  have hF (n : ℤ) : Q (F.X n) := by
    dsimp [F, Affine.associatedComplex]
    infer_instance
  rcases lt_trichotomy i b with hi | hi | hi
  · exact Q.prop_of_iso (F.truncLEXIso b i hi).symm (hF i)
  · subst i
    have hc : Q (F.cycles b) := Q.prop_of_isLimit (F.cyclesIsKernel b (b + 1) (by simp))
      (by rintro (_ | _) <;> exact hF _)
    exact Q.prop_of_iso (F.truncLEXIsoCycles b).symm hc
  · change ((F.truncLE b).X i).IsQuasicoherent
    have := Quillen.SchemeSheaf.finiteLocallyFree_of_isZero
      ((F.truncLE b).isZero_of_isStrictlyLE b i hi)
    infer_instance

/-- The source retains a given lower bound and the chosen finite upper bound. -/
theorem affineBoundedQCSource_bounds (R : CommRingCat.{u}) (I : Complex (Spec R))
    (a b : ℤ) (hab : a ≤ b) [I.IsStrictlyGE a] :
    (∀ i, i < a ∨ b < i → IsZero ((affineBoundedQCSource R I b).X i)) := by
  let F := (Affine.associatedComplex R).obj ((Affine.sectionsComplex R).obj I)
  have : F.IsStrictlyGE a := by dsimp [F]; infer_instance
  intro i hi
  rcases hi with hi | hi
  · exact (F.isZero_of_isStrictlyGE a i hi).of_iso (F.truncLEXIso b i (by omega))
  · exact (F.truncLE b).isZero_of_isStrictlyLE b i hi

/-- Bounded QC cohomology of the injective input makes its original truncated
associated-sections counit a genuine quasi-isomorphism. -/
theorem affineBoundedQCCounit_quasiIso (R : CommRingCat.{u}) (I : Complex (Spec R))
    (a b : ℤ) [I.IsStrictlyGE a] [I.IsLE b]
    (hinj : ∀ i, Injective (I.X i)) (hqc : ∀ i, (I.homology i).IsQuasicoherent) :
    QuasiIso (affineBoundedQCCounit R I b) := by
  let F := (Affine.associatedComplex R).obj ((Affine.sectionsComplex R).obj I)
  have : QuasiIso (Affine.associatedSectionsCounit R I) :=
    Affine.quasiIso_associatedSectionsCounit I a
      (fun i hi => I.isZero_of_isStrictlyGE a i hi) hinj hqc
  have : F.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact (exactAt_iff_of_quasiIsoAt
      (Affine.associatedSectionsCounit R I) i).mpr (I.exactAt_of_isLE b i hi)
  have : QuasiIso (F.ιTruncLE b) := inferInstance
  dsimp only [affineBoundedQCCounit]
  infer_instance

/-- An actual weak comparison from a finite-term QC source to an injective
bounded-below target remains weak after affine pushforward. The proof uses
the two original derived units and their literal naturality square. -/
theorem quasiIso_affinePushforward_of_boundedQC_injective
    {U X : Scheme.{u}} (j : U ⟶ X) [IsAffineHom j]
    (P I : CochainComplex.Plus U.Modules) (f : P ⟶ I) [QuasiIso f.hom]
    (a b : ℤ) (hl : ∀ i, i < a → IsZero (P.obj.X i))
    (hu : ∀ i, b < i → IsZero (P.obj.X i))
    (hqc : ∀ i, (P.obj.X i).IsQuasicoherent) (hinj : ∀ i, Injective (I.obj.X i)) :
    QuasiIso (((Scheme.Modules.pushforward j).mapCochainComplexPlus.map f).hom) := by
  let F := Scheme.Modules.pushforward j
  have : IsIso (F.rightDerivedFunctorPlusUnit.app P) :=
    SchemeSheaf.isIso_derivedPushforwardPlusUnit_of_term_bounds j P a b hl hu hqc
  have : IsIso (F.rightDerivedFunctorPlusUnit.app I) :=
    F.isIso_rightDerivedFunctorPlusUnit_of_injective I hinj
  have : IsIso (DerivedCategory.Plus.Q.map f) := by
    have hf : IsIso (DerivedCategory.Q.map f.hom) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules f.hom).mpr inferInstance
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map f)) := by
      change IsIso ((DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι).map f)
      exact (NatIso.isIso_map_iff (DerivedCategory.Plus.QCompιIso U.Modules) f).mpr hf
    exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  have hn := F.rightDerivedFunctorPlusUnit.naturality f
  dsimp only [Functor.comp_map] at hn
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f) ≫
      F.rightDerivedFunctorPlusUnit.app I) := by
    rw [hn]
    infer_instance
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f)) :=
    IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlusUnit.app I)
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).mp
  change IsIso (((CochainComplex.Plus.ι X.Modules) ⋙ DerivedCategory.Q).map
    (F.mapCochainComplexPlus.map f))
  have hmap : IsIso ((DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι).map
      (F.mapCochainComplexPlus.map f)) := by
    change IsIso (DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f)))
    infer_instance
  exact (NatIso.isIso_map_iff (DerivedCategory.Plus.QCompιIso X.Modules)
    (F.mapCochainComplexPlus.map f)).mp hmap

/-- Every literal chain map from a termwise QC source factors through the
original affine counit. No projectivity or injectivity is needed for this factorization. -/
def liftToAffineCounit (R : CommRingCat.{u}) {P I : Complex (Spec R)}
    (hP : ∀ i, (P.X i).IsQuasicoherent) (f : P ⟶ I) :
    P ⟶ (Affine.associatedComplex R).obj ((Affine.sectionsComplex R).obj I) :=
  (Affine.associatedSectionsIsoOfQuasicoherent R P hP).inv ≫
    (Affine.associatedComplex R).map ((Affine.sectionsComplex R).map f)

@[reassoc (attr := simp)]
theorem liftToAffineCounit_fac (R : CommRingCat.{u}) {P I : Complex (Spec R)}
    (hP : ∀ i, (P.X i).IsQuasicoherent) (f : P ⟶ I) :
    liftToAffineCounit R hP f ≫ Affine.associatedSectionsCounit R I = f := by
  rw [liftToAffineCounit, Category.assoc, Affine.associatedSectionsCounit_naturality]
  change (Affine.associatedSectionsIsoOfQuasicoherent R P hP).inv ≫
    (Affine.associatedSectionsIsoOfQuasicoherent R P hP).hom ≫ f = f
  simp

/-- The same actual factorization respects a finite upper term bound. -/
def liftToBoundedAffineCounit (R : CommRingCat.{u}) {P I : Complex (Spec R)}
    (b : ℤ) [P.IsStrictlyLE b] (hP : ∀ i, (P.X i).IsQuasicoherent) (f : P ⟶ I) :
    P ⟶ affineBoundedQCSource R I b :=
  inv (P.ιTruncLE b) ≫ CochainComplex.truncLEMap (liftToAffineCounit R hP f) b

@[reassoc (attr := simp)]
theorem liftToBoundedAffineCounit_fac (R : CommRingCat.{u}) {P I : Complex (Spec R)}
    (b : ℤ) [P.IsStrictlyLE b] (hP : ∀ i, (P.X i).IsQuasicoherent) (f : P ⟶ I) :
    liftToBoundedAffineCounit R b hP f ≫ affineBoundedQCCounit R I b = f := by
  dsimp only [liftToBoundedAffineCounit, affineBoundedQCCounit]
  rw [Category.assoc, ← Category.assoc (CochainComplex.truncLEMap _ _),
    CochainComplex.ιTruncLE_naturality, Category.assoc,
    liftToAffineCounit_fac, IsIso.inv_hom_id_assoc]

open Quillen.SchemeSheaf

/-- The original open localization of a complex, with unchanged degreewise maps. -/
def openLocalizationComplex {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : Complex X) : Complex X := (pushforwardComplex j).obj ((restrict j).obj I)

/-- The literal restriction unit on the original complex. -/
def openLocalizationComplexUnit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : Complex X) : I ⟶ openLocalizationComplex j I where
  f i := (openLocalizationUnit j).app (I.X i)
  comm' i k _ := ((openLocalizationUnit j).naturality (I.d i k)).symm

/-- The original nested-open restriction map, degree by degree. -/
def openLocalizationComplexMap {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (I : Complex X) :
    openLocalizationComplex j I ⟶ openLocalizationComplex (a ≫ j) I where
  f i := openLocalizationMap a j (I.X i)
  comm' i k _ := (openLocalizationMap_naturality a j (I.d i k)).symm

/-- The original second restriction map into the same actual overlap. -/
def openLocalizationComplexSecond {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : a ≫ j = b ≫ k) (I : Complex X) :
    openLocalizationComplex k I ⟶ openLocalizationComplex (a ≫ j) I where
  f i := TwoOpen.sheafSecondRestriction a b j k h (I.X i)
  comm' i m _ := (TwoOpen.sheafSecondRestriction_naturality a b j k h (I.d i m)).symm

/-- The signed original two-open sequence of actual complexes of sheaves. -/
def twoOpenComplexSequence {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : IsPullback a b j k) (I : Complex X) : ShortComplex (Complex X) :=
  ShortComplex.productSequence (openLocalizationComplexUnit j I)
    (openLocalizationComplexUnit k I) (openLocalizationComplexMap a j I)
    (openLocalizationComplexSecond a b j k h.w I) (by
      ext i : 1
      exact TwoOpen.sheaf_restriction_compatibility a b j k h (I.X i))

/-- The actual two-open complex sequence is short exact, without acyclicity
or quasicoherence assumptions on the original complex. -/
theorem twoOpenComplexSequence_shortExact {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : IsPullback a b j k)
    (hcover : ∀ x : X, (∃ y : U, j y = x) ∨ (∃ z : V, k z = x)) (I : Complex X) :
    (twoOpenComplexSequence a b j k h I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.productSequenceMapIso (HomologicalComplex.eval X.Modules (.up ℤ) i)
      (openLocalizationComplexUnit j I) (openLocalizationComplexUnit k I)
      (openLocalizationComplexMap a j I) (openLocalizationComplexSecond a b j k h.w I)
      _).symm (TwoOpen.sheafSequence_shortExact a b j k h (I.X i) hcover)

/-- A bounded QC complex on the ambient scheme from the actual affine counit. -/
def openAffineQCSource {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] (I : Complex X) (b : ℤ) : Complex X :=
  (pushforwardComplex j).obj (affineBoundedQCSource R ((restrict j).obj I) b)

/-- The actual direct image of the original bounded affine counit. -/
def openAffineQCCounit {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] (I : Complex X) (b : ℤ) :
    openAffineQCSource R j I b ⟶ openLocalizationComplex j I :=
  (pushforwardComplex j).map (affineBoundedQCCounit R ((restrict j).obj I) b)

/-- The pushed source is termwise QC for an actual quasi-compact affine open. -/
theorem openAffineQCSource_quasicoherent {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (I : Complex X) (b i : ℤ) : ((openAffineQCSource R j I b).X i).IsQuasicoherent := by
  let := affineBoundedQCSource_quasicoherent R ((restrict j).obj I) b i
  exact CoherentScheme.quasicoherent_pushforward_open j _

/-- The pushed source retains the actual finite term window. -/
theorem openAffineQCSource_bounds {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j]
    (I : Complex X) (a b : ℤ) (hab : a ≤ b) [I.IsStrictlyGE a] :
    ∀ i, i < a ∨ b < i → IsZero ((openAffineQCSource R j I b).X i) := by
  have : ((restrict j).obj I).IsStrictlyGE a := by dsimp [restrict]; infer_instance
  intro i hi
  exact (Scheme.Modules.pushforward j).map_isZero
    (affineBoundedQCSource_bounds R ((restrict j).obj I) a b hab i hi)

/-- The original affine direct-image counit is weak for bounded-below injective
input with bounded QC cohomology. -/
theorem openAffineQCCounit_quasiIso {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] [IsAffineHom j]
    (I : Complex X) (a b : ℤ) (hab : a ≤ b) [I.IsStrictlyGE a] [I.IsLE b]
    (hinj : ∀ i, Injective (I.X i)) (hqc : ∀ i, (I.homology i).IsQuasicoherent) :
    QuasiIso (openAffineQCCounit R j I b) := by
  let J := (restrict j).obj I
  have hJl : J.IsStrictlyGE a := by dsimp [J, restrict]; infer_instance
  have hJu : J.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    exact ((Scheme.Modules.restrictFunctor j).map_isZero
      ((I.exactAt_of_isLE b i hi).isZero_homology)).of_iso (restrictHomologyIso j I i)
  have hJi (i : ℤ) : Injective (J.X i) := by
    let := hinj i
    exact injective_restrict j (I.X i)
  have hJq (i : ℤ) : (J.homology i).IsQuasicoherent := by
    let := hqc i
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (restrictHomologyIso j I i).symm inferInstance
  let P := affineBoundedQCSource R J b
  have hPb := affineBoundedQCSource_bounds R J a b hab
  have : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).mpr
    (fun i hi => hPb i (Or.inl hi))
  let Pp : CochainComplex.Plus (Spec R).Modules := ⟨P, a, inferInstance⟩
  let Jp : CochainComplex.Plus (Spec R).Modules := ⟨J, a, inferInstance⟩
  let ε : Pp ⟶ Jp := ObjectProperty.homMk (affineBoundedQCCounit R J b)
  have : QuasiIso ε.hom := affineBoundedQCCounit_quasiIso R J a b hJi hJq
  exact quasiIso_affinePushforward_of_boundedQC_injective j Pp Jp ε a b
    (fun i hi => hPb i (Or.inl hi)) (fun i hi => hPb i (Or.inr hi))
    (affineBoundedQCSource_quasicoherent R J b) hJi

/-- An actual ambient chain map from a bounded QC source factors through the
pushed affine counit, by the original restriction/direct-image adjunction. -/
def liftToOpenAffineQCCounit {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] {P I : Complex X} (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ i, (P.X i).IsQuasicoherent) (f : P ⟶ openLocalizationComplex j I) :
    P ⟶ openAffineQCSource R j I b := by
  have : ((restrict j).obj P).IsStrictlyLE b := by dsimp [restrict]; infer_instance
  exact (restrictPushforwardComplexAdjunction j).homEquiv P _
    (liftToBoundedAffineCounit R b (fun i => by
      let := hP i
      change ((P.X i).restrict j).IsQuasicoherent
      infer_instance)
      (((restrictPushforwardComplexAdjunction j).homEquiv P _).symm f))

@[reassoc (attr := simp)]
theorem liftToOpenAffineQCCounit_fac {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] {P I : Complex X} (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ i, (P.X i).IsQuasicoherent) (f : P ⟶ openLocalizationComplex j I) :
    liftToOpenAffineQCCounit R j b hP f ≫ openAffineQCCounit R j I b = f := by
  dsimp only [liftToOpenAffineQCCounit, openAffineQCCounit]
  rw [← Adjunction.homEquiv_naturality_right, liftToBoundedAffineCounit_fac,
    Equiv.apply_symm_apply]

/-- Products of the two original chain comparisons remain weak. -/
theorem quasiIso_complex_prod_map {X : Scheme.{u}} {A B C D : Complex X}
    (f : A ⟶ C) (g : B ⟶ D) [QuasiIso f] [QuasiIso g] : QuasiIso (prod.map f g) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).mp
  let F := toDerived X
  have : IsIso (F.map (prod.map f g) ≫ prodComparison F C D) := by
    rw [prodComparison_natural]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.map (prod.map f g)) (prodComparison F C D)

/-- The actual complex product of two QC complexes is termwise QC. -/
theorem quasicoherent_complex_prod {X : Scheme.{u}} (A B : Complex X)
    (hA : ∀ i, (A.X i).IsQuasicoherent) (hB : ∀ i, (B.X i).IsQuasicoherent) (i : ℤ) :
    ((A ⨯ B).X i).IsQuasicoherent := by
  let Q := SheafOfModules.isQuasicoherent X.ringCatSheaf
  exact Q.prop_of_iso
    (asIso (prodComparison (HomologicalComplex.eval X.Modules (.up ℤ) i) A B)).symm
    (Q.prop_prod _ _ (hA i) (hB i))

/-- A common term window is retained by the actual complex product. -/
theorem complex_prod_bounds {X : Scheme.{u}} (A B : Complex X) (a b : ℤ)
    (hA : ∀ i, i < a ∨ b < i → IsZero (A.X i))
    (hB : ∀ i, i < a ∨ b < i → IsZero (B.X i)) :
    ∀ i, i < a ∨ b < i → IsZero ((A ⨯ B).X i) := by
  intro i hi
  have hz : IsZero (A.X i ⨯ B.X i) := by
    rw [IsZero.iff_id_eq_zero]
    apply prod.hom_ext
    · exact (hA i hi).eq_of_tgt _ _
    · exact (hB i hi).eq_of_tgt _ _
  exact hz.of_iso (asIso
    (prodComparison (HomologicalComplex.eval X.Modules (.up ℤ) i) A B))

open CategoryTheory.Pretriangulated
attribute [local instance] Abelian.hasFiniteBiproducts

/-- On an actual two-affine cover with affine overlap and affine chart maps,
bounded QC cohomology of a bounded-below injective complex has a constructed
bounded termwise-QC representative. The counits and signed overlap map are the
actual original chain maps. -/
theorem exists_bounded_qc_model_of_twoAffine_injective
    {X : Scheme.{u}} (R S T : CommRingCat.{u})
    (p : Spec T ⟶ Spec R) (q : Spec T ⟶ Spec S) (j : Spec R ⟶ X) (k : Spec S ⟶ X)
    [IsOpenImmersion p] [IsOpenImmersion q] [IsOpenImmersion j] [IsOpenImmersion k]
    [IsAffineHom j] [IsAffineHom k] (h : IsPullback p q j k)
    (hcover : ∀ x : X, (∃ y : Spec R, j y = x) ∨ (∃ z : Spec S, k z = x))
    (I : Complex X) (a b : ℤ) (hab : a ≤ b) [I.IsStrictlyGE a] [I.IsLE b]
    (hinj : ∀ i, Injective (I.X i)) (hqc : ∀ i, (I.homology i).IsQuasicoherent) :
    ∃ P : Complex X, (∀ i, i < a ∨ b + 1 < i → IsZero (P.X i)) ∧
      (∀ i, (P.X i).IsQuasicoherent) ∧ Nonempty ((toDerived X).obj P ≅ (toDerived X).obj I) := by
  let A := openAffineQCSource R j I b
  let B := openAffineQCSource S k I b
  let C := openAffineQCSource T (p ≫ j) I b
  let ca := openAffineQCCounit R j I b
  let cb := openAffineQCCounit S k I b
  let cc := openAffineQCCounit T (p ≫ j) I b
  have hA := openAffineQCSource_bounds R j I a b hab
  have hB := openAffineQCSource_bounds S k I a b hab
  have hC := openAffineQCSource_bounds T (p ≫ j) I a b hab
  have hM := complex_prod_bounds A B a b hA hB
  have hMq := quasicoherent_complex_prod A B (openAffineQCSource_quasicoherent R j I b)
    (openAffineQCSource_quasicoherent S k I b)
  have hCq := openAffineQCSource_quasicoherent T (p ≫ j) I b
  have : (A ⨯ B).IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).mpr
    (fun i hi => hM i (Or.inr hi))
  let Seq := twoOpenComplexSequence p q j k h I
  have hSeq : Seq.ShortExact := twoOpenComplexSequence_shortExact p q j k h hcover I
  let c : A ⨯ B ⟶ Seq.X₂ := prod.map ca cb
  let δ : A ⨯ B ⟶ C := liftToOpenAffineQCCounit T (p ≫ j) b hMq (c ≫ Seq.g)
  have hδ : δ ≫ cc = c ≫ Seq.g :=
    liftToOpenAffineQCCounit_fac T (p ≫ j) b hMq (c ≫ Seq.g)
  have : QuasiIso ca := openAffineQCCounit_quasiIso R j I a b hab hinj hqc
  have : QuasiIso cb := openAffineQCCounit_quasiIso S k I a b hab hinj hqc
  have : QuasiIso cc := openAffineQCCounit_quasiIso T (p ≫ j) I a b hab hinj hqc
  have : QuasiIso c := quasiIso_complex_prod_map ca cb
  let e₀ : (toDerived X).obj (A ⨯ B) ≅ (toDerived X).obj Seq.X₂ :=
    asIso ((toDerived X).map c)
  let e₁ : (toDerived X).obj C ≅ (toDerived X).obj Seq.X₃ :=
    asIso ((toDerived X).map cc)
  have hcomm : (toDerived X).map δ ≫ e₁.hom =
      e₀.hom ≫ (shortExactTriangle hSeq).rotate.mor₁ := by
    change (toDerived X).map δ ≫ (toDerived X).map cc =
      (toDerived X).map c ≫ (toDerived X).map Seq.g
    simp only [← Functor.map_comp, hδ]
  let eC : (toDerived X).obj (CochainComplex.mappingCone δ) ≅
      ((toDerived X).obj I)⟦(1 : ℤ)⟧ :=
    Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ (shortExactTriangle hSeq).rotate
      (mappingConeTriangle_distinguished δ)
      (rot_of_distTriang _ (shortExactTriangle_distinguished hSeq)) e₀ e₁ hcomm)
  let P := (CochainComplex.mappingCone δ)⟦(-1 : ℤ)⟧
  refine ⟨P, ?_, ?_, ⟨?_⟩⟩
  · intro i hi
    change IsZero ((CochainComplex.mappingCone δ).X (i + -1))
    apply (CochainComplex.mappingCone.isZero_X_iff δ _).mpr
    exact ⟨hM (i + -1 + 1) (by omega), hC (i + -1) (by omega)⟩
  · intro i
    let Q := SheafOfModules.isQuasicoherent X.ringCatSheaf
    change Q ((CochainComplex.mappingCone δ).X (i + -1))
    apply Q.prop_of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod δ (i + -1) i
        (by change i + -1 + 1 = i; omega)).symm
    exact Q.prop_of_iso (biprod.isoProd _ _).symm (Q.prop_prod _ _ (hMq i) (hCq (i + -1)))
  · exact ((toDerived X).commShiftIso (-1)).app (CochainComplex.mappingCone δ) ≪≫
      (shiftFunctor (Derived X) (-1)).mapIso eC ≪≫
      (shiftFunctorCompIsoId (Derived X) (1 : ℤ) (-1) (by omega)).app ((toDerived X).obj I)

open Quillen.Scheme.ProjectiveLine Quillen.Scheme.PolynomialLaurent

/-- Every original complex on the actual two-chart line with bounded QC
cohomology admits a constructed bounded termwise-QC model in the original
ambient derived category. No termwise QC hypothesis on the input is used. -/
theorem exists_bounded_quasicoherent_model (R : CommRingCat.{u})
    (K : Complex (twoChartLine R)) (a b : ℤ) (hab : a ≤ b) [K.IsGE a] [K.IsLE b]
    (hqc : ∀ i, (K.homology i).IsQuasicoherent) :
    ∃ P : Complex (twoChartLine R), (∀ i, i < a ∨ b + 1 < i → IsZero (P.X i)) ∧
      (∀ i, (P.X i).IsQuasicoherent) ∧
        Nonempty ((toDerived _).obj P ≅ (toDerived _).obj K) := by
  have : QuasiIso (K.πTruncGE a) := (K.quasiIso_πTruncGE_iff a).mpr inferInstance
  obtain ⟨I, s, hs, hinj, hl⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (K.truncGE a) a
  let := hs
  let := hl
  let q := K.πTruncGE a ≫ s
  have : QuasiIso q := inferInstance
  have : I.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact (exactAt_iff_of_quasiIsoAt q i).mp (K.exactAt_of_isLE b i hi)
  have hIq (i : ℤ) : (I.homology i).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (twoChartLine R).ringCatSheaf).prop_of_iso
      (isoOfQuasiIsoAt q i) (hqc i)
  obtain ⟨P, hPb, hPq, ⟨eP⟩⟩ := exists_bounded_qc_model_of_twoAffine_injective
    (.of (Polynomial R)) (.of (Polynomial R)) (.of (LaurentPolynomial R))
    (laurentPlus R) (laurentMinus R) (plusChart R) (minusChart R)
    (chart_isPullback R) (charts_jointly_surjective R) I a b hab hinj hIq
  exact ⟨P, hPb, hPq, ⟨eP ≪≫ (asIso ((toDerived _).map q)).symm⟩⟩

/-- An arbitrary intrinsic perfect bounded-below derived object on the actual
line has a genuine bounded-below termwise-QC representative. This is a producer,
not a supplied replacement premise. -/
theorem exists_quasicoherent_model_of_perfect_plus (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (twoChartLine R).Modules)
    (hK : perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj K)) :
    ∃ P : CochainComplex.Plus (twoChartLine R).Modules,
      (∀ i, (P.obj.X i).IsQuasicoherent) ∧ Nonempty (DerivedCategory.Plus.Q.obj P ≅ K) := by
  obtain ⟨L, ⟨eL⟩⟩ :=
    (perfectDerivedObjects_iff_exists_representative (twoChartLine R) _).mp hK
  obtain ⟨c, b, hb⟩ := locallyPerfect_homology_bounded L.property
  let a := min c b
  have : L.obj.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (hb i (Or.inl (by dsimp [a] at hi; omega)))
  have : L.obj.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (hb i (Or.inr hi))
  obtain ⟨P, hPb, hPq, ⟨eP⟩⟩ := exists_bounded_quasicoherent_model R L.obj a b
    (min_le_right _ _) (locallyPerfect_quasicoherent_homology L.property)
  have : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).mpr
    (fun i hi => hPb i (Or.inl hi))
  let Pp : CochainComplex.Plus (twoChartLine R).Modules := ⟨P, a, inferInstance⟩
  exact ⟨Pp, hPq, ⟨DerivedCategory.Plus.ι.preimageIso (eP ≪≫ eL)⟩⟩

end Quillen.PerfectComplexes.ProjectiveLine
