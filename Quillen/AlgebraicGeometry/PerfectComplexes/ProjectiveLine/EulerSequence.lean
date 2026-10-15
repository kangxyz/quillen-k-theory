/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.LineTensorCompatibility
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOne
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativePerfectGeneration

/-!
# The original Euler sequence with strict-perfect coefficients

The tautological sequence is tensored with its original subline. Its quotient
is identified with the structure module by the actual determinant pairing.
The original tensor maps yield a natural degreewise sequence on strict-perfect
coefficients; finite local freeness of each coefficient term proves exactness.
Godement totalization and ordinary projection retain an actual short exact
sequence, using the flasque kernel terms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
open FlasqueCoefficients
variable (R : CommRingCat.{u})

/-- The original tautological sequence after literal left tensor by L. -/
def tensorTautological : ShortComplex (twoChartLine R).Modules :=
  (tautologicalSequence R).map (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R))

lemma tensorTautological_shortExact : (tensorTautological R).ShortExact :=
  (tautologicalSequence_shortExact R).map_of_exact _

/-- Original Euler maps, using the actual determinant pairing on the quotient. -/
def sequence : ShortComplex (twoChartLine R).Modules :=
  ShortComplex.mk (tensorTautological R).f
    ((tensorTautological R).g ≫ (tautologicalLineTensorQuotientIso R).hom)
    (by rw [← Category.assoc, (tensorTautological R).zero, zero_comp])

/-- The normalization changes only the quotient by the fixed determinant isomorphism. -/
def sequenceIso : tensorTautological R ≅ sequence R :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (tautologicalLineTensorQuotientIso R)
    (by simp [sequence]) (by simp [sequence])

lemma sequence_shortExact : (sequence R).ShortExact :=
  ShortComplex.shortExact_of_iso (sequenceIso R) (tensorTautological_shortExact R)

lemma sequence_f : (sequence R).f =
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
      (tautologicalLineInclusion R) := rfl

lemma sequence_g : (sequence R).g =
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
      (tautologicalQuotientMap R) ≫ tautologicalLinePairing R := rfl

/-- The fixed product distribution and right unitor identify the actual middle with L ⊕ L. -/
def middleIso : (sequence R).X₂ ≅ tautologicalLine R ⊞ tautologicalLine R :=
  asIso (prodComparison (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R))
      (SheafOfModules.unit (twoChartLine R).ringCatSheaf)
      (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) ≪≫
    prod.mapIso
      ((SheafOfModulesOfCommRing.tensorRightUnitIso (twoChartLine R).sheaf).app
        (tautologicalLine R))
      ((SheafOfModulesOfCommRing.tensorRightUnitIso (twoChartLine R).sheaf).app
        (tautologicalLine R)) ≪≫
    (biprod.isoProd (tautologicalLine R) (tautologicalLine R)).symm

/-- Each endpoint tensor is the original sheafified tensor with a fixed Euler endpoint. -/
def endpointComplex (M : (twoChartLine R).Modules) :
    StrictPerfect (Spec R) ⥤ Complex (twoChartLine R) :=
  (strictPerfect (Spec R)).ι ⋙ pullbackComplex (projection R) ⋙ tensorByLineComplex M

instance endpointComplex_additive (M : (twoChartLine R).Modules) :
    (endpointComplex R M).Additive := by unfold endpointComplex; infer_instance

/-- Tensoring the actual first Euler arrow is natural in the original coefficient complex. -/
def first : endpointComplex R (sequence R).X₁ ⟶ endpointComplex R (sequence R).X₂ :=
  Functor.whiskerLeft ((strictPerfect (Spec R)).ι ⋙ pullbackComplex (projection R))
    ((moduleTensorCoefficientMap (twoChartLine R) (sequence R).f).mapHomologicalComplex (.up ℤ))

/-- Tensoring the actual quotient Euler arrow is natural in the original coefficient complex. -/
def second : endpointComplex R (sequence R).X₂ ⟶ endpointComplex R (sequence R).X₃ :=
  Functor.whiskerLeft ((strictPerfect (Spec R)).ι ⋙ pullbackComplex (projection R))
    ((moduleTensorCoefficientMap (twoChartLine R) (sequence R).g).mapHomologicalComplex (.up ℤ))

lemma first_second : first R ≫ second R = 0 := by
  apply NatTrans.ext
  funext A
  apply HomologicalComplex.Hom.ext
  funext n
  change (moduleTensorByLineRight
    (((pullbackComplex (projection R)).obj A.obj).X n)).map (sequence R).f ≫
      (moduleTensorByLineRight
        (((pullbackComplex (projection R)).obj A.obj).X n)).map (sequence R).g = 0
  rw [← Functor.map_comp, (sequence R).zero, Functor.map_zero]

/-- The actual coefficient Euler short complex, retaining the first-variable tensor maps. -/
def coefficientSequence (A : StrictPerfect (Spec R)) : ShortComplex (Complex (twoChartLine R)) :=
  ShortComplex.mk ((first R).app A) ((second R).app A) (NatTrans.congr_app (first_second R) A)

/-- Each pulled-back coefficient term is finite locally free; no arbitrary flatness is assumed. -/
lemma coefficientSequence_shortExact (A : StrictPerfect (Spec R)) :
    (coefficientSequence R A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let : IsFiniteLocallyFree (Spec R) (A.obj.X n) := A.property.2 n
  let : IsFiniteLocallyFree (twoChartLine R)
      (((pullbackComplex (projection R)).obj A.obj).X n) :=
    finiteLocallyFree_pullback (projection R) (A.obj.X n)
  change ((sequence R).map (moduleTensorByLineRight
    (((pullbackComplex (projection R)).obj A.obj).X n))).ShortExact
  exact (sequence_shortExact R).map_of_exact _

/-- Every endpoint keeps each specified strict lower bound of the original coefficient. -/
lemma endpointComplex_isStrictlyGE (M : (twoChartLine R).Modules)
    (A : StrictPerfect (Spec R)) (a : ℤ) [A.obj.IsStrictlyGE a] :
    ((endpointComplex R M).obj A).IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (moduleTensorLeftFunctor (twoChartLine R) M).map_isZero
    ((Scheme.Modules.pullback (projection R)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE A.obj a n hn))

/-- Literal Godement totalization of the original coefficient Euler sequence. -/
def totalSequence (A : StrictPerfect (Spec R)) : ShortComplex (Complex (twoChartLine R)) :=
  (coefficientSequence R A).map (godementTotal (twoChartLine R))

lemma totalSequence_shortExact (A : StrictPerfect (Spec R)) :
    (totalSequence R A).ShortExact :=
  godementTotal_shortExact (coefficientSequence_shortExact R A)

/-- Every term of the actual totalized kernel is flasque. -/
lemma totalSequence_kernel_flasque (A : StrictPerfect (Spec R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque ((totalSequence R A).X₁.X n).presheaf := by
  obtain ⟨a, b, hab⟩ := A.property.1
  let : A.obj.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ a).mpr
    (fun i hi => hab i (Or.inl hi))
  let K := (endpointComplex R (sequence R).X₁).obj A
  let : K.IsStrictlyGE a := endpointComplex_isStrictlyGE R _ A a
  exact godementTotal_isFlasque K a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE K a i hi) n

/-- Literal ordinary projection of the actual totalized Euler sequence. -/
def pushedSequence (A : StrictPerfect (Spec R)) : ShortComplex (Complex (Spec R)) :=
  (totalSequence R A).map
    ((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ))

/-- Original totalization and projection retain short exactness through the flasque kernel. -/
lemma pushedSequence_shortExact (A : StrictPerfect (Spec R)) :
    (pushedSequence R A).ShortExact :=
  pushforwardComplex_shortExact_of_flasque_kernel (projection R)
    (totalSequence_shortExact R A) (totalSequence_kernel_flasque R A)

end Quillen.PerfectComplexes.ProjectiveLine.Euler
