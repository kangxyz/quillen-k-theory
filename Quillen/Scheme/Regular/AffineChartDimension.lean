import Quillen.Scheme.Regular.ResolutionProperty
import Quillen.Scheme.Coherent.Restriction
import Quillen.Scheme.VectorBundle.Restriction

/-!
# Projective dimension on actual affine charts

These are local module projective dimensions, not projective dimensions of
sheaves in a global category. In particular, only the restriction of a
vector bundle to an affine chart is used as a projective object.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf
variable {X : AlgebraicGeometry.Scheme.{u}} [IsLocallyNoetherian X]
  (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j]

/-- Restrict a genuine coherent sheaf to an affine chart, take its finite
module under the tilde equivalence, and forget finiteness. -/
def coherentChartModule : CoherentScheme.Coherent X ⥤ ModuleCat.{u} R := by
  letI := CoherentScheme.noetherian_affineChart R j
  exact CoherentScheme.coherentRestriction j ⋙
    (CoherentScheme.coherentSpecModuleEquivalence R).functor ⋙
      (CoherentScheme.finiteModule R).ι

instance coherentChartModule_additive : (coherentChartModule R j).Additive := by
  have := CoherentScheme.noetherian_affineChart R j
  let E := CoherentScheme.coherentSpecModuleEquivalence R
  let := preservesBinaryBiproducts_of_preservesBinaryProducts E.functor
  have : E.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  dsimp [coherentChartModule]
  infer_instance

/-- Actual global coherent short exact sequences stay exact in the module
category of an affine chart. -/
theorem coherentChartModule_shortExact (S : ShortComplex (CoherentScheme.Coherent X))
    (hS : S.ShortExact) : (S.map (coherentChartModule R j)).ShortExact := by
  have := CoherentScheme.noetherian_affineChart R j
  exact ((hS.map_of_exact (CoherentScheme.coherentRestriction j)).map_of_exact
    (CoherentScheme.coherentSpecModuleEquivalence R).functor).map_of_exact
      (CoherentScheme.finiteModule R).ι

/-- Finite local freeness on the affine chart is exactly projectivity of
its finite section module, expressed in the ambient module category. -/
theorem coherentChartModule_projective_iff (M : CoherentScheme.Coherent X) :
    Projective ((coherentChartModule R j).obj M) ↔
      IsFiniteLocallyFree (Spec R) (M.obj.restrict j) := by
  have := CoherentScheme.noetherian_affineChart R j
  let N := (CoherentScheme.coherentRestriction j).obj M
  change Projective (((CoherentScheme.coherentSpecModuleEquivalence R).functor.obj N).obj) ↔
    coherentVectorBundle (Spec R) N
  exact (IsProjective.iff_projective
    (((CoherentScheme.coherentSpecModuleEquivalence R).functor.obj N).obj)).symm.trans
      (coherentVectorBundle_iff_projective R N).symm

/-- A global vector bundle gives a projective module on every affine chart;
no global sheaf-projectivity assertion is made. -/
theorem coherentChartModule_projective (M : CoherentScheme.Coherent X)
    (hM : coherentVectorBundle X M) : Projective ((coherentChartModule R j).obj M) := by
  have : IsFiniteLocallyFree X M.obj := hM
  exact (coherentChartModule_projective_iff R j M).mpr (finiteLocallyFree_restrict j M.obj)

/-- Each genuine global vector-bundle cover drops the local projective
dimension of its coherent kernel by one on every affine chart. -/
theorem coherentChartModule_syzygy (S : ShortComplex (CoherentScheme.Coherent X))
    (hS : S.ShortExact) (hP : coherentVectorBundle X S.X₂) (n : ℕ)
    [HasProjectiveDimensionLE ((coherentChartModule R j).obj S.X₃) (n + 1)] :
    HasProjectiveDimensionLE ((coherentChartModule R j).obj S.X₁) n := by
  have hdim : HasProjectiveDimensionLT (S.map (coherentChartModule R j)).X₃ (n + 2) := by
    change HasProjectiveDimensionLE ((coherentChartModule R j).obj S.X₃) (n + 1)
    infer_instance
  exact ((coherentChartModule_shortExact R j S hS).hasProjectiveDimensionLT_X₃_iff n
    (coherentChartModule_projective R j S.X₂ hP)).mp hdim

/-- The actual chart module is finite. -/
instance coherentChartModule_finite (M : CoherentScheme.Coherent X) :
    Module.Finite R ((coherentChartModule R j).obj M) := by
  have := CoherentScheme.noetherian_affineChart R j
  change Module.Finite R
    (((CoherentScheme.coherentSpecModuleEquivalence R).functor.obj
      ((CoherentScheme.coherentRestriction j).obj M)).obj)
  infer_instance

end Quillen.SchemeSheaf

namespace Quillen.Scheme

/-- A finite affine subcover of a quasi-compact scheme, retaining the
actual chart rings and open-immersion maps from the chosen affine cover. -/
def finiteAffineOpenCover (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X] :
    X.AffineOpenCover where
  I₀ := X.affineCover.finiteSubcover.I₀
  X i := X.affineOpenCover.X (X.affineCover.idx i.1)
  f := X.affineCover.finiteSubcover.f
  idx := X.affineCover.finiteSubcover.idx
  covers := X.affineCover.finiteSubcover.covers
  map_prop := X.affineCover.finiteSubcover.map_prop

instance finiteAffineOpenCover_finite (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X] :
    Fintype (finiteAffineOpenCover X).I₀ := by
  change Fintype X.affineCover.finiteSubcover.I₀
  infer_instance

end Quillen.Scheme
