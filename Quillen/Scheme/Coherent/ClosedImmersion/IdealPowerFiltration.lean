import Quillen.Scheme.Coherent.ClosedImmersion.IdealSupport
import Quillen.GTheory.FiniteModules.IdealPowerFiltration
import Quillen.Devissage.FiltrationFunctor

/-!
# Actual ideal-power filtrations of affine coherent sheaves

The actual finite-module tower IⁿM transports through the genuine affine
module/sheaf equivalence to a finite coherent-sheaf filtration. Its quotient
factors are annihilated by I, and its endpoint is the original sheaf.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme.ClosedImmersion.Ideal
open FiniteModuleLocalization.IdealClosedSupport
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

instance coherentSpecModuleEquivalence_inverse_additive :
    (coherentSpecModuleEquivalence R).inverse.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (coherentSpecModuleEquivalence R).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The actual inverse affine equivalence is exact. -/
def associatedCoherentExact :
    ExactFunctor (finiteModuleExactStructure.{u, u} R) (coherentExactStructure (Spec R)) where
  toFunctor := (coherentSpecModuleEquivalence R).inverse
  map_conflation _ h := h.map_of_exact _

/-- The actual associated coherent sheaf of an I-annihilated finite module
is itself annihilated by I. -/
theorem associatedCoherent_killed (M : FGModuleCat.{u} R) (hM : killedBy I M) :
    coherentKilledBy R I ((coherentSpecModuleEquivalence R).inverse.obj M) :=
  (killedBy I).prop_of_iso ((coherentSpecModuleEquivalence R).counitIso.app M).symm hM

/-- Every actual coherent sheaf supported on V(I) has its genuine finite
ideal-power filtration, transported from actual I-power submodules of its
finite global-section module and ending at the original sheaf. -/
theorem coherentIdealPowerFiltration (M : Coherent (Spec R))
    (hM : coherentSupportedAway (openMap R I) M) :
    Nonempty ((coherentExactStructure (Spec R)).Filtration (coherentKilledBy R I) M) := by
  obtain ⟨n, hn⟩ := (coherentSupportedAway_iff_pow_le_annihilator R I M).mp hM
  obtain ⟨F⟩ := idealPowerFiltration I ((coherentSpecModuleEquivalence R).functor.obj M) n hn
  let G := (associatedCoherentExact R).mapFiltration (associatedCoherent_killed R I) F
  exact ⟨G.ofIso ((coherentSpecModuleEquivalence R).unitIso.app M).symm⟩

end Quillen.CoherentScheme.ClosedImmersion.Ideal
