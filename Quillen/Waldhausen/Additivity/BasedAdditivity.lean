import Quillen.Waldhausen.Additivity.NormalizedEndpointHomotopies
import Quillen.Waldhausen.Additivity.NormalizedMixedHomotopy
import Quillen.Waldhausen.Additivity.BasedHomotopyTools
import Quillen.Waldhausen.Additivity.DiagonalKMap

/-! # Waldhausen additivity for the original chosen-zero K-maps

All three deformation homotopies have proved constant chosen-zero tracks.
After subdivision, the middle functor and the split sum therefore induce
the same based group map. Cancellation uses only surjectivity of the proved
actual forward subdivision map. The exact diagonal comparison then identifies
this equality with the original public normalized `KMap` homomorphisms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v

namespace Quillen.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
variable {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
variable (hs : IsCofibrationSequence V W a b)

/-- The actual rebased middle map and the common normalized separated sum
are homotopic relative to the displayed subdivided zero point. -/
def subdividedBasedAdditivityHomotopy :
    ((realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)).comp
      (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))).HomotopyRel
      (realizedDiagonalMap (normalizedSumMap V W hs.exactH hs.exactF))
      {subdivisionBasepoint V} := by
  let h₀ := homotopyRelOfFixed
    (normalizedIdentityEndpointRealizationHomotopy V W a hs.exactF hs.exactG hs.cofibration)
    (realizationPoint (diagonalZeroVertex V)) (realizationPoint (diagonalZeroVertex W))
    (normalizedIdentityEndpointRealizationHomotopy_fixed_zero V W a hs.exactF hs.exactG hs.cofibration)
  let hm := homotopyRelOfFixed
    (realizationSimplicialHomotopy
      (normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration))
    (subdivisionBasepoint V) (realizationPoint (diagonalZeroVertex W))
    (normalizedMixedRealizationHomotopy_fixed_zero V W a hs.exactF hs.exactG hs.cofibration)
  let h₁ := homotopyRelOfFixed
    (normalizedSeparatedEndpointRealizationHomotopy V W a b hs)
    (subdivisionBasepoint V) (realizationPoint (diagonalZeroVertex W))
    (normalizedSeparatedEndpointRealizationHomotopy_fixed_zero V W a b hs)
  have hm' :
      ((realizedDiagonalMap (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration)).comp
        (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))).HomotopyRel
        (realizedDiagonalMap (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration))
        {subdivisionBasepoint V} :=
    hm.cast (congrArg TopCat.Hom.hom (SSet.toTop.map_comp _ _)) rfl
  exact (homotopyRelPrecompPoint h₀
    (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
    (subdivisionBasepoint V) (horizontalEndpoint_basepoint V)).symm.trans (hm'.trans h₁)

/-- Equality of the actual canonically normalized diagonal group maps. -/
theorem diagonalKMap_additivity (n : ℕ) :
    diagonalKMap V W hs.exactG n =
      diagonalKMap V W (sumFunctor_isExact V W hs.exactH hs.exactF) n := by
  apply piMap_eq_of_based_precomp_surjective n
    (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
    (horizontalEndpoint_basepoint V) (subdivisionPiMap_surjective V n)
  exact (subdividedBasedAdditivityHomotopy V W a b hs).trans
    (subdividedBasedAdditivityHomotopy V W (sumInr H F) (sumProjection W H F)
      (splitIsCofibrationSequence V W hs.exactH hs.exactF)).symm

/-- Genuine additivity of the original public chosen-zero K-homomorphisms.
The right side is the map of the actual sum functor `H ⨿ F`; no alternative
K-map or unspecified comparison equivalence is substituted. -/
theorem KMap_additivity (n : ℕ) :
    KMap hs.exactG n = KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n := by
  have hg := diagonalKMap_naturality V W hs.exactG n
  have hs' := diagonalKMap_naturality V W (sumFunctor_isExact V W hs.exactH hs.exactF) n
  have he := diagonalKMap_additivity V W a b hs n
  ext q
  obtain ⟨p, rfl⟩ := (diagonalPiEquiv V n).surjective q
  calc
    KMap hs.exactG n (diagonalPiEquiv V n p) =
        diagonalPiEquiv W n (diagonalKMap V W hs.exactG n p) :=
      (DFunLike.congr_fun hg p).symm
    _ = diagonalPiEquiv W n (diagonalKMap V W (sumFunctor_isExact V W hs.exactH hs.exactF) n p) :=
      congrArg (diagonalPiEquiv W n) (DFunLike.congr_fun he p)
    _ = KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n (diagonalPiEquiv V n p) :=
      DFunLike.congr_fun hs' p

end Quillen.Waldhausen.Additivity
