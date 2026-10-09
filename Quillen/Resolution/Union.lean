import Quillen.Resolution.Bounded
import Quillen.Topology.FilteredRealization.NerveColimit
import Quillen.Topology.FilteredRealization.HomotopyEquivalence
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# The actual filtered union of resolution-length Q-categories

The indexing category is the natural numbers. Every ambient Q-arrow lifts to
one finite stratum by bounding the resolutions of its source, target, apex,
left kernel, and right cokernel. Thus no uniform resolution bound is assumed.
Filtered nerve realization invariance is the already-proved topological theorem.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Simplicial

namespace Quillen.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [E.IsKernelClosed P] [P.IsClosedUnderFiniteProducts]
  [h : Fact (E.ResolutionHypothesis P)]

/-- Universe-compatible natural-number index for the resolution strata. -/
abbrev StratumIndex := AsSmall.{u} ℕ

/-- The finite resolution length indexing this stage. -/
abbrev stratumRank (j : StratumIndex.{u}) : ℕ := AsSmall.down.obj j

/-- A natural number viewed as an index. -/
abbrev stratumIndex (n : ℕ) : StratumIndex.{u} := AsSmall.up.obj n

/-- The strict diagram of the actual inherited Q-categories. -/
@[implicit_reducible]
def stratumQDiagram : StratumIndex.{u} ⥤ Cat.{u,u} where
  obj j := Cat.of (stratumExactStructure E P (stratumRank j)).QCategory
  map f := (stratumTransition E P (leOfHom (AsSmall.down.map f))).mapQ.toCatHom
  map_id j := by
    apply Cat.Hom.ext
    change (ExactFunctor.id (stratumExactStructure E P (stratumRank j))).mapQ = 𝟭 _
    exact ExactFunctor.mapQ_id _
  map_comp f g := by
    apply Cat.Hom.ext
    exact ExactFunctor.mapQ_comp
      (stratumTransition E P (leOfHom (AsSmall.down.map f)))
      (stratumTransition E P (leOfHom (AsSmall.down.map g)))

/-- The canonical ambient inclusions assemble to a strict categorical cocone. -/
@[implicit_reducible]
def stratumQCocone : Cocone (stratumQDiagram E P) where
  pt := Cat.of E.QCategory
  ι :=
    { app j := (exactInclusion E (E.ResolutionLength P (stratumRank j))).mapQ.toCatHom
      naturality {j k} f := by
        apply Cat.Hom.ext
        change (stratumTransition E P (leOfHom (AsSmall.down.map f))).mapQ ⋙
          (exactInclusion E (E.ResolutionLength P (stratumRank k))).mapQ =
            (exactInclusion E (E.ResolutionLength P (stratumRank j))).mapQ
        rw [← ExactFunctor.mapQ_comp, exactInclusionOfLE_comp] }

/-- A whole ambient Q-arrow, including its kernel and cokernel witnesses,
lifts to one genuine exact length stratum. -/
theorem stratumQCocone_arrowSurjective :
    FilteredNerveColimit.ArrowSurjective (stratumQDiagram E P) (stratumQCocone E P) := by
  rintro ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ ⟨s⟩
  change Span E.deflation E.inflation X Y at s
  obtain ⟨K, i, hi, hK⟩ := s.wl
  obtain ⟨Z, p, hp, hZ⟩ := s.wr
  obtain ⟨RX⟩ := h.out X
  obtain ⟨RY⟩ := h.out Y
  obtain ⟨RA⟩ := h.out s.apex
  obtain ⟨RK⟩ := h.out K
  obtain ⟨RZ⟩ := h.out Z
  let N := max RX.length (max RY.length (max RA.length (max RK.length RZ.length)))
  have hX : E.ResolutionLength P N X := ⟨RX, by dsimp [N]; omega⟩
  have hY : E.ResolutionLength P N Y := ⟨RY, by dsimp [N]; omega⟩
  have hA : E.ResolutionLength P N s.apex := ⟨RA, by dsimp [N]; omega⟩
  have hK' : E.ResolutionLength P N K := ⟨RK, by dsimp [N]; omega⟩
  have hZ' : E.ResolutionLength P N Z := ⟨RZ, by dsimp [N]; omega⟩
  let x : (E.ResolutionLength P N).FullSubcategory := ⟨X, hX⟩
  let y : (E.ResolutionLength P N).FullSubcategory := ⟨Y, hY⟩
  let a : (E.ResolutionLength P N).FullSubcategory := ⟨s.apex, hA⟩
  let t : Span (stratumExactStructure E P N).deflation (stratumExactStructure E P N).inflation x y :=
    { apex := a
      l := ObjectProperty.homMk s.l
      r := ObjectProperty.homMk s.r
      wl := (ExactSubcategory.deflation_iff E (E.ResolutionLength P N) _).2
        ⟨K, hK', i, hi, hK⟩
      wr := (ExactSubcategory.inflation_iff E (E.ResolutionLength P N) _).2
        ⟨Z, hZ', p, hp, hZ⟩ }
  refine ⟨stratumIndex N, Q.of _ _ x, Q.of _ _ y, Q.mkHom _ _ t, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl

/-- Objects lift in particular by lifting their identity arrows. -/
theorem stratumQCocone_objectSurjective :
    ∀ X : (stratumQCocone E P).pt, ∃ j, ∃ x : (stratumQDiagram E P).obj j,
      ((stratumQCocone E P).ι.app j).toFunctor.obj x = X := by
  intro X
  obtain ⟨j, x, _, _, hx, _, _⟩ := stratumQCocone_arrowSurjective E P (𝟙 X)
  exact ⟨j, x, hx⟩

/-- The stage inclusions already reflect equality of objects; no further
increase of the resolution bound is necessary. -/
theorem stratumQCocone_eventuallyEqualObjects :
    FilteredNerveColimit.EventuallyEqualObjects (stratumQDiagram E P) (stratumQCocone E P) := by
  intro j X Y hXY
  have hobj : X = Y := by
    rcases X with ⟨⟨X⟩⟩
    rcases Y with ⟨⟨Y⟩⟩
    have he := congrArg (fun T => T.obj.of) hXY
    change X.obj = Y.obj at he
    have he' : X = Y := ObjectProperty.FullSubcategory.ext he
    cases he'
    rfl
  exact ⟨j, 𝟙 j, congrArg ((stratumQDiagram E P).map (𝟙 j)).toFunctor.obj hobj⟩

instance stratumQCocone_faithful (j : StratumIndex.{u}) :
    (FilteredNerveColimit.leg (stratumQDiagram E P) (stratumQCocone E P) j).Faithful := by
  letI : (exactInclusion E (E.ResolutionLength P (stratumRank j))).toFunctor.Full :=
    inferInstanceAs (E.ResolutionLength P (stratumRank j)).ι.Full
  letI : (exactInclusion E (E.ResolutionLength P (stratumRank j))).toFunctor.Faithful :=
    inferInstanceAs (E.ResolutionLength P (stratumRank j)).ι.Faithful
  exact (exactInclusion E (E.ResolutionLength P (stratumRank j))).mapQ_faithful_of_fullyFaithful

/-- The ambient Q-nerve really is the filtered simplicial colimit of the
finite-resolution-length strata. -/
def stratumNerveCocone_isColimit :
    IsColimit (nerveFunctor.mapCocone (stratumQCocone E P)) :=
  FilteredNerveColimit.nerveCocone_isColimit (stratumQDiagram E P) (stratumQCocone E P)
    (stratumQCocone_objectSurjective E P) (stratumQCocone_arrowSurjective E P)
    (stratumQCocone_eventuallyEqualObjects E P)

/-- Each finite stratum includes by an actual homotopy equivalence into the
ambient Q-classifying space, despite the absence of any common finite bound. -/
def stratumToAmbientHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (stratumExactStructure E P n).KSpace E.KSpace :=
  FilteredRealization.stageHomotopyEquiv
    (stratumQDiagram E P ⋙ nerveFunctor) (nerveFunctor.mapCocone (stratumQCocone E P))
    (stratumNerveCocone_isColimit E P)
    (fun f => stratumTransitionHomotopyEquiv E P (leOfHom (AsSmall.down.map f)))
    (fun f => by
      convert stratumTransitionHomotopyEquiv_toFun E P (leOfHom (AsSmall.down.map f)) using 1 <;> rfl)
    (stratumIndex n)

@[simp] theorem stratumToAmbientHomotopyEquiv_toFun (n : ℕ) :
    (stratumToAmbientHomotopyEquiv E P n).toFun =
      (classifyingSpaceMap (exactInclusion E (E.ResolutionLength P n)).mapQ).hom := by
  rfl

end Quillen.Resolution
