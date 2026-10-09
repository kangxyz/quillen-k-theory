import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The actual truncated times in finite mapping-cylinder lifts -/
noncomputable section
open scoped Topology unitInterval
namespace Quillen.TheoremB.CompactMappingCylinder

/-- Follow a shifted path until time one. -/
def addTime (s t : unitInterval) : unitInterval :=
  ⟨min ((s : ℝ) + (t : ℝ)) 1,le_min (add_nonneg s.2.1 t.2.1) zero_le_one,min_le_right _ _⟩
/-- The remaining path time after traversing a cylinder segment. -/
def remainingTime (t s : unitInterval) : unitInterval :=
  ⟨max ((t : ℝ) - (s : ℝ)) 0,le_max_right _ _,max_le (by linarith [t.2.2,s.2.1]) zero_le_one⟩

@[fun_prop] theorem continuous_addTime : Continuous (fun z : unitInterval × unitInterval ↦ addTime z.1 z.2) := by
  unfold addTime
  fun_prop
@[fun_prop] theorem continuous_remainingTime :
    Continuous (fun z : unitInterval × unitInterval ↦ remainingTime z.1 z.2) := by
  unfold remainingTime
  fun_prop
@[simp] theorem addTime_zero (s : unitInterval) : addTime s 0 = s := by
  apply Subtype.ext
  simp [addTime,min_eq_left s.2.2]
@[simp] theorem zero_addTime (t : unitInterval) : addTime 0 t = t := by
  apply Subtype.ext
  simp [addTime,min_eq_left t.2.2]
@[simp] theorem remainingTime_zero (t : unitInterval) : remainingTime t 0 = t := by
  apply Subtype.ext
  simp [remainingTime,max_eq_left t.2.1]
@[simp] theorem remainingTime_self (t : unitInterval) : remainingTime t t = 0 := by
  apply Subtype.ext
  simp [remainingTime]
theorem remainingTime_eq_zero {t s : unitInterval} (h : t ≤ s) : remainingTime t s = 0 := by
  apply Subtype.ext
  exact max_eq_right (sub_nonpos.mpr h)
theorem addTime_remainingTime {s t : unitInterval} (h : s ≤ t) :
    addTime s (remainingTime t s) = t := by
  apply Subtype.ext
  change min ((s : ℝ) + max ((t : ℝ) - (s : ℝ)) 0) 1 = (t : ℝ)
  rw [max_eq_left (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from h))]
  have he : (s : ℝ) + ((t : ℝ) - (s : ℝ)) = (t : ℝ) := by ring
  rw [he, min_eq_left t.2.2]
@[simp] theorem addTime_symm (s : unitInterval) : addTime s (unitInterval.symm s) = 1 := by
  apply Subtype.ext
  change min ((s : ℝ) + (1 - (s : ℝ))) 1 = 1
  simp

end Quillen.TheoremB.CompactMappingCylinder
