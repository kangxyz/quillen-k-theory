import Quillen.PerfectComplexes.VectorBundleInclusion
import Quillen.PerfectComplexes.Restriction
import Quillen.PerfectComplexes.LocalRestriction
import Quillen.PerfectComplexes.LocalLifting
import Quillen.PerfectComplexes.Support
import Quillen.PerfectComplexes.Closure
import Quillen.PerfectComplexes.PerfectSupport
import Quillen.PerfectComplexes.SplitSupport
import Quillen.PerfectComplexes.SplitComparison
import Quillen.PerfectComplexes.QuillenComparison

/-!
# Public strict and locally-perfect connective K-theory

This interface exposes canonical maps from public scheme K, the actual
quasi-isomorphism Waldhausen S-construction,
strict and locally-perfect K-groups with their actual support/restriction maps,
and the genuinely local perfectness predicate in the actual derived localization.
Both ambient-monomorphism and degreewise-split cofibration models, with
perfect quotient, are provided, and their canonical comparison maps are proved
to be equivalences in every nonnegative degree. It does not identify
strict-perfect K with all-perfect K or with the existing vector-bundle Q model.
Those comparison and localization theorems require separate proofs.
-/
