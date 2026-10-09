# Local-perfect closure: checked proof architecture

The former local-closure gap is now filled by actual Lean proofs. The objects
are locally isomorphic in quasi-isomorphism localization to globally bounded
finite-locally-free complexes on neighborhoods. Global strict representability
and global projectivity of vector bundles are never assumed.

## Checked geometric argument

1. `LocalLifting` uses the existing local splitting of vector-bundle quotients
   to lift maps from finite locally free sheaves through arbitrary epis on
   actual open subschemes. Factoring through cycles gives the exact-sequence
   version of local projective lifting.
2. `LocalHomotopyStep` corrects an approximate nullhomotopy at one degree
   after shrinking. Acyclicity makes the differential onto cycles surjective;
   the finite locally free source term supplies the local correction.
3. `LocalNullHomotopy` performs only finitely many descending corrections
   because the strict source is termwise bounded. It keeps successive opens
   as a composite immersion, then transports the resulting actual homotopy
   using the restriction-composition isomorphism.
4. `LocalQuasiIsoLifting` uses the acyclic cone of a quasi-isomorphism and
   exactness of its actual homotopy-category triangle to lift a map locally
   through that quasi-isomorphism up to chain homotopy.
5. `DerivedMorphisms` combines this lifting with mathlib's derived fraction
   calculus to produce local chain representatives of derived morphisms
   having strict-perfect source. `DerivedRepresentativeNaturality` proves
   compatibility with every derived lift of restriction.
6. `DerivedStructure` equips the constructed localization with mathlib's
   standard triangulated structure and exact derived restriction.
7. `LocalModels` refines endpoint representatives to a common neighborhood
   and converts arbitrary open-immersion witnesses to literal open subsets.
8. `LocalTriangles` represents a distinguished triangle locally by the cone
   of a genuine chain map between strict complexes. `Closure` proves this
   cone and all shifts strict perfect using actual termwise bounds.
9. `Extension` applies this to the inverse rotation of the derived triangle
   of a short exact sequence, proving its middle object locally perfect.
10. `KTheory` and `PerfectSupport` instantiate the proved Waldhausen adapter
    and actual S-construction groups, with restriction/support/comparison maps.

## Remaining theorem work

- Gillet–Waldhausen equivalence. The canonical exact-category Q/S comparison
  and strict/local perfect change-of-cofibrations equivalences are now proved.
- Strict-to-local comparison equivalence under geometric resolution hypotheses.
- Waldhausen additivity and the relevant approximation/cofinality results.
- Nonconnective spectra, extension across opens, and Thomason–Trobaugh
  localization. Defining supported objects and their maps does not establish
  a localization sequence.

For a TT-labelled endpoint on non-quasi-compact schemes, the separately
imposed global Tor-amplitude convention must also be addressed explicitly.
The current `PerfectK` is identified by its exact local-perfect object model.
