# Rebuilding the restricted notebooks after the library split

The 16 restricted notebooks remain readable public snapshots. Their committed
Glitnir results describe the saved source at the original dependency pins. A
recheck against newer Asgard/Forseti revisions requires a maintainer with access
to the private libraries; changing an import also requires a fresh Glitnir check
and a new recorded result. Do not edit a `.glitnir.json` record by hand.

Two notebooks directly import modules whose *module paths* moved into the private
Gimle Lean library:

| Notebook | Old import | New import |
| --- | --- | --- |
| `examples/finance/RobustHedge.lean` | `Gimle.Forseti.Hedging` | `GimleLean.Finance.PathwiseHedging` |
| `examples/pdes/Euler.lean` | `Gimle.Asgard.Examples.EulerBand` | `GimleLean.Examples.EulerBand` |
| `examples/pdes/Euler.lean` | `Gimle.Asgard.Streams.EulerRadius` | `GimleLean.Streams.EulerRadius` |
| `examples/pdes/Euler.lean` | `Gimle.Asgard.Streams.VorticityTable` | `GimleLean.Streams.VorticityTable` |

Other notebooks import product modules that have already been updated internally.
When repinning the root Lake project, compile and recheck each notebook before
changing its saved record. Preserve circuit/Hoare claims where they are the
subject of the notebook; the public Atlas Fibonacci and Jordan notebooks are
separate matrix presentations.

The complete source-to-module map is maintained in the private Gimle Lean
`MIGRATIONS.json`. The Asgard/Forseti architecture guides explain which
mathematics moved and which circuit or contract interfaces remain.
