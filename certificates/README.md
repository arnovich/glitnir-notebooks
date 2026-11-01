# AIFSafety: a certified safety proof for antithetic integral feedback

`AIFSafety` proves, in Lean, that Asgard's antithetic integral feedback circuit
(`Gimle.Asgard.Examples.AIF`) keeps its output in a safe range. For every fixed
$\eta \in [8, 12]$, the circuit started at zero has exactly one behaviour, and
that behaviour keeps the output within $0 \le x_2 \le 16/5$ for all $t \ge 0$,
and within $x_2 \le 5/2$ from $t = 30$ on.

The main theorems are in `AIFSafety/CompleteSafety.lean`:

- `forward_safety`: safety for all time, and that a behaviour exists;
- `hundred_safety`: the same bound on $[0, 100]$;
- `forward_contract`, `hundred_contract`: the same statements as Forseti
  trajectory contracts;
- `later_output`: $x_2 \le 5/2$ from $t = 30$ on;
- `species_nonnegative`, `realization_unique`, `safe_behavior_exists`.

Every theorem depends only on Lean's standard axioms: `propext`,
`Classical.choice` and `Quot.sound`. Building a module prints the axioms of its
main theorems, and the root theorems' reports cover everything they use. Lean
prints names relative to the open namespaces, so `#print axioms` alone does not
rule out a declared axiom that shares a standard axiom's short name; the
library declares no axioms.

`AIFSafety/NotebookStatements.lean` imports the
[AntitheticFeedback notebook](../examples/biochemistry/AntitheticFeedback.lean)
and proves its two cited definitions, `ForwardSafety` and `LaterOutput`, from
`forward_safety` and `later_output`.

## How the proof is built

The first thirty time units are covered by a moving tube around a numerically
computed trajectory. The tube is cut into 8 bins of $\eta$ and 370 time slabs,
2960 cells in all. Each cell is checked by kernel evaluation against the
candidate mesh. The checks cover the drift inequality, with its square
certificates; the tube's containment margin; and the output enclosure. A
composition rule in Forseti Lean turns one checked cell per slab, and matching
joins between neighbours, into a tube that no behaviour can leave. At $t = 30$, a
quadratic Lyapunov function takes over and carries the bound to all later time.

The numerical trajectory and the mesh are untrusted inputs. They enter as
rational data, and the kernel checks every inequality the proof uses about them.
A wrong mesh makes a cell fail to build; it cannot make the theorem false.

| Modules | Content |
| --- | --- |
| `Cell` | What a cell must check, and the two theorems a passing cell gives |
| `MeshGeometry`, `MeshBin0`–`MeshBin7`, `CandidateMesh` | The candidate mesh: knots, slabs, coverage and joins |
| `Cells/Bin{b}/Slab{i}` | One module per cell, `b` in 0–7 and `i` in 0–369 |
| `CompleteFamilyBin{b}Slabs{lo}To{hi}`, `CompleteFamilyBin{b}`, `CompleteFamily` | Every cell, collected by slab range and bin |
| `Startup*`, `CircuitSolution`, `UniformPrefix*`, `TerminalEnergy`, `TerminalEntryBin*` | The start of the tube, the circuit's solution, and the hand-off at $t = 30$ |
| `SafetyComposition`, `TrajectoryContract`, `CompleteSafety` | The composition into the final theorems |
| `NotebookStatements` | The notebook's cited statements, proved from the final theorems |
| `*Regressions` | Statements that changed inputs are rejected |

These sources were generated, and are committed so the proof can be checked
without the generator. `Cell`, `NotebookStatements` and the root `AIFSafety`
are written by hand.

## Building it

`AIFSafety` is not a default target of this project. To check all of it, run:

```sh
lake build AIFSafety
```

A cell takes 36 to 61 seconds (about 37 on average) and over 7 GB of memory, and the whole library
about 30 hours of processor time (measured with six modules at a time on a
twelve-thread machine, about five hours of wall time). Lake starts as many
modules at once as it can, so on a machine with less than about 8 GB of memory
per core, build it in chunks, one cell or one range module at a time:

```sh
lake build AIFSafety.Cells.Bin3.Slab100
lake build AIFSafety.CompleteFamilyBin3Slabs81To120
```

The [AntitheticFeedback notebook](../examples/biochemistry/AntitheticFeedback.lean)
explains the proof, and checks the circuit's equations, the composition rule and
one cell in Glitnir.
