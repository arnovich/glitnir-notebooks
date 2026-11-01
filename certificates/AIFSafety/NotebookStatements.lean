import AntitheticFeedback
import AIFSafety.CompleteSafety

/-! The antithetic feedback notebook writes the library's two main results out as
definitions and cites them without checking them. This module proves those
definitions, exactly as the notebook states them, from the library's theorems,
so the notebook cites what the library proves. -/
namespace AIFSafety.NotebookStatements

/-- The notebook's `ForwardSafety` is `AIFSafety.CompleteSafety.forward_safety`. -/
theorem forward_safety : Notebook.AntitheticFeedback.ForwardSafety :=
  AIFSafety.CompleteSafety.forward_safety

/-- The notebook's `LaterOutput` is `AIFSafety.CompleteSafety.later_output`. -/
theorem later_output : Notebook.AntitheticFeedback.LaterOutput :=
  AIFSafety.CompleteSafety.later_output

#print axioms forward_safety
#print axioms later_output
end AIFSafety.NotebookStatements
