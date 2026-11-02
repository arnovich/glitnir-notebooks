"""Static guards for workflow inputs that are easy to break silently."""

import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class RecheckWorkflowTests(unittest.TestCase):
    """Keep manual notebook selection and forced receipts wired to dispatch inputs."""

    def test_manual_dispatch_uses_its_own_inputs(self) -> None:
        """The select job cannot read its own not-yet-created outputs."""
        workflow = (ROOT / ".github/workflows/recheck.yml").read_text()
        self.assertIn("INPUT_ONLY: ${{ inputs.only }}", workflow)
        self.assertNotIn("INPUT_ONLY: ${{ needs.select.outputs.only }}", workflow)

    def test_recheck_shards_are_independent_and_keep_the_full_gate(self) -> None:
        """A slow notebook cannot time out the serial suite or cancel its peers."""
        workflow = (ROOT / ".github/workflows/recheck.yml").read_text()
        for required in (
            "matrix: ${{ steps.select.outputs.matrix }}",
            '--matrix --only "$selection"',
            "matrix: ${{ fromJSON(needs.select.outputs.matrix) }}",
            "glitnir_tag: ${{ steps.glitnir.outputs.tag }}",
            "GLITNIR_TAG: ${{ needs.select.outputs.glitnir_tag }}",
            "fail-fast: false", "max-parallel: 4", "timeout-minutes: 360",
            "ONLY: ${{ matrix.notebook }}",
            "name: notebook-recheck-${{ matrix.notebook }}",
            'python -m scripts.recheck --report recheck-report --only "${only[@]}"',
        ):
            self.assertIn(required, workflow)

    def test_manual_dispatch_can_force_named_decision_receipts(self) -> None:
        """A release recheck can refresh UNKNOWN cards as well as accepted blocks."""
        workflow = (ROOT / ".github/workflows/recheck.yml").read_text()
        self.assertIn("force_decisions:", workflow)
        self.assertIn("FORCE_DECISIONS: ${{ inputs.force_decisions }}", workflow)
        self.assertIn("--force-decision", workflow)


if __name__ == "__main__":
    unittest.main()
