"""The ETH atlas keeps paper and formalization reading routes distinct."""

import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "walkthroughs" / "eth"


class EthAtlasTests(unittest.TestCase):
    """Protect mathematical distinctions in the first proof atlas."""

    def test_source_bindings_match_the_pinned_walkthrough(self) -> None:
        """Every atlas argument points to real, qualified outline mappings."""
        atlas = json.loads((ROOT / "atlas.json").read_text())
        outline = json.loads((ROOT / "outline.json").read_text())
        self.assertEqual(atlas["commit"], outline["project"]["commit"])
        statements = {node["id"]: node for node in outline["nodes"]}
        for node in atlas["nodes"]:
            statement = statements[node["statement"]]
            names = {entry["name"] for entry in statement["lean"]}
            self.assertTrue(set(node["declarations"]) <= names)
            self.assertNotIn("status", node)
        self.assertFalse((ROOT / "EthWalkthrough.glitnir.json").exists())

    def test_paper_and_lean_routes_do_not_conflate_counting_and_deciding(self) -> None:
        """Lean's route uses the Main Theorem; the paper uses Theorem 2."""
        atlas = json.loads((ROOT / "atlas.json").read_text())
        routes = {route["id"]: route for route in atlas["routes"]}
        self.assertIn("thm2", routes["paper"]["supports"]["eth"])
        self.assertEqual(routes["lean"]["supports"]["eth"], ["wrap"])
        self.assertEqual(routes["lean"]["supports"]["wrap"], ["thm1"])
        nodes = {node["id"]: node for node in atlas["nodes"]}
        self.assertIn("decision-only", nodes["thm2"]["difference"])
        self.assertEqual(nodes["combine"]["declarations"], ["CountedRoute.corMinHolds"])
        self.assertEqual(nodes["wrap"]["declarations"], ["Wrap.countingBoundImpliesFailureOfETH"])


class EthAtlasDepthTests(unittest.TestCase):
    """The counted-pieces route reaches actual intermediate source declarations."""

    def test_counted_pieces_reaches_the_padding_machine(self) -> None:
        """Several mathematical layers stay navigable and bound to exact names."""
        atlas = json.loads((ROOT / "atlas.json").read_text())
        nodes = {node["id"]: node for node in atlas["nodes"]}
        route = next(r for r in atlas["routes"] if r["id"] == "lean")
        path = ["appB", "half_bridge", "padded_bound", "counted_cost", "pad_machine"]
        for parent, child in zip(path, path[1:]):
            self.assertIn(child, route["supports"][parent])
        self.assertIn("PiecesCounted.padThen_runs", nodes["pad_machine"]["declarations"])
        self.assertIn("PiecesCounted.computes_of_answer", nodes["counted_cost"]["declarations"])
        self.assertIn("state", nodes["pad_machine"]["scope"])
        self.assertTrue(nodes["padded_bound"]["difference"])


if __name__ == "__main__":
    unittest.main()
