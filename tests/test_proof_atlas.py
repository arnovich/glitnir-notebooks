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


if __name__ == "__main__":
    unittest.main()
