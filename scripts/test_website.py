"""Integration checks for compiler-derived dependencies and static source links."""
import json
import unittest
from pathlib import Path
from urllib.parse import unquote

from build_website import ROOT, OUT, authored_declarations, mask_comments


class WebsiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.graph = json.loads((OUT / "graph.json").read_text())
        cls.nodes = {n["id"]: n for n in cls.graph["nodes"]}
        cls.edges = {(e["source"], e["target"]) for e in cls.graph["edges"]}

    def test_complete_authored_inventory(self):
        self.assertEqual(set(self.nodes), {n["id"] for n in authored_declarations()})
        self.assertEqual(len(self.nodes), len(self.graph["nodes"]))
        self.assertEqual(sum(n["kind"] == "example" for n in self.nodes.values()), 10)
        self.assertTrue(self.nodes["WordRam.Examples.r0"]["private"])
        for n in self.nodes.values():
            self.assertGreater(len(n["description"]), 20, n["id"])

    def test_lean_dependencies_include_implicit_and_grouped_references(self):
        for edge in [
            ("WordRam.Steps.run_eq", "WordRam.run_resume"),
            ("WordRam.update_other", "WordRam.step_frame"),
            ("WordRam.Step", "WordRam.Steps"),  # Inductive constructor argument.
            ("WordRam.Registers", "WordRam.State"),  # Structure field.
            ("WordRam.Operand", "WordRam.Instr"),  # Instruction constructors.
            ("WordRam.Examples.r0", "WordRam.Examples.arithmetic"),  # Private name.
            ("WordRam.wordFintype", "WordRam.randomMemoryLaw"),  # Inferred instance.
            ("WordRam.probability_two_cells", "Checks.example_26"),  # Anonymous proof.
            ("StaticSet.QuerySpec", "PerfectHash.DictionarySpec"),
            ("StaticSet.QuerySpec.after_overwrite", "PerfectHash.DictionarySpec.query_after_build"),
        ]:
            self.assertIn(edge, self.edges)
        self.assertNotIn(("WordRam.update", "WordRam.word"), self.edges)

    def test_dictionary_module_labels_are_distinct(self):
        self.assertEqual(self.nodes["StaticSet.QuerySpec"]["module"], "StaticSet.Specification")
        self.assertEqual(self.nodes["PerfectHash.DictionarySpec"]["module"], "PerfectHash.Specification")
        self.assertEqual(len(self.graph["modules"]), len(set(self.graph["modules"])))

    def test_edges_and_reverse_index_agree(self):
        for e in self.graph["edges"]:
            a, b = e["source"], e["target"]
            self.assertIn(a, self.nodes)
            self.assertIn(b, self.nodes)
            self.assertNotEqual(a, b)
            self.assertTrue(set(e["roles"]) <= {"type", "body"})
        for n in self.nodes.values():
            self.assertEqual(set(n["dependencies"]), {a for a, b in self.edges if b == n["id"]})
            self.assertEqual(set(n["dependents"]), {b for a, b in self.edges if a == n["id"]})

    def test_every_source_link_and_snapshot(self):
        for n in self.nodes.values():
            with self.subTest(name=n["id"]):
                path, anchor = n["sourceUrl"].split("#")
                page = (OUT / unquote(path)).read_text()
                self.assertIn(f'id="{anchor}"', page)
                original = (ROOT / n["file"]).read_text()
                self.assertEqual((OUT / n["leanUrl"]).read_text(), original)
                self.assertEqual(n["source"], "\n".join(original.splitlines()[n["line"] - 1:n["endLine"]]))
                self.assertNotIn("WebsiteExample", n["source"])

    def test_no_description_drift(self):
        descriptions = json.loads((ROOT / "website/descriptions.json").read_text())
        self.assertEqual(set(descriptions), set(self.nodes))

    def test_nested_comments_preserve_source_positions(self):
        source = '/- outer\n /- theorem fake : False -/\n-/\ndef real := "-- /-" -- comment\n'
        masked = mask_comments(source)
        self.assertEqual(len(source), len(masked))
        self.assertEqual(source.count("\n"), masked.count("\n"))
        self.assertNotIn("theorem fake", masked)
        self.assertIn('def real := "-- /-"', masked)


if __name__ == "__main__":
    unittest.main()
