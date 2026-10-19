"""Regression checks for dependency scheduling and exact axiom coverage."""
import threading
import unittest

import verify_project as verifier


def audit_line(name, axioms="propext, Classical.choice, Quot.sound"):
    return f"'{name}' depends on axioms: [{axioms}]\n"


class AxiomAuditTests(unittest.TestCase):
    def test_exact_manifest_with_axiom_free_theorem(self):
        result = verifier.audit_axioms(
            audit_line("Example.one") +
            "'Example.two' does not depend on any axioms\n",
            ["Example.two", "Example.one"])
        self.assertEqual(set(result["theorems"]), {"Example.one", "Example.two"})
        self.assertEqual(result["theorems"]["Example.two"], [])

    def test_missing_theorem_even_with_over_100_outputs(self):
        names = [f"Example.theorem_{index}" for index in range(102)]
        with self.assertRaisesRegex(ValueError, "missing=.*theorem_101"):
            verifier.audit_axioms("".join(map(audit_line, names[:-1])), names)

    def test_unexpected_theorem(self):
        with self.assertRaisesRegex(ValueError, "unexpected=.*Example.extra"):
            verifier.audit_axioms(audit_line("Example.one") + audit_line("Example.extra"),
                                  ["Example.one"])

    def test_duplicate_output(self):
        with self.assertRaisesRegex(ValueError, "Duplicate theorem entries"):
            verifier.audit_axioms(audit_line("Example.one") * 2, ["Example.one"])

    def test_duplicate_manifest(self):
        with self.assertRaisesRegex(ValueError, "Duplicate theorem names"):
            verifier.audit_axioms(audit_line("Example.one"), ["Example.one"] * 2)

    def test_unknown_transitive_axiom(self):
        with self.assertRaisesRegex(ValueError, "Unexpected transitive axioms"):
            verifier.audit_axioms(audit_line("Example.one", "propext, Example.assumption"),
                                  ["Example.one"])


class DependencySchedulingTests(unittest.TestCase):
    def test_independent_analytic_modules_compile_concurrently(self):
        modules = ["Sechstmoment.AnalyticLeft", "Sechstmoment.AnalyticRight"]
        barrier = threading.Barrier(2)
        recorded = []

        def compile_module(module):
            barrier.wait(timeout=5)
            return module, {"exit_code": 0}

        verifier.compile_modules(modules, {module: [] for module in modules},
                                 compile_module, lambda result: recorded.append(result[0]),
                                 workers=2)
        self.assertEqual(set(recorded), set(modules))

    def test_failed_dependency_never_enables_consumer(self):
        compiled, recorded = [], []

        def compile_module(module):
            compiled.append(module)
            raise RuntimeError("compiler rejected dependency")

        with self.assertRaisesRegex(RuntimeError, "compiler rejected"):
            verifier.compile_modules(["Base", "Consumer"],
                                     {"Base": [], "Consumer": ["Base"]},
                                     compile_module, recorded.append, workers=2)
        self.assertEqual(compiled, ["Base"])
        self.assertEqual(recorded, [])

    def test_nonpositive_workers_rejected(self):
        with self.assertRaisesRegex(ValueError, "workers must be positive"):
            verifier.compile_modules([], {}, lambda _: None, lambda _: None, workers=0)

    def test_new_module_waits_for_gram_and_certificate(self):
        base = "Sechstmoment.Base"
        grams = ["Sechstmoment.Certificate.GramBlocks.B000", "Sechstmoment.Certificate.GramBlocks.B001"]
        certificate = "Sechstmoment.Certificate.Exact.DenominatorBound"
        new_module = "Sechstmoment.NewIntegralBridge"
        order = [new_module, certificate, *grams, base]
        dependencies = {base: [], grams[0]: [base], grams[1]: [base],
                        certificate: grams, new_module: [certificate, grams[0]]}
        completed = set()
        recorded = []
        lock = threading.Lock()
        simultaneous_grams = threading.Barrier(2)

        def compile_module(module):
            with lock:
                self.assertTrue(set(dependencies[module]) <= completed,
                                f"Premature compilation of {module}")
            if module in grams:
                simultaneous_grams.wait(timeout=5)
            return module, {"exit_code": 0}

        def record(result):
            module, _ = result
            with lock:
                completed.add(module)
                recorded.append(module)

        verifier.compile_modules(order, dependencies, compile_module, record, workers=2)
        self.assertEqual(completed, set(order))
        self.assertEqual(recorded[0], base)
        self.assertEqual(recorded[-2:], [certificate, new_module])

    def test_cycle_is_reported(self):
        with self.assertRaisesRegex(ValueError, "cannot be satisfied"):
            verifier.compile_modules(["A", "B"], {"A": ["B"], "B": ["A"]},
                                     lambda _: self.fail("Cycle must not compile"),
                                     lambda _: None, workers=1)


if __name__ == "__main__":
    unittest.main()
