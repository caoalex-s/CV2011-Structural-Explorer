"""Concept grades must come from the server key, not the client's claimed grade."""
import tempfile
import unittest
from server.app import Store
from server.concepts import QUESTIONS, check_concept


class ConceptChecks(unittest.TestCase):
    def test_every_choice_has_an_explicit_outcome(self):
        for question in QUESTIONS.values():
            for choice in question["choices"]:
                payload = {"step": question["id"], "answer": choice["id"], "units": "choice"}
                result = check_concept(payload)
                self.assertEqual(result["status"], "correct" if choice["id"] == question["correct"] else "incorrect")
                self.assertEqual(result["category"], choice["category"])
                self.assertEqual(result["verifier"], "course-concept-key-v1")

    def test_rejects_unknown_questions_choices_and_units(self):
        valid = {"step": "concept_parallel_restraints_v1", "answer": "horizontal", "units": "choice"}
        for changes in ({"step": "concept_unknown"}, {"answer": "invented"}, {"units": "kN"}):
            with self.assertRaises(ValueError):
                check_concept(valid | changes)

    def test_authenticated_record_overrides_client_grade_and_identity(self):
        payload = {"id": "concept-event", "event": "submit", "courseId": "FAKE", "step": "concept_parallel_restraints_v1", "answer": "count", "units": "choice", "result": {"status": "correct"}}
        with tempfile.TemporaryDirectory() as folder:
            store = Store(folder)
            event = store.record("COURSE-001", payload, check_concept(payload))
            self.assertEqual(event["courseId"], "COURSE-001")
            self.assertEqual(event["result"]["status"], "incorrect")
            self.assertEqual(event["result"]["category"], "reaction_count_without_geometry")
            self.assertEqual(len(store.records("COURSE-001")), 1)
