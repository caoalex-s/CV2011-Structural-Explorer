"""Grade versioned concept choices from the same source used by the lesson.

The authenticated API records these as concept checks, not symbolic or Lean
verification. Choice categories describe observed answers, not a diagnosis.
"""
import json
from pathlib import Path

QUESTION_FILE = Path(__file__).resolve().parents[1] / "src/data/questions.json"
QUESTIONS = {item["id"]: item for item in json.loads(QUESTION_FILE.read_text(encoding="utf-8"))}


def check_concept(payload):
    question = QUESTIONS.get(payload.get("step"))
    if question is None:
        raise ValueError("Unknown concept question.")
    if payload.get("units") != "choice":
        raise ValueError("A concept answer must use choice units.")
    choice = next((item for item in question["choices"] if item["id"] == payload.get("answer")), None)
    if choice is None:
        raise ValueError("Unknown answer choice.")
    return {
        "status": "correct" if choice["id"] == question["correct"] else "incorrect",
        "category": choice["category"],
        "message": question["explanation"],
        "verifier": "course-concept-key-v1",
    }
