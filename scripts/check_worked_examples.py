"""Check public synthetic examples and publish their derivations and receipts.

No student model or attempt record enters this workflow. A local pilot may copy
the published receipt file to proofs/worked-receipts.json. Modified examples
receive no formal badge unless their complete certificate also has a receipt
or an explicitly configured local compiler checks it.
"""
import json
from pathlib import Path
import subprocess

from server.worked import worked_solution


def main():
    # The examples come directly from the browser's maintained model factory.
    result = subprocess.run(
        ["node", "--input-type=module", "-e",
         "import {example} from './web/engine.ts'; console.log(JSON.stringify(['beam','udl','overhang'].map(name=>({name,model:example(name)}))));"],
        capture_output=True, text=True, check=True,
    )
    receipts = {"toolchain": "leanprover/lean4:v4.19.0", "certificates": {}}
    library = {"schemaVersion": 1, "examples": []}
    names = {"beam": "Simply supported beam", "udl": "Distributed load", "overhang": "Overhanging beam"}
    for example in json.loads(result.stdout):
        published = {"name": names[example["name"]], "model": example["model"], "solutions": []}
        for section in (0.25, 0.5, 0.75):
            response = worked_solution({"model": example["model"], "section": section})
            proof = response["proof"]
            if proof["status"] != "checked":
                raise RuntimeError(f"{example['name']} at {section}: {proof.get('audit', proof['message'])}")
            receipts["certificates"][proof["sha256"]] = {
                "status": "checked", "statements": proof["statements"],
                "example": example["name"], "section": section,
            }
            # Publish only the maintained synthetic examples, never student
            # snapshots or records. Keep the source and VS Code proof download.
            proof.pop("audit", None)
            proof["message"] = f"Lean checked {proof['statements']} exact statements for this published model and section in GitHub CI."
            published["solutions"].append({"section": section, "response": response})
            print(f"Checked {example['name']} at {section}: {proof['statements']} statements")
        library["examples"].append(published)
    Path("web/worked-receipts.json").write_text(json.dumps(receipts, indent=2) + "\n", encoding="utf-8")
    Path("web/worked-examples.json").write_text(json.dumps(library, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
