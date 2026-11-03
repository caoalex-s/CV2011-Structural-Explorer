"""Check public synthetic examples in Linux CI and publish exact-source receipts.

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
    for example in json.loads(result.stdout):
        for section in (0.25, 0.5, 0.75):
            response = worked_solution({"model": example["model"], "section": section})
            proof = response["proof"]
            if proof["status"] != "checked":
                raise RuntimeError(f"{example['name']} at {section}: {proof.get('audit', proof['message'])}")
            receipts["certificates"][proof["sha256"]] = {
                "status": "checked", "statements": proof["statements"],
                "example": example["name"], "section": section,
            }
            print(f"Checked {example['name']} at {section}: {proof['statements']} statements")
    Path("web/worked-receipts.json").write_text(json.dumps(receipts, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
