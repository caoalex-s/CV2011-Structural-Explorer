"""Local or hosted verification API with pseudonymous, token-authenticated records.

Run `python -m server.app` from the project root after building dist/. SQLite
data and account tokens are written only under .data/ (excluded from Git).
Hosted mode requires explicit origins, an instructor token, and issued accounts.
"""
import argparse
import hashlib
import hmac
import json
import os
from pathlib import Path
import secrets
import sqlite3
from contextlib import contextmanager
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlsplit

from server.verifier import VERSION, check, solution
from server.worked import worked_solution
from server.concepts import check_concept

ROOT = Path(__file__).resolve().parents[1]
DATA = Path(os.environ.get("EXPLORER_DATA", ROOT / ".data"))


def digest(token):
    return hashlib.sha256(token.encode()).hexdigest()


class Store:
    def __init__(self, directory=DATA):
        self.directory = Path(directory)
        self.directory.mkdir(parents=True, exist_ok=True)
        self.database = self.directory / "attempts.sqlite3"
        with self.connect() as connection:
            connection.execute("CREATE TABLE IF NOT EXISTS accounts (course_id TEXT PRIMARY KEY, token_hash TEXT UNIQUE NOT NULL)")
            connection.execute("CREATE TABLE IF NOT EXISTS attempts (id TEXT PRIMARY KEY, course_id TEXT NOT NULL, created TEXT NOT NULL, payload TEXT NOT NULL)")

    @contextmanager
    def connect(self):
        connection = sqlite3.connect(self.database)
        try:
            with connection:
                yield connection
        finally:
            connection.close()

    def issue(self, course_id):
        if not course_id or len(course_id) > 40 or not all(c.isalnum() or c in "-_" for c in course_id):
            raise ValueError("Use a pseudonymous ID of at most 40 letters, digits, hyphens, or underscores.")
        token = secrets.token_urlsafe(32)
        with self.connect() as connection:
            connection.execute("INSERT INTO accounts VALUES (?,?)", (course_id, digest(token)))
        return token

    def identity(self, token):
        with self.connect() as connection:
            row = connection.execute("SELECT course_id FROM accounts WHERE token_hash=?", (digest(token),)).fetchone()
        return row[0] if row else None

    def record(self, course_id, payload, result):
        from datetime import datetime, timezone
        if not isinstance(payload.get("id"), str) or len(payload["id"]) > 80:
            raise ValueError("A bounded event ID is required.")
        # The authenticated identity and server result override client claims.
        event = {key: payload.get(key) for key in ["id", "event", "model", "step", "answer", "units", "side", "hintUsed", "solutionRevealed", "section"]}
        event.update(courseId=course_id, timestamp=datetime.now(timezone.utc).isoformat(), result=result)
        with self.connect() as connection:
            previous = connection.execute("SELECT course_id,payload FROM attempts WHERE id=?", (event["id"],)).fetchone()
            if previous:
                if previous[0] != course_id:
                    raise ValueError("Event identifier already used.")
                return json.loads(previous[1])
            connection.execute("INSERT INTO attempts VALUES (?,?,?,?)", (event["id"], course_id, event["timestamp"], json.dumps(event)))
        return event

    def records(self, course_id=None):
        with self.connect() as connection:
            if course_id:
                rows = connection.execute("SELECT payload FROM attempts WHERE course_id=? ORDER BY created LIMIT 10000", (course_id,)).fetchall()
            else:
                rows = connection.execute("SELECT payload FROM attempts ORDER BY created LIMIT 10000").fetchall()
        return [json.loads(row[0]) for row in rows]


def make_handler(store, instructor_token, origins, local_demo=None):
    class Handler(SimpleHTTPRequestHandler):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, directory=str(ROOT / "dist"), **kwargs)

        def log_message(self, format, *args):
            # Never log Authorization or submitted expressions.
            print(f"{self.command} {urlsplit(self.path).path}", flush=True)

        def origin_allowed(self):
            origin = self.headers.get("Origin")
            return not origin or origin in origins

        def end_headers(self):
            origin = self.headers.get("Origin")
            if origin in origins:
                self.send_header("Access-Control-Allow-Origin", origin)
                self.send_header("Vary", "Origin")
            self.send_header("X-Content-Type-Options", "nosniff")
            super().end_headers()

        def respond(self, data, status=200):
            encoded = json.dumps(data).encode()
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(encoded)))
            self.end_headers()
            self.wfile.write(encoded)

        def token(self):
            header = self.headers.get("Authorization", "")
            return header.removeprefix("Bearer ") if header.startswith("Bearer ") else ""

        def do_OPTIONS(self):
            if not self.origin_allowed():
                self.respond({"error": "Origin is not allowed."}, 403)
                return
            self.send_response(204)
            self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
            self.send_header("Access-Control-Allow-Headers", "Authorization, Content-Type")
            self.end_headers()

        def do_GET(self):
            path = urlsplit(self.path).path
            if not self.origin_allowed():
                self.respond({"error": "Origin is not allowed."}, 403)
                return
            if path == "/api/health":
                self.respond({"sympy": True, "verifier": VERSION, "localDemo": local_demo})
            elif path == "/api/me":
                identity = store.identity(self.token())
                self.respond({"courseId": identity} if identity else {"error": "Valid personal token required."}, 200 if identity else 401)
            elif path == "/api/instructor/attempts":
                if self.token() and hmac.compare_digest(self.token(), instructor_token):
                    self.respond({"attempts": store.records()})
                else:
                    self.respond({"error": "Instructor authentication required."}, 403)
            elif path == "/api/attempts":
                identity = store.identity(self.token())
                self.respond({"attempts": store.records(identity)} if identity else {"error": "Personal authentication required."}, 200 if identity else 401)
            elif path.startswith("/api/"):
                self.respond({"error": "Unknown endpoint."}, 404)
            else:
                # SimpleHTTPRequestHandler constrains serving to dist/, which
                # contains no database, account file, server, or credentials.
                super().do_GET()

        def do_POST(self):
            if not self.origin_allowed():
                self.respond({"error": "Origin is not allowed."}, 403)
                return
            identity = store.identity(self.token())
            if not identity:
                self.respond({"error": "Valid personal token required."}, 401)
                return
            try:
                length = int(self.headers.get("Content-Length", "0"))
                if not 0 < length <= 100000:
                    raise ValueError("Request size must be between 1 and 100000 bytes.")
                if not self.headers.get("Content-Type", "").startswith("application/json"):
                    raise ValueError("Use application/json.")
                payload = json.loads(self.rfile.read(length))
                if not isinstance(payload, dict):
                    raise ValueError("Expected a JSON object.")
                path = urlsplit(self.path).path
                if path == "/api/solution":
                    self.respond(solution(payload))
                elif path == "/api/worked-solution":
                    self.respond(worked_solution(payload))
                elif path == "/api/attempts":
                    if payload.get("courseId") != identity:
                        raise ValueError("Course ID does not correspond to the authenticated account.")
                    if payload.get("event") == "submit":
                        result = check_concept(payload) if str(payload.get("step", "")).startswith("concept_") else check(payload)
                    elif payload.get("event") in ("hint", "reveal"):
                        result = {"status": "not_graded", "category": payload["event"], "message": "Learning event recorded.", "verifier": VERSION}
                    else:
                        raise ValueError("Unknown learning event.")
                    event = store.record(identity, payload, result)
                    self.respond({"result": event["result"], "id": event["id"]})
                else:
                    self.respond({"error": "Unknown endpoint."}, 404)
            except (ValueError, KeyError, TypeError, json.JSONDecodeError) as error:
                self.respond({"error": str(error)}, 400)

    return Handler


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=int(os.environ.get("PORT", 8765)))
    parser.add_argument("--issue", help="Issue a new pseudonymous account; prints its personal token once.")
    args = parser.parse_args()
    store = Store()
    if args.issue:
        print(json.dumps({"courseId": args.issue, "token": store.issue(args.issue)}))
        return
    origins = {value.strip() for value in os.environ.get("EXPLORER_ORIGINS", "").split(",") if value.strip()}
    instructor_token = os.environ.get("EXPLORER_INSTRUCTOR_TOKEN", "")
    local_demo = None
    if args.host in ("127.0.0.1", "localhost"):
        origins.update({f"http://127.0.0.1:{args.port}", f"http://localhost:{args.port}"})
        credentials = store.directory / "local-credentials.json"
        if credentials.exists():
            local_demo = json.loads(credentials.read_text())
        else:
            local_demo = {"courseId": "DEMO-001", "token": store.issue("DEMO-001"), "instructor": secrets.token_urlsafe(32)}
            credentials.write_text(json.dumps(local_demo))
        instructor_token = local_demo["instructor"]
    elif not instructor_token or not origins:
        raise SystemExit("Hosted mode requires EXPLORER_INSTRUCTOR_TOKEN and EXPLORER_ORIGINS.")
    server = ThreadingHTTPServer((args.host, args.port), make_handler(store, instructor_token, origins, local_demo))
    print(f"Structural Explorer: http://{args.host}:{args.port}", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
