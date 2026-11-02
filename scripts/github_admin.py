"""Operate the project repository using the existing Git credential manager.

Credentials remain in process memory and are never printed or written to disk.
The inspect command is read-only. Publish commands are invoked explicitly.
"""
import json
import os
import subprocess
import sys
import urllib.error
import urllib.request

REPOSITORY = "caoalex-s/CV2011-Structural-Explorer"


def api(path, method="GET", payload=None, raw=False):
    credential = subprocess.run(
        ["git", "credential", "fill"], input="protocol=https\nhost=github.com\n\n",
        capture_output=True, text=True, check=True,
        env={**os.environ, "GIT_TERMINAL_PROMPT": "0", "GCM_INTERACTIVE": "never"},
    )
    fields = dict(line.split("=", 1) for line in credential.stdout.splitlines() if "=" in line)
    request = urllib.request.Request(
        "https://api.github.com/" + path,
        data=json.dumps(payload).encode() if payload is not None else None,
        method=method,
        headers={"Authorization": "Bearer " + fields["password"],
                 "Accept": "application/vnd.github+json", "User-Agent": "CV2011-Explorer",
                 "X-GitHub-Api-Version": "2022-11-28"},
    )
    try:
        class SafeRedirect(urllib.request.HTTPRedirectHandler):
            def redirect_request(self, request, fp, code, message, headers, newurl):
                redirected = super().redirect_request(request, fp, code, message, headers, newurl)
                if redirected is not None:
                    redirected.remove_header("Authorization")
                return redirected

        with urllib.request.build_opener(SafeRedirect()).open(request, timeout=30) as response:
            body = response.read()
            if raw:
                return body.decode()
            return json.loads(body) if body else {}
    except urllib.error.HTTPError as error:
        return {"http_status": error.code, "detail": error.read().decode()[:1000]}


if __name__ == "__main__":
    operation = sys.argv[1]
    if operation == "inspect":
        user = api("user")
        repo = api("repos/" + REPOSITORY)
        print(json.dumps({"login": user.get("login"), "repository_exists": "id" in repo,
                          "repository_status": repo.get("http_status"),
                          "permissions": repo.get("permissions")}))
    elif operation == "create":
        created = api("user/repos", "POST", {
            "name": REPOSITORY.split("/")[1], "private": False,
            "description": "Interactive structural analysis and verified learning activities for CV2011.",
            "auto_init": False,
        })
        print(json.dumps({key: created.get(key) for key in ["html_url", "full_name", "private", "http_status", "detail"]}))
        if "id" not in created:
            sys.exit(1)
    elif operation == "pages":
        print(json.dumps(api("repos/" + REPOSITORY + "/pages", "POST", {"build_type": "workflow"})))
    elif operation == "runs":
        runs = api("repos/" + REPOSITORY + "/actions/runs?per_page=4")
        print(json.dumps([{key: run.get(key) for key in ["id", "name", "status", "conclusion", "html_url"]}
                          for run in runs.get("workflow_runs", [])]))
    elif operation == "jobs":
        print(json.dumps(api("repos/" + REPOSITORY + "/actions/runs/" + sys.argv[2] + "/jobs")))
    elif operation == "logs":
        result = api("repos/" + REPOSITORY + "/actions/jobs/" + sys.argv[2] + "/logs", raw=True)
        print("\n".join(result.splitlines()[-100:]) if isinstance(result, str) else json.dumps(result))
