$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath (Split-Path -Parent $PSScriptRoot)
$pythonPath = Join-Path (Get-Location) '.venv/Scripts/python.exe'

# Publish only reviewed application source and synthetic checks.
git add .github .gitignore .dockerignore Dockerfile README.md package.json tsconfig.json requirements.txt start-local.ps1 stop-local.ps1 proofs scripts server tests web
if ($LASTEXITCODE -ne 0) { throw 'Could not stage project source.' }
git diff --cached --check
if ($LASTEXITCODE -ne 0) { throw 'Source whitespace check failed.' }
git commit -m 'Build interactive structural explorer with verified beam practice'
if ($LASTEXITCODE -ne 0) { throw 'Could not commit project source.' }
& $pythonPath scripts/github_admin.py create
if ($LASTEXITCODE -ne 0) { throw 'Could not create the GitHub repository.' }
git remote add origin https://github.com/caoalex-s/CV2011-Structural-Explorer.git
git push -u origin main
if ($LASTEXITCODE -ne 0) { throw 'Could not push the repository.' }
& $pythonPath scripts/github_admin.py pages
