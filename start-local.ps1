$ErrorActionPreference = 'Stop'
$projectDirectory = $PSScriptRoot
Set-Location -LiteralPath $projectDirectory
if (-not (Test-Path -LiteralPath '.venv/Scripts/python.exe')) {
    throw 'Create .venv and install requirements.txt first. See README.md.'
}
node scripts/build.mjs
if ($LASTEXITCODE -ne 0) { throw 'The browser build failed.' }
New-Item -ItemType Directory -Force -Path '.data' | Out-Null
$pilotProcess = Start-Process -FilePath (Join-Path $projectDirectory '.venv/Scripts/python.exe') -ArgumentList '-m', 'server.app' -WorkingDirectory $projectDirectory -WindowStyle Hidden -PassThru -RedirectStandardOutput (Join-Path $projectDirectory '.data/server.log') -RedirectStandardError (Join-Path $projectDirectory '.data/server-errors.log')
$pilotProcess.Id | Set-Content -LiteralPath '.data/server.pid'
Write-Output 'Local pilot starting at http://127.0.0.1:8765/'
