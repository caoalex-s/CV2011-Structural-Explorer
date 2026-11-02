$ErrorActionPreference = 'Stop'
$projectDirectory = $PSScriptRoot
Set-Location -LiteralPath $projectDirectory
if (-not (Test-Path -LiteralPath '.venv/Scripts/python.exe')) {
    throw 'Create .venv and install requirements.txt first. See README.md.'
}
node scripts/build.mjs
if ($LASTEXITCODE -ne 0) { throw 'The browser build failed.' }
New-Item -ItemType Directory -Force -Path '.data' | Out-Null
try {
    $existingService = Invoke-RestMethod -Uri 'http://127.0.0.1:8765/api/health' -TimeoutSec 2
    if ($existingService.verifier -eq 'beam-exact-1') {
        Write-Output 'The local pilot is already running at http://127.0.0.1:8765/'
        exit
    }
} catch {
    # Start the service when no existing pilot responds on this port.
}
$pilotProcess = Start-Process -FilePath (Join-Path $projectDirectory '.venv/Scripts/python.exe') -ArgumentList '-m', 'server.app' -WorkingDirectory $projectDirectory -WindowStyle Hidden -PassThru -RedirectStandardOutput (Join-Path $projectDirectory '.data/server.log') -RedirectStandardError (Join-Path $projectDirectory '.data/server-errors.log')
$pilotProcess.Id | Set-Content -LiteralPath '.data/server.pid'
for ($attemptNumber = 0; $attemptNumber -lt 20; $attemptNumber++) {
    try {
        $ready = Invoke-RestMethod -Uri 'http://127.0.0.1:8765/api/health' -TimeoutSec 1
        if ($ready.sympy) {
            Write-Output 'Local pilot ready at http://127.0.0.1:8765/'
            exit
        }
    } catch {
        Start-Sleep -Milliseconds 150
    }
}
throw 'The local pilot did not start. Inspect .data/server-errors.log.'
