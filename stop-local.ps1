$ErrorActionPreference = 'Stop'
$pidPath = Join-Path $PSScriptRoot '.data/server.pid'
if (-not (Test-Path -LiteralPath $pidPath)) { Write-Output 'No recorded local pilot process.'; exit }
$pilotPid = [int](Get-Content -LiteralPath $pidPath)
$pilotProcess = Get-CimInstance Win32_Process -Filter "ProcessId = $pilotPid"
$expectedExecutable = (Join-Path $PSScriptRoot '.venv/Scripts/python.exe').Replace('/', '\')
if ($pilotProcess -and $pilotProcess.ExecutablePath -eq $expectedExecutable -and $pilotProcess.CommandLine -match '-m\s+server\.app') {
    Stop-Process -Id $pilotPid
    Write-Output 'Stopped the local pilot.'
} elseif ($pilotProcess) {
    throw 'The recorded process is not this pilot. No process was stopped.'
} else {
    Write-Output 'The recorded local pilot is already stopped.'
}
