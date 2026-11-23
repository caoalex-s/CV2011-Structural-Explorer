import { setWorkspaceBusy } from './workspace-readiness.js';

// The hash selects the current workspace mode. Skip navigation moves focus only.
document.querySelector<HTMLAnchorElement>('.skip-workspace')!.onclick = event => {
    event.preventDefault();
    document.getElementById('workspace')!.focus();
};
const exercise = new URLSearchParams(location.search).get('exercise');
try {
    if (exercise === 'simple-beams') {
        await import('./simple-beams.js');
        setWorkspaceBusy(false);
    } else if (exercise === 'week04-truss-sections') {
        await import('./week04-workspace.js');
        setWorkspaceBusy(false);
    } else if (exercise === 'ideal-planar-truss') {
        await import('./truss-workspace.js');
        setWorkspaceBusy(false);
    } else {
        // The frame editor also consumes any file selected before its module loaded.
        await import('./app.js');
    }
} catch (error) {
    setWorkspaceBusy(true, 'The workspace could not open. Reload the page to try again.');
    throw error;
}
