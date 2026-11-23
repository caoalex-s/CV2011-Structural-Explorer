import { setWorkspaceBusy } from './workspace-readiness.js';

const exercise = new URLSearchParams(location.search).get('exercise');
try {
    if (exercise === 'ideal-planar-truss') {
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
