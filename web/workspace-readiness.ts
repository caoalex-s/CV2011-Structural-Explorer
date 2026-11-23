/** Keep the static workspace visible while its handlers or a model import are pending. */
export function setWorkspaceBusy(busy: boolean, message = '') {
    const workspace = document.getElementById('workspace')!;
    const status = document.getElementById('workspace-operation')!;
    workspace.inert = busy;
    workspace.setAttribute('aria-busy', String(busy));
    document.querySelector<HTMLElement>('header.topbar')!.inert = busy;
    status.textContent = message;
    status.hidden = !message;
    const generate = document.querySelector<HTMLButtonElement>('#frame-generate');
    if (generate) generate.disabled = busy;
}
