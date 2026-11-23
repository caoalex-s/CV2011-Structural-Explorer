/** Both truss exercises share the same course links and learning-record controls. */
export function showTrussNavigation(exercise: 'ideal-planar-truss' | 'week04-truss-sections') {
    const nav = document.querySelector<HTMLElement>('.topbar nav')!;
    const brand = document.querySelector<HTMLAnchorElement>('.topbar .brand')!;
    brand.href = './#sandbox';
    nav.innerHTML = '<a href="learn/">Learn</a><a href="./">Frame workspace</a>'
        + '<a href="?exercise=ideal-planar-truss">Ideal planar truss</a>'
        + '<a href="?exercise=week04-truss-sections">Method of sections</a>';
    nav.querySelector('a[href="?exercise=' + exercise + '"]')!.setAttribute('aria-current', 'page');
    document.querySelector('.header-actions')!.innerHTML =
        '<button id="replay">Local replay</button><button id="settings-button">Session</button><button id="instructor">Learning insights</button>';
}
