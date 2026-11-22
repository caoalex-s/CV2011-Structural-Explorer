const exercise=new URLSearchParams(location.search).get('exercise');
if(exercise==='ideal-planar-truss') await import('./truss-workspace.js');
else await import('./app.js');
export {};
