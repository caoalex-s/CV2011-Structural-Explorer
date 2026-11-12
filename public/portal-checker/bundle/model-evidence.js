/** Local evidence envelopes bind a frozen drawing and query; they do not verify it. */
                                                                     

                                           
                                
                   
                      
                                              
                     
                  
                           
 

function object(value         , name        , keys          )              {
    if (value === null || typeof value !== 'object' || Array.isArray(value)) throw Error(`${name} must be an object`);
    const result = value               ;
    for (const key of Object.keys(result)) if (!keys.includes(key)) throw Error(`${name}: unknown field ${key}`);
    return result;
}
function text(value         , name        )         {
    if (typeof value !== 'string' || value.trim() === '') throw Error(`${name} must be a nonempty string`);
    return value;
}
function number(value         , name        )         {
    if (typeof value !== 'number' || !Number.isFinite(value)) throw Error(`${name} must be finite`);
    return value === 0 ? 0 : value;
}
function positive(value         , name        )         {
    const result = number(value, name);
    if (result <= 0) throw Error(`${name} must be positive`);
    return result;
}
function parameter(value         , name        )         {
    const result = number(value, name);
    if (result < 0 || result > 1) throw Error(`${name} must lie between 0 and 1`);
    return result;
}
function choice                  (value         , name        , options              )    {
    if (typeof value !== 'string' || !options.includes(value     )) throw Error(`${name} is invalid`);
    return value     ;
}
function flag(value         , name        )          {
    if (value === undefined) return false;
    if (typeof value !== 'boolean') throw Error(`${name} must be boolean`);
    return value;
}
function array(value         , name        )            {
    if (!Array.isArray(value)) throw Error(`${name} must be an array`);
    return value;
}
function connection(value         , name        )                         {
    if (value === undefined) return undefined;
    const item = object(value, name, ['axial', 'transverse', 'rotation']);
    const rule = (v         , field        )                 =>
        v === 'rigid' || v === 'free' ? v : positive(v, `${name}.${field}`);
    return { axial: rule(item.axial, 'axial'), transverse: rule(item.transverse, 'transverse'), rotation: rule(item.rotation, 'rotation') };
}
function unique(ids          , name        )       {
    if (new Set(ids).size !== ids.length) throw Error(`${name} IDs must be unique`);
}

/** Strictly parse the existing local Model or its version-2 export, without solving it. */
export function parseEvidenceModel(input         )        {
    const root = object(input, 'input', ['version', 'model', 'nodes', 'members', 'supports', 'loads']);
    let raw             ;
    if ('version' in root || 'model' in root) {
        if (root.version !== 2 || !('model' in root) || Object.keys(root).some(key => key !== 'version' && key !== 'model')) throw Error('Expected a version-2 model export');
        raw = object(root.model, 'model', ['nodes', 'members', 'supports', 'loads']);
    } else raw = root;
    const nodes = array(raw.nodes, 'nodes').map((value, index) => {
        const name = `nodes[${index}]`, item = object(value, name, ['id', 'x', 'y', 'joint', 'rotationStiffness', 'referenceMember']);
        const joint = item.joint === undefined ? 'rigid' : choice(item.joint, `${name}.joint`, ['rigid', 'pinned', 'semi-rigid', 'custom']         );
        const rotationStiffness = item.rotationStiffness === undefined ? (joint === 'semi-rigid' ? 20000 : undefined) : positive(item.rotationStiffness, `${name}.rotationStiffness`);
        const referenceMember = item.referenceMember === undefined ? undefined : text(item.referenceMember, `${name}.referenceMember`);
        return { id: text(item.id, `${name}.id`), x: number(item.x, `${name}.x`), y: number(item.y, `${name}.y`), joint, ...(rotationStiffness === undefined ? {} : { rotationStiffness }), ...(referenceMember === undefined ? {} : { referenceMember }) };
    });
    unique(nodes.map(node => node.id), 'Node');
    const members = array(raw.members, 'members').map((value, index) => {
        const name = `members[${index}]`, item = object(value, name, ['id', 'a', 'b', 'EA', 'EI', 'connectionA', 'connectionB']);
        const a = text(item.a, `${name}.a`), b = text(item.b, `${name}.b`);
        const start = nodes.find(node => node.id === a), end = nodes.find(node => node.id === b);
        if (!start || !end || a === b || (start.x === end.x && start.y === end.y)) throw Error(`${name} must connect distinct existing points`);
        const connectionA = connection(item.connectionA, `${name}.connectionA`), connectionB = connection(item.connectionB, `${name}.connectionB`);
        return { id: text(item.id, `${name}.id`), a, b, EA: positive(item.EA, `${name}.EA`), EI: positive(item.EI, `${name}.EI`), ...(connectionA ? { connectionA } : {}), ...(connectionB ? { connectionB } : {}) };
    });
    unique(members.map(member => member.id), 'Member');
    for (const node of nodes) if (node.referenceMember !== undefined && !members.some(member => member.id === node.referenceMember && (member.a === node.id || member.b === node.id))) throw Error(`Invalid reference member at node ${node.id}`);
    const memberReference = (value         , name        ) => {
        const id = text(value, name);
        if (!members.some(member => member.id === id)) throw Error(`${name} refers to a missing member`);
        return id;
    };
    const supports = array(raw.supports, 'supports').map((value, index) => {
        const name = `supports[${index}]`, item = object(value, name, ['id', 'member', 't', 'kind', 'angle', 'fixX', 'fixY', 'fixRotation']);
        return { id: text(item.id, `${name}.id`), member: memberReference(item.member, `${name}.member`), t: parameter(item.t, `${name}.t`), kind: choice(item.kind, `${name}.kind`, ['pin', 'roller', 'fixed', 'guided', 'custom']         ), angle: number(item.angle, `${name}.angle`), fixX: flag(item.fixX, `${name}.fixX`), fixY: flag(item.fixY, `${name}.fixY`), fixRotation: flag(item.fixRotation, `${name}.fixRotation`) };
    });
    unique(supports.map(item => item.id), 'Support');
    const loads = array(raw.loads, 'loads').map((value, index) => {
        const name = `loads[${index}]`, item = object(value, name, ['id', 'label', 'member', 'kind', 't', 'end', 'fx', 'fy', 'mz', 'qEnd']);
        const kind = choice(item.kind, `${name}.kind`, ['force', 'moment', 'distributed']         ), t = parameter(item.t, `${name}.t`), end = parameter(item.end, `${name}.end`);
        if (kind === 'distributed' && end <= t) throw Error(`${name} must have a positive interval`);
        const label = item.label === undefined ? undefined : text(item.label, `${name}.label`);
        return { id: text(item.id, `${name}.id`), ...(label === undefined ? {} : { label }), member: memberReference(item.member, `${name}.member`), kind, t, end, fx: number(item.fx, `${name}.fx`), fy: number(item.fy, `${name}.fy`), mz: number(item.mz, `${name}.mz`), qEnd: number(item.qEnd, `${name}.qEnd`) };
    });
    unique(loads.map(item => item.id), 'Load');
    return { nodes, members, supports, loads };
}

/** Deterministic JSON: object keys sort, while every array retains its order. */
function canonical(value         )         {
    if (value === null || typeof value === 'string' || typeof value === 'boolean') return JSON.stringify(value);
    if (typeof value === 'number') return JSON.stringify(number(value, 'canonical number'));
    if (Array.isArray(value)) return `[${value.map(canonical).join(',')}]`;
    if (typeof value === 'object') return `{${Object.entries(value               ).sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0).map(([key, child]) => `${JSON.stringify(key)}:${canonical(child)}`).join(',')}}`;
    throw Error('Unsupported canonical value');
}
function freeze   (value   )    {
    if (value && typeof value === 'object') {
        for (const child of Object.values(value)) freeze(child);
        Object.freeze(value);
    }
    return value;
}
async function digest(value        )                  {
    const bytes = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(value));
    return Array.from(new Uint8Array(bytes), byte => byte.toString(16).padStart(2, '0')).join('');
}
function validateQuery(query               , model       )                {
    const item = object(query, 'query', ['member', 'parameter', 'cutSide', 'quantity', 'units', 'signConvention']);
    const member = text(item.member, 'query.member');
    if (!model.members.some(candidate => candidate.id === member)) throw Error('Query member is missing');
    return { member, parameter: parameter(item.parameter, 'query.parameter'), cutSide: choice(item.cutSide, 'query.cutSide', ['left', 'right', 'unspecified']         ), quantity: text(item.quantity, 'query.quantity'), units: text(item.units, 'query.units'), signConvention: text(item.signConvention, 'query.signConvention') };
}
function partition(model       ) {
    const display = { loads: model.loads.map(load => ({ id: load.id, label: load.label ?? null })) };
    const mechanics = { ...model, loads: model.loads.map(({ label: _label, ...load }) => load) };
    return { mechanics, display };
}

/** Capture only local data. Binary64 JSON numbers denote their exact parsed binary values. */
export async function createEvidenceEnvelope(input         , query               , rawSource         ) {
    const model = parseEvidenceModel(input);
    const checkedQuery = validateQuery(query, model);
    if (rawSource !== undefined && canonical(parseEvidenceModel(JSON.parse(rawSource))) !== canonical(model)) throw Error('Raw source does not match the snapshot');
    const { mechanics, display } = partition(model);
    const [mechanical, presentation, queryHash, raw] = await Promise.all([
        digest(canonical(mechanics)), digest(canonical(display)), digest(canonical(checkedQuery)),
        rawSource === undefined ? Promise.resolve(null) : digest(rawSource),
    ]);
    return freeze({ schema: 'cv2011-local-evidence', version: 1, numericSemantics: 'parsed-finite-binary64-as-exact-binary-rational; signed-zero-normalized', status: 'pending-not-formally-verified', model, query: checkedQuery,
        bindings: { rawSource: raw, mechanical, display: presentation, query: queryHash, exactAdapter: null, theoremBundle: null, checker: null, result: null } });
}

/** Revision tokens reject superseded or edited requests, including edit-then-revert. */
export class EvidenceRequests {
            revision = 0;
            request = 0;
            signature = '';
    /** Ignore presentation-only edits, but retain the history of mechanical/query edits. */
    update(input         , query               )       {
        const model = parseEvidenceModel(input);
        const signature = canonical({ mechanics: partition(model).mechanics, query: validateQuery(query, model) });
        if (this.signature !== signature) { this.signature = signature; this.revision++; }
    }
    invalidate()       { this.revision++; }
    begin()                                        { return { revision: this.revision, request: ++this.request }; }
    isCurrent(token                                       )          { return token.revision === this.revision && token.request === this.request; }
    accept   (token                                       , result   )    {
        if (!this.isCurrent(token)) throw Error('Stale evidence result');
        return result;
    }
}
