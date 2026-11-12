/** Decode named values from the exact packet returned by the compiled ABI.
 * Call only after that same byte array receives code 1. Parsing supplies no
 * mathematical acceptance; it preserves the checked identities for display.
 */
                                                      
import { frameLimits, frameQueryConvention } from './frame-candidate.js';
import { framePacketVersion } from './frame-packet.js';

                                    
                                                        
                                                  
                                              
 
                                     
                                                                
                                                                            
                                                                  
                                             
 

export function decodeAcceptedFramePacket(bytes            )                     {
    if (bytes.length > frameLimits.bytes) throw Error('Checker packet exceeds the display limit.');
    const text = new TextDecoder('utf-8', { fatal: true }).decode(bytes);
    if (!/^[\x20-\x7e\n]*$/.test(text)) throw Error('Invalid checker packet characters.');
    const fields = text.split('\n');
    if (fields.length > 6000) throw Error('Too many checker packet fields.');
    let position = 0;
    const token = ()         => {
        if (position >= fields.length) throw Error('Truncated checker packet.');
        return fields[position++];
    };
    const natural = (maximum        )         => {
        const value = token();
        if (!/^(0|[1-9]\d{0,2})$/.test(value) || Number(value) > maximum) throw Error('Invalid checker count or index.');
        return Number(value);
    };
    const rational = ()           => {
        const numerator = token(), denominator = token();
        if (!/^-?(0|[1-9]\d{0,127})$/.test(numerator) || numerator === '-0' ||
            !/^[1-9]\d{0,127}$/.test(denominator)) throw Error('Invalid checker rational.');
        return { numerator, denominator };
    };
    const identifier = ()         => {
        const hex = token();
        if (!/^(?:[0-9a-f]{4}){1,256}$/.test(hex)) throw Error('Invalid checker identifier.');
        let value = '';
        for (let i = 0; i < hex.length; i += 4) value += String.fromCharCode(Number.parseInt(hex.slice(i, i + 4), 16));
        return value;
    };
    const vector = (count        )             => Array.from({ length: count }, rational);
    if (token() !== framePacketVersion) throw Error('Unsupported checker packet version.');
    const nodeCount = natural(frameLimits.nodes), memberCount = natural(frameLimits.members);
    const supportCount = natural(frameLimits.supports), loadCount = natural(frameLimits.loads);
    if (!nodeCount || !memberCount) throw Error('Empty checker model.');

    // Read the accepted source identity tables. No candidate-side map labels
    // a checked value, and no rounded drawing coordinates enter this decoder.
    const nodeIds           = [], memberIds           = [];
    for (let i = 0; i < nodeCount; i++) {
        nodeIds.push(identifier()); rational(); rational(); natural(0); natural(memberCount); rational();
    }
    for (let i = 0; i < memberCount; i++) {
        memberIds.push(identifier()); natural(nodeCount - 1); natural(nodeCount - 1);
        rational(); rational(); natural(1);
    }
    for (let i = 0; i < supportCount; i++) {
        identifier(); natural(memberCount - 1); rational(); natural(2); rational();
    }
    for (let i = 0; i < loadCount; i++) {
        identifier(); natural(memberCount - 1); natural(2);
        for (let field = 0; field < 6; field++) rational();
    }
    const member = memberIds[natural(memberCount - 1)], parameter = rational();
    const cutSide = natural(1) ? 'right' : 'left';
    if (natural(1) !== 1) throw Error('Unknown query convention.');
    const mechanism = natural(1) === 1;
    const motionCount = natural(frameLimits.coordinates), freeCount = natural(frameLimits.coordinates);
    const pointCount = natural(frameLimits.points);
    if (motionCount !== 3 * pointCount || (mechanism && freeCount !== 0)) throw Error('Invalid checked dimensions.');
    const points                      = [];
    for (let i = 0; i < pointCount; i++) {
        const owned = natural(1) === 1;
        const index = natural((owned ? memberCount : nodeCount) - 1);
        points.push({ owner: owned ? 'member' : 'node', id: (owned ? memberIds : nodeIds)[index], index,
            parameter: rational(), x: rational(), y: rational(), motion: [] });
    }
    const motion = vector(motionCount);
    let reactions             = [], readouts             = [];
    if (!mechanism) {
        reactions = vector(motionCount);
        // The positive-factor witness is retained in the packet export. The
        // display consumes its values without allocating a second matrix.
        for (let i = 0; i < freeCount * freeCount + freeCount; i++) rational();
        readouts = vector(6);
    }
    const loadWork = rational();
    if (position !== fields.length) throw Error('Unexpected trailing checker fields.');
    points.forEach((point, i) => {
        point.motion = motion.slice(3 * i, 3 * i + 3);
        if (!mechanism) point.reaction = reactions.slice(3 * i, 3 * i + 3);
    });
    return { kind: mechanism ? 'mechanism' : 'solution', points, readouts, loadWork,
        query: { member, parameter, cutSide, ...frameQueryConvention } };
}
