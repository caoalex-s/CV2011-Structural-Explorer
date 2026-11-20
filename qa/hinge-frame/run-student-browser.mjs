import { runMemberDeformationStudentCases } from '../member-kinematics/member-diagram-deformation-student-cases.mjs';
import { chromium } from '../../.data/student-tools/node_modules/playwright/index.mjs';
import { runMemberDiagramStudentCases } from '../member-diagram/student-canvas-cases.mjs';
import { runInclinedMemberDiagramStudentCases } from '../inclined-diagram/member-diagram-inclined-student-cases.mjs';
import { runJointMemberDiagramStudentCases } from '../member-diagram/member-diagram-joint-student-cases.mjs';
import { runSpringStudentCases } from '../frame-spring/student-canvas-cases.mjs';
import { runStudentCanvasCases } from './student-canvas-cases.mjs';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';

const [base, target] = process.argv.slice(2);
if (!base || !['published', 'stage2', 'stage3', 'springs', 'diagram', 'joint-diagram', 'inclined-diagram', 'member-kinematics'].includes(target)) throw Error('Expected site URL and review target.');
const browser = await chromium.launch({ headless: true });
try {
    const context = await browser.newContext({ viewport: { width: 1440, height: 1000 } });
    if (target === 'published') {
        const served = {};
        for (const path of ['', 'index.html', 'verification.json', 'portal-checker/bundle/manifest.json']) {
            const response = await context.request.get(new URL(path, base).href, { headers: { 'Cache-Control': 'no-cache' } });
            const body = await response.body();
            served[path || '/'] = { status: response.status(), url: response.url(), sha256: createHash('sha256').update(body).digest('hex'),
                ...(path === 'verification.json' && response.ok() ? { verification: JSON.parse(body) } : {}) };
        }
        await mkdir('.data/student-results', { recursive: true });
        await writeFile('.data/student-results/served.json', JSON.stringify(served, null, 2));
    }
    const page = await context.newPage();
    page.setDefaultTimeout(10000);
    const options = { page, base, target, output: '.data/student-results' };
    async function recreatePacket(sourceRequest, archived) {
        const { registerHooks } = await import('node:module');
        const hooks = registerHooks({ resolve(specifier, context, next) {
            if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
                return next(specifier.replace(/\.js$/, '.ts'), context);
            return next(specifier, context);
        } });
        try {
            const released = archived.startsWith('CV2011_INCLINED_RELEASE_1\n');
            const propose = released
                ? (await import('../../web/frame-inclined-release-packet.ts')).proposeInclinedReleasePacket
                : (await import('../../web/frame-interval-packet.ts')).proposeInclinedPacket;
            return propose(sourceRequest.model, sourceRequest.query, 96).packet;
        } finally { hooks.deregister(); }
    }
    const result = target === 'member-kinematics' ? await runMemberDeformationStudentCases({ ...options, recreatePacket }) : target === 'inclined-diagram' ? await runInclinedMemberDiagramStudentCases(options) : target === 'joint-diagram' ? await runJointMemberDiagramStudentCases(options) : target === 'diagram' ? await runMemberDiagramStudentCases(options) : target === 'springs' ? await runSpringStudentCases(options) : await runStudentCanvasCases(options);
    console.log(JSON.stringify(result, null, 2));
    if (result.errors.length || result.records.some(record => record.failure)) process.exitCode = 1;
} finally {
    await browser.close();
}
