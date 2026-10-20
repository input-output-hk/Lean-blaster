// Execute the workflow's actual inline reporter against a GitHub API double.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const text = fs.readFileSync(path.join(__dirname, '../../.github/workflows/ci-nightly-build.yaml'), 'utf8');
const source = text.split('          script: |\n')[1].split('\n').map(line => line.slice(12)).join('\n');
const AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
const report = new AsyncFunction('github', 'context', source);
const marker = '<!-- blaster-nightly-lean -->';

async function run(result, issues) {
  process.env.BUILD_RESULT = result;
  const writes = [];
  const github = {
    paginate: async () => issues,
    rest: {issues: {
      listForRepo: () => {},
      create: async args => writes.push(['create', args]),
      createComment: async args => writes.push(['comment', args]),
      update: async args => writes.push(['update', args]),
    }},
  };
  await report(github, {serverUrl: 'https://github.com', repo: {owner: 'owner', repo: 'repo'}, runId: 123});
  return writes;
}

(async () => {
  const tracked = {number: 1, user: {type: 'Bot'}, body: marker};
  const human = {number: 2, user: {type: 'User'}, body: marker};
  const unrelated = {number: 3, user: {type: 'Bot'}, body: 'unrelated'};
  const pr = {...tracked, number: 4, pull_request: {url: 'pr'}};
  const failure = await run('failure', []);
  assert.equal(failure.length, 1);
  assert.equal(failure[0][0], 'create');
  assert.match(failure[0][1].body, /actions\/runs\/123/);
  assert.deepEqual(await run('failure', [tracked]), []);
  assert.deepEqual(await run('success', []), []);
  assert.deepEqual(await run('cancelled', [tracked]), []);
  const recovery = await run('success', [tracked, human, unrelated, pr]);
  assert.deepEqual(recovery.map(([kind]) => kind), ['comment', 'update']);
  assert.equal(recovery[1][1].issue_number, 1);
  assert.equal(recovery[1][1].state, 'closed');
  console.log('Nightly reporting: failure, deduplication, recovery and ownership checks passed');
})().catch(error => { console.error(error); process.exitCode = 1; });
