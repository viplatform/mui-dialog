import assert from 'node:assert/strict';

async function verifySecurityDependencies() {
  const { default: browserslist } = await import('browserslist');
  const expected = browserslist('defaults');
  for (const key of ['__proto__', 'toString', 'valueOf', 'constructor', 'hasOwnProperty', 'isPrototypeOf']) {
    const stats = JSON.parse(JSON.stringify({ [key]: { one: 5 }, chrome: { 100: 50 } }));
    assert.deepEqual(browserslist('defaults', { stats }), expected);
  }
  console.log('Security dependency regressions passed');
}

verifySecurityDependencies().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
