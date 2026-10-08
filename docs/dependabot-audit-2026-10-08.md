# Dependency security verification — 2026-10-08

The proposed lockfiles remove all 3 currently open GitHub alert/version matches in this repository. This is a pre-merge verification, not a claim that GitHub has closed the alerts.

Every exact package/version in both lockfiles was checked against the npm bulk advisory endpoint and OSV querybatch. All current GitHub advisory ranges were separately checked for every proposed patch version. No new advisory matches were introduced, and OSV returned no vulnerabilities for any newly selected version. npm and OSV agree on the remaining findings. Aliased Yarn dependencies were checked under their real package names.

| Lockfile | Advisory range matches before | After | Newly introduced | OSV package/version queries |
| --- | ---: | ---: | ---: | ---: |
| npm | 12 | 7 | 0 | 737 |
| yarn | 8 | 7 | 0 | 734 |

These counts are package/advisory/range matches, not GitHub alert counts. Remaining findings are reviewed exceptions, not patched vulnerabilities.

## Open alert verification

| Alert | Package | Resulting versions | Lockfile |
| --- | --- | --- | --- |
| [#104](https://github.com/viplatform/mui-dialog/security/dependabot/104) | source-map-js | 1.2.2 | yarn.lock |
| [#100](https://github.com/viplatform/mui-dialog/security/dependabot/100) | source-map-js | 1.2.2 | package-lock.json |
| [#97](https://github.com/viplatform/mui-dialog/security/dependabot/97) | brace-expansion | 1.1.21, 2.1.7, 5.0.12 | package-lock.json |

## Remaining findings and applicability

- [@humanfs/node — GHSA-p498-v437-472g](https://github.com/advisories/GHSA-p498-v437-472g): ESLint filesystem tooling only. The consuming ESLint code does not call copy/copyAll; no application import reaches the affected symlink-copy API.
- [@vitest/mocker — GHSA-82fw-gwwq-j7x9](https://github.com/advisories/GHSA-82fw-gwwq-j7x9): Vitest development tooling only. No checked-in tests, browser-mode server, mockerPlugin or interceptorPlugin registration; the vulnerable public mock-registration/file-serving path is absent.
- [sprintf-js — GHSA-hp3w-g68c-fv3c](https://github.com/advisories/GHSA-hp3w-g68c-fv3c): Only argparse CLI/help tooling consumes repository-controlled format/help strings. No application accepts attacker-controlled format strings. No published patched version.
- [tinypool — GHSA-5gmw-xhrv-c9v3](https://github.com/advisories/GHSA-5gmw-xhrv-c9v3): Vitest-only development dependency with no checked-in tests, CI Vitest execution or application worker-pool calls. The affected worker options are not exercised. The patched 2.1.2 branch requires Node 20 or >=22 and is outside Vitest 3’s ^1.1.1 range; reassess if tests/workers are added.
- [tinypool — GHSA-85c8-ppgw-ccpr](https://github.com/advisories/GHSA-85c8-ppgw-ccpr): Vitest-only development dependency with no checked-in tests, CI Vitest execution or application worker-pool calls. The affected worker options are not exercised. The patched 2.1.2 branch requires Node 20 or >=22 and is outside Vitest 3’s ^1.1.1 range; reassess if tests/workers are added.
- [uuid — GHSA-w5hq-g745-h8pq](https://github.com/advisories/GHSA-w5hq-g745-h8pq): Storybook addon-actions uses uuid.v4() without a caller-provided buffer; the advisory affects v3/v5/v6 buffer writes, which this consumer does not use.
- [vitest — GHSA-82fw-gwwq-j7x9](https://github.com/advisories/GHSA-82fw-gwwq-j7x9): No checked-in tests or CI Vitest execution, and no browser-mode mock-registration server. The affected file-read path is absent. Vitest 4 would drop Node 18 support.

## Compatibility and validation

Production build and existing dependency security regression checks pass with the Yarn dependency tree. Frozen Yarn installs preserve both lockfiles. Targeted dependency API checks pass on Node 18.20.8 and Node 20.20.2. These checks do not establish that the entire project toolchain supports Node 18.

brace-expansion 5.0.12 declares Node `20 || >=22`; the previously locked 5.x versions already had that requirement. The 1.1.21 and 2.1.7 branches retain Node 18 compatibility. No legacy 1.x or 2.x consumer is moved to 5.x by these npm overrides. Existing Yarn overrides that already use 5.x are retained.

A separate clean npm installation was checked to verify the npm lockfile independently. npm ci and the existing dependency security checks pass without modifying package-lock.json. Clean npm build reproduces the existing ajv-draft-04 peer-resolution failure (`Cannot find module ajv/dist/core`) on the unchanged merged baseline. Yarn build passes.

## Evidence and limits

[Machine-readable verification](dependabot-audit-2026-10-08.json) records exact lockfile hashes, every open alert comparison, changed-version OSV results, package engine metadata, and all retained findings. Sources: [GitHub Advisory API](https://docs.github.com/en/rest/security-advisories/global-advisories), [npm audit endpoint](https://docs.npmjs.com/cli/v10/commands/npm-audit#bulk-advisory-endpoint), and [OSV querybatch](https://google.github.io/osv.dev/post-v1-querybatch/).

This establishes no newly introduced **currently known** vulnerabilities in the scanned trees. It cannot rule out undisclosed vulnerabilities or advisories published later. Keep this PR in draft until review and the documented build limitations are accepted; merge approval is not requested by this report.
