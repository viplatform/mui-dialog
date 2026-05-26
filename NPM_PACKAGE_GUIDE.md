# Building & Publishing an NPM Package

A crisp, end-to-end playbook based on this repo (`mui-dialog`). Covers project setup → build → automated release on npm.

---

## 1. Initialize the project

```bash
mkdir my-pkg && cd my-pkg
git init
yarn init -y
```

Pick a unique, lowercase, kebab-case name. For a scoped package, use `@scope/name` (e.g. `@viplatform/mui-dialog`).

---

## 2. Core dependencies

```bash
# Build tooling
yarn add -D vite vite-plugin-dts vite-plugin-css-injected-by-js \
  @vitejs/plugin-react rollup-plugin-peer-deps-external terser typescript

# Lint / commit hygiene
yarn add -D eslint husky @commitlint/config-conventional standard-version

# Testing
yarn add -D vitest jsdom @testing-library/react @testing-library/jest-dom

# Storybook (optional, for component docs)
yarn add -D storybook @storybook/react-vite @storybook/addon-essentials
```

Library deps (e.g. React + MUI) go in `peerDependencies`, **never** `dependencies` — consumers provide them.

---

## 3. Project layout

```
src/
  index.ts            # public entry — re-exports everything
  myComponent/
    index.tsx
    types.ts
.storybook/           # component playground
.github/workflows/    # CI release pipelines
vite.config.ts
tsconfig.json
package.json
```

`src/index.ts` is the **only** public surface — see [src/index.ts](src/index.ts).

---

## 4. `package.json` essentials

The fields that make it a real library (see [package.json](package.json)):

```jsonc
{
  "name": "mui-dialog",
  "version": "1.0.34",
  "files": ["dist"],                       // what gets shipped
  "main": "./dist/mui-dialog.es.js",       // entry
  "types": "./dist/index.d.ts",            // type defs
  "exports": {                              // modern resolver
    ".": {
      "types": "./dist/index.d.ts",
      "import": "./dist/mui-dialog.es.js",
      "default": "./dist/mui-dialog.es.js"
    }
  },
  "peerDependencies": { "react": "^18 || ^19", "@mui/material": "^7" },
  "scripts": {
    "build": "yarn lint && vite build",
    "lint": "tsc --noEmit && eslint",
    "test": "vitest",
    "release": "standard-version",
    "prepublishOnly": "yarn build"         // safety net before npm publish
  }
}
```

Key rules:
- **`files`** restricts what ships to npm (everything else stays out).
- **`prepublishOnly`** guarantees a fresh build before any publish.
- **`peerDependencies`** lets the host app dedupe React, MUI, etc.

---

## 5. TypeScript config

[tsconfig.json](tsconfig.json) — strict, `noEmit: true` (Vite emits), bundler resolution, JSX `react-jsx`.

Aliases (`@components/*`) must be mirrored in `vite.config.ts` *and* in the `dts` plugin so generated `.d.ts` files resolve correctly.

---

## 6. Vite library build

See [vite.config.ts](vite.config.ts). The critical bits:

```ts
build: {
  lib: {
    formats: ["es"],                       // ESM only
    entry: "src/index.ts",
    fileName: (f) => `mui-dialog.${f}.js`
  },
  rollupOptions: {
    external: ["react", "react-dom", "@mui/material", /* …peers */]
  }
},
plugins: [
  peerDepsExternal(),                      // auto-externalize peerDeps
  react(),
  dts({ insertTypesEntry: true, outDir: "dist" }),  // emits .d.ts
  cssInjectedByJsPlugin()                  // inlines CSS into JS bundle
]
```

Run `yarn build` → produces `dist/mui-dialog.es.js` + `dist/index.d.ts`.

Smoke-test the output:
```bash
yarn pack                                  # creates a .tgz, inspect contents
npm install ../my-pkg/my-pkg-1.0.0.tgz     # in a sibling test app
```

---

## 7. Commit conventions & hooks

```bash
yarn husky init
echo 'yarn lint' > .husky/pre-commit
echo 'npx commitlint --edit "$1"' > .husky/commit-msg
```

Add [commitlint.config.js](commitlint.config.js):
```js
module.exports = { extends: ['@commitlint/config-conventional'] };
```

Commits must follow `type(scope): subject` — `feat:`, `fix:`, `chore:`. This drives changelog/version bumping.

---

## 8. Storybook (optional but recommended)

`yarn storybook` for local dev. `yarn build-storybook` produces `storybook-static/` — deploy to GitHub Pages / GCS as living docs. See [.storybook/main.ts](.storybook/main.ts).

---

## 9. Publishing — manual one-time

```bash
npm login                                  # uses registry.npmjs.org
yarn build
npm publish --access public                # --access public required for scoped pkgs
```

Verify on `https://www.npmjs.com/package/<name>`.

---

## 10. Automated release pipeline (the real workflow)

This repo uses two GitHub Actions. **Only one of them publishes to npm.**

### a) Version bump + release draft on every push to `main`
[.github/workflows/yarn-alpha-package-release.yml](.github/workflows/yarn-alpha-package-release.yml)

> Despite the workflow name ("Publish Alpha package"), it does **not** actually publish anything to npm — there is no `yarn publish` / `npm publish` step. It only prepares the next release.

What it actually does:
- Runs `yarn build` as a sanity check (artifact is discarded).
- Bumps to `x.y.z-alpha.<sha>` via `npm version prerelease --preid=alpha.<sha> --no-git-tag-version`.
- Commits the bumped `package.json` + `yarn.lock` back to `main`.
- `release-drafter` updates a draft GitHub Release using PR labels (see [.github/release-drafter.yaml](.github/release-drafter.yaml)).

**If you want real alpha publishes** (so consumers can `npm install mui-dialog@alpha`), append:
```yaml
- name: Publish alpha to npm
  run: yarn publish --tag alpha --non-interactive
  env:
    NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}
```
The `--tag alpha` is critical — without it the prerelease overwrites the `latest` dist-tag and breaks consumers on stable.

### b) Production publish on GitHub Release publish
[.github/workflows/yarn-prod-package-release.yml](.github/workflows/yarn-prod-package-release.yml)

- Triggered when you click **Publish** on the drafted release.
- Checks out the release tag, builds, and runs `yarn publish` with `NODE_AUTH_TOKEN`.
- **This is the only workflow in the repo that pushes a tarball to the npm registry.**

### Required secrets
In GitHub repo → Settings → Secrets:
- `NPM_TOKEN` — npm "Automation" token with publish rights.
- `GITHUB_TOKEN` — provided automatically.

### Release flow in practice
1. Open PR, label it `feature` / `fix` / `chore` / `major` / `minor` / `patch`.
2. Merge to `main` → version bumps to `x.y.z-alpha.<sha>` and the draft release updates. **Nothing is published yet.**
3. Open the drafted release in GitHub UI → review notes → **Publish release** → prod workflow ships the tarball to npm.

---

## 11. Version strategy

Driven by `release-drafter` labels (see config):
- `major` → 2.0.0
- `minor` → 1.1.0
- `patch` (default) → 1.0.1

For manual releases: `yarn release` → uses `standard-version` per [package.json](package.json) `scripts.release`.

---

## 12. Pre-publish checklist

- [ ] `yarn build` succeeds; `dist/` contains JS + `.d.ts`
- [ ] `yarn pack` tarball contains only what you expect (controlled by `files`)
- [ ] Smoke-tested in a real consumer app
- [ ] `peerDependencies` ranges cover supported host versions
- [ ] `README.md` + `LICENSE` present
- [ ] `name` available on npm (`npm view <name>`)
- [ ] Repo `NPM_TOKEN` secret set
