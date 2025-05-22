# BaseTable

`BaseTable` is a React component which is built to share the boilerplate code of Material React Table V3 across different projects.

---

## Features

https://www.material-react-table.com/

## Repo

https://github.com/KevinVandy/material-react-table

## Storybook

https://www.material-react-table.dev/?path=/story/features-row-pinning-examples--row-pinning-sticky-default-enabled

---

## Setup

To run this repository locally, follow these steps (ensure you're using Node version 20+):

1. **Clone this repo**
   ```bash
      git clone https://github.com/viplatform/fe-vi-dialog.git
   ```
2. **Install dependencies**
   ```bash
      npm run install
   ```

---

## Changes

Before committing any new changes, ensure everything is working correctly by running the following commands:

1. **Fix Linting Issues**

   ```bash
   npm run lint:fix
   ```

2. **Build the Project**

   ```bash
   npm run build
   ```

Make sure all of the above commands run without errors before committing your changes.

---

## Commit Lint pre-commit hook rules reference link

1. The commit message will be always in this format type(scope): subject (BLANK LINE) body (BLANK LINE) footer
2. The type is mandatory and determines the intent of the change. Here are possible values:
   - build: changes affecting build systems or external dependencies
   - ci: updating configuration files for continuous integration and deployment services
   - chore: updating grunt tasks etc.; no production code change
   - docs: documentation-only changes
   - feat: a new feature
   - fix: a bug fix
   - perf: a code change that improves performance
   - refactor: a code change that neither fixes a bug nor adds a feature
   - style: changes that do not affect the meaning of the code (white-space, formatting, missing semicolons, etc.)
   - test: adding missing tests or correcting existing tests
3. A scope is an optional value that provides additional contextual information about the change. For example, when the module’s name, npm package, or particular routine was affected. The scope, when present, must be contained within parenthesis.
4. The subject is the headline of the commit. It should summarize in one sentence the nature of change.
5. Example of few commit messages :
   - docs(changelog): update changelog to beta.5
   - fix(release): need to depend on latest rxjs and zone.js
6. More refrences
   - [What is commitlint](https://github.com/conventional-changelog/commitlint/#what-is-commitlint)
   - [Best practices around commitlint](https://www.freecodecamp.org/news/how-to-use-commitlint-to-write-good-commit-messages/)
   - [Official commitlint github page](https://github.com/conventional-changelog/commitlint)

---

## Installation of the package in other repos

To install the `BaseTable` package, follow these steps:

1. **Generate a GitHub Access Token**

   You need a GitHub access token to access private GitHub packages. To generate one:

   - Go to [GitHub Settings](https://github.com/settings/tokens).
   - Click **Generate new token**.
   - Give your token a descriptive name and select the scopes`read:packages` & `repo` for accessing packages.
   - Click **Generate token** and copy the token.

2. **Create a `.npmrc` File**

   Create a `.npmrc` file in your project root with the following configuration:

   ```
   @viplatform:registry=https://npm.pkg.github.com
   //npm.pkg.github.com/:_authToken=YOUR_GITHUB_ACCESS_TOKEN

   ```

3. **Install package**

   ```bash
   npm install @viplatform/fe-vi-dialog
   ```

   or with yarn:

   ```bash
   yarn add @viplatform/fe-vi-dialog
   ```
