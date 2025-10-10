# GitHub Actions Workflows Documentation

This repository uses GitHub Actions for continuous integration and quality assurance. This document describes each workflow and its purpose.

## Workflows Overview

### 1. Repository CI (`ci.yml`)

**Triggers:** Push and Pull Requests to `main` and `develop` branches

**Purpose:** Validates the overall repository structure and generates metrics

**Jobs:**
- **validate-structure**: Checks for critical files (README.md, UNIFICACION_RH-BSD-GRH-GOLDBACH.md)
- **check-for-duplicates**: Scans for duplicate files with naming patterns like `(1)`, `(2)`, etc.
- **generate-metrics**: Produces statistics about documentation files and repository content

**What it checks:**
- ✓ Critical documentation files exist
- ✓ GitHub Actions workflows are present
- ✓ No duplicate files with suspicious naming patterns
- ✓ Repository metrics (file counts, line counts)

---

### 2. Documentation Check (`documentation-check.yml`)

**Triggers:** Push and Pull Requests to `main` and `develop` branches

**Purpose:** Ensures documentation quality and completeness

**Jobs:**
- **documentation-check**: Verifies required files, validates LaTeX syntax, and generates documentation summaries

**What it checks:**
- ✓ Required documentation files exist
- ✓ LaTeX equations are properly formatted in markdown
- ✓ Documentation summary with file metrics

**Artifacts:** Generates `documentation-summary.md` as a build artifact

---

### 3. Markdown Lint (`markdown-lint.yml`)

**Triggers:** Push and Pull Requests to `main` and `develop` branches (when `.md` files change)

**Purpose:** Maintains consistent markdown formatting and checks for broken links

**Jobs:**
- **markdown-lint**: Lints all markdown files and checks for broken links

**What it checks:**
- ✓ Markdown style consistency (using markdownlint-cli)
- ✓ Broken or invalid links (using markdown-link-check)

**Configuration:**
- `.markdownlint.json` - Markdown linting rules
- `.markdown-link-check.json` - Link checking configuration

---

### 4. Greetings (`greetings.yml`)

**Triggers:** First-time issues and pull requests

**Purpose:** Welcomes new contributors and provides guidance

**Jobs:**
- **greeting**: Automatically posts welcome messages to first-time contributors

**Messages:**
- First issue: Welcomes contributor and explains the project
- First PR: Provides contribution guidelines and expectations

---

## Configuration Files

### `.markdownlint.json`

Configures markdown linting rules:
- Disables line length checks (MD013) for mathematical content
- Allows HTML (MD033) for special formatting
- Allows duplicate headings in different sections (MD024)

### `.markdown-link-check.json`

Configures link checking:
- Ignores localhost links
- Sets timeouts and retry logic
- Handles rate limiting (429 errors)

---

## Running Workflows Locally

While GitHub Actions run automatically, you can test workflow logic locally:

### Test Repository Structure Validation

```bash
# Check for critical files
bash .github/workflows/ci.yml # (extract and run the validation script)
```

### Test Markdown Linting

```bash
# Install markdownlint-cli
npm install -g markdownlint-cli

# Run markdown linting
markdownlint '**/*.md' --ignore node_modules --config .markdownlint.json
```

### Test Link Checking

```bash
# Install markdown-link-check
npm install -g markdown-link-check

# Check links in markdown files
find . -name "*.md" -not -path "*/node_modules/*" -exec markdown-link-check {} \;
```

---

## Workflow Status

You can check the status of workflows in the GitHub Actions tab of the repository:

- 🟢 **Green**: All checks passed
- 🟡 **Yellow**: Workflow is running
- 🔴 **Red**: Some checks failed

---

## Contributing

When contributing to this repository:

1. All workflows will run automatically on your PR
2. Ensure all checks pass before requesting review
3. Fix any markdown linting issues reported
4. Verify that documentation files follow the standard format

---

## Future Enhancements

Potential workflow improvements:

- [ ] Add automated testing for Lean formalization (when present)
- [ ] Add Python code linting and testing (when Python code is added)
- [ ] Add spell checking for documentation
- [ ] Add automated LaTeX compilation and validation
- [ ] Add dependency scanning for security

---

*Last Updated: October 2025*
