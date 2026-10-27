# Domain Docs

This repo uses a single context: `CONTEXT.md` and `docs/adr/` at the repo root.

## Before exploring, read these

- **`CONTEXT.md`** — read the project's domain language.
- **`docs/adr/`** — read ADRs that touch the area you're about to work in.

If these files or directories don't exist, **proceed silently**. Don't flag their absence or suggest creating them upfront. The `/domain-modeling` skill (reached via `/grill-with-docs` and `/improve-codebase-architecture`) creates them lazily when terms or decisions actually get resolved.

## File structure

```text
/
├── CONTEXT.md
└── docs/
    └── adr/
        └── NNNN-<decision>.md
```

## Use the glossary's vocabulary

When your output names a domain concept (in an issue title, a refactor proposal, a hypothesis, or a test name), use the term as defined in `CONTEXT.md`. Don't drift to synonyms the glossary explicitly avoids.

If the concept you need isn't in the glossary yet, reconsider whether it belongs to the project's language. If there's a real gap, note it for `/domain-modeling`.

## Flag ADR conflicts

If your output contradicts an existing ADR, surface it explicitly rather than silently overriding it. Identify the ADR and explain why the decision may be worth reopening.
