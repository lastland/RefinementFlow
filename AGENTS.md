## Agent skills

### Issue tracker

Issues and PRDs are tracked as local Markdown under `.scratch/<feature-slug>/`; external PRs are not a triage surface. See `docs/agents/issue-tracker.md`.

### Triage labels

The five canonical triage roles use their default strings in issue `Status:` lines. See `docs/agents/triage-labels.md`.

### Domain docs

Single-context: root `CONTEXT.md` and `docs/adr/`. See `docs/agents/domain.md`.

### Cost conventions

Use [docs/agents/cost-conventions.md](docs/agents/cost-conventions.md) for the approved project-wide charging rules, the L1 revision, and current assurance status.

## Program construction

- Keep behavioral and resource specifications algorithm-independent. Let the derivation choose the algorithm and concrete resource-bound witnesses within researcher-approved construction constraints.
- Construct each target implementation inside its `Derive ... in ... as ...` proof. Reusable primitives and proof rules belong in the shared library.
- Use the shared `cost_iter` combinator for target-program loops.

## Coq/Rocq conventions

Use notation supplied by ITree and ext-lib wherever it applies.

- For ITree computations, use `ITreeNotations`: `value <- computation ;; next value`, `computation ;; next`, or `computation >>= continuation`. Emit events with `trigger event`.
- For ext-lib computations, use `MonadNotation`, `FunctorNotation`, and `ApplicativeNotation` as applicable.
- For ITree propositions and types, use `result ∈ program` (`LeafNotations`), `program ⤳ post` (`HasPostNotations`), `program ≈ next`, `program ≅ next`, and `E ~> F`. Use `SumNotations` for explicit event-sum injections.

Import notation modules where used and open scopes locally. Disambiguate mixed monadic expressions with `%itree` and `%monad`.

Name constants directly when proof tactics or higher-order APIs require them, such as `unfold ITree.bind` or `Proper (eq_itree eq ==> ...)`. Use named operations when the library supplies no applicable notation.
