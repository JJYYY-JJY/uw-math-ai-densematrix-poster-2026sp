# Issue Tracker: GitHub

Issues and PRDs for this repo live in GitHub Issues for `uw-math-ai/provable_computation`.
Use the `gh` CLI for issue operations from inside this clone.

## Conventions

- **Create an issue**: `gh issue create --title "..." --body "..."`
- **Read an issue**: `gh issue view <number> --comments`
- **List issues**: `gh issue list --state open --json number,title,body,labels,comments`
- **Comment on an issue**: `gh issue comment <number> --body "..."`
- **Apply or remove labels**: `gh issue edit <number> --add-label "..."` or `gh issue edit <number> --remove-label "..."`
- **Close an issue**: `gh issue close <number> --comment "..."`

Infer the repository from `git remote -v`; `gh` does this automatically when run inside this clone.

## When a Skill Says "Publish to the Issue Tracker"

Create a GitHub issue.

## When a Skill Says "Fetch the Relevant Ticket"

Run `gh issue view <number> --comments`.
