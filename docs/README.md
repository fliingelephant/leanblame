# LeanBlame documentation

Read in order. Each file is short.

| # | File | Question it answers |
|---|------|---------------------|
| 1 | [01-motivation.md](01-motivation.md) | Why does this need to exist? |
| 2 | [02-concepts.md](02-concepts.md) | What are the seven words we use everywhere? |
| 3 | [03-trust-model.md](03-trust-model.md) | **What exactly does a signature cover, and what happens on change?** Read this one. |
| 4 | [04-architecture.md](04-architecture.md) | What are the parts, and which repo owns what? |
| 5 | [05-records.md](05-records.md) | How is a signoff stored? |
| 6 | [06-versioning.md](06-versioning.md) | What happens when mathlib or the library changes? Who is blamed? |
| 7 | [07-releases-and-eval.md](07-releases-and-eval.md) | How are versions released, and how do we measure library quality? |
| 8 | [08-identity.md](08-identity.md) | How do reviewers log in and get an ID? |
| 10 | [10-prior-art.md](10-prior-art.md) | Who did similar things, in Lean and elsewhere? |
| 11 | [11-decisions.md](11-decisions.md) | Decision log and FAQ. Why not X? |
| 12 | [12-roadmap.md](12-roadmap.md) | What exists, what to build, in what order. |
| 13 | [13-glossary.md](13-glossary.md) | Every term, one line. |
| 14 | [14-schemas.md](14-schemas.md) | Exact fields of the four interfaces. For implementers. |

One-paragraph summary:

> The Lean kernel checks proofs. LeanBlame records which human approved which
> declarations, at which kernel-level hash, and when. Trust flows through
> people like `git blame`: you sign your own declaration fully, you sign only
> the name, type and informal text of signed declarations you use, and you sign
> everything of unsigned ones. When upstream changes, `status` says what moved
> and why. If only unsigned code underneath changed, `equiv` asks the kernel
> whether the meaning is the same, and a human approves the new hash with one
> click. Records are never deleted. Three parts: a Lean CLI, signoff records
> in git, a web sign server and page.
