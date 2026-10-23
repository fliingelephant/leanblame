# LeanBlame documentation

Read in order. Each file is short.

| # | File | Question it answers |
|---|------|---------------------|
| 1 | [01-motivation.md](01-motivation.md) | Why does this need to exist? |
| 2 | [02-concepts.md](02-concepts.md) | What are the five or six words we use everywhere? |
| 3 | [03-architecture.md](03-architecture.md) | What are the parts, and which repo owns what? |
| 4 | [04-records.md](04-records.md) | What exactly does a signer sign, and how is it stored? |
| 5 | [05-versioning.md](05-versioning.md) | What happens when mathlib or the library changes? Who is blamed? |
| 6 | [06-releases-and-eval.md](06-releases-and-eval.md) | How are versions released, and how do we measure library quality? |
| 7 | [07-identity.md](07-identity.md) | How do reviewers log in and get an ID? |
| 8 | [08-performance.md](08-performance.md) | Where does checking time go, and what can be made faster? |
| 9 | [09-prior-art.md](09-prior-art.md) | Who did similar things, in Lean and elsewhere? |
| 10 | [10-decisions.md](10-decisions.md) | Decision log and FAQ. Why not X? |
| 11 | [11-roadmap.md](11-roadmap.md) | What exists, what to build, in what order. |

One-paragraph summary:

> Lean's `comparator` already splits a formal result into a trusted statement
> file and an untrusted proof file, and checks the proof. LeanBlame records
> which human read the trusted file, at which kernel-level hash, and when.
> Trust flows through people like `git blame`: an imported definition is
> trusted because a named person signed it. When upstream changes, `status`
> names the changed constant, `equiv` has an agent try to prove old equals
> new, and a human decides whether the old signoff carries. Records are never
> deleted. Three parts: a Lean CLI, signoff records in git, a web sign server
> and page.
