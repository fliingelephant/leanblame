# 13. Glossary

| Term | Meaning |
|------|---------|
| **mathlib** | The main Lean 4 mathematics library. |
| **physlib** | An existing Lean physics library. Any upstream library is treated the same way. |
| **declaration / constant** | One named thing in a Lean environment: def, theorem, structure, axiom, instance. |
| **kind** | What a declaration is. The hash takes the kernel's kind (Lean: `def`, `theorem`, `inductive`, …); the boundary list and `status` show the documentation's word (`structure`, `field`, `instance`, …). Never interpreted. |
| **role** | What a declaration's body is to a signer: `assumed` (none), `defined` (the meaning, read), `proved` (a proof, never read). The hash rules read it. |
| **export** | Output of `leanexport`: every constant with its type and body, as the kernel sees it. |
| **frontend** | The part of LeanBlame that knows one proof assistant: reads its exports, prints its terms, asks its kernel. Lean's is the only one. See [04-architecture.md](04-architecture.md), "Beyond Lean". |
| **closure** | A declaration plus everything it uses, recursively. |
| **boundary list** | The declarations a human must read, with their informal text. Input to LeanBlame. |
| **tagged** | On the boundary list. `@[trusted]` is the usual way. |
| **id** | A declaration's random UUID, in its tag (`@[trusted "id"]`, or `attribute [trusted "id"] Name` after the fact), written by `leanblame id`; a structure's field has the structure's id and its name. Survives renames; never hashed. Records name declarations by it. Cite as `id@record`. |
| **informal text** | The docstring, or the blueprint's statement text. The spec a signer relies on. |
| **spec** | Name, type, informal text of a declaration. What its users sign. |
| **claim hash** | Hash of what one signoff covers. See [03-trust-model.md](03-trust-model.md). |
| **record** | One signoff file: approve or withdraw. |
| **live record** | An approve record that counts for a declaration: no counting withdraw covers it, not excluded, signer allowed. Defined in [05-records.md](05-records.md). |
| **standing** | What an approval is worth now: `current`, `superseded`, `withdrawn`, `excluded` or `not-allowed`. |
| **blocked** | Your hash is fine but a tagged dependency isn't valid. Wait for its signer. |
| **`equiv`** | Command that rebuilds an old meaning from the old export and asks the kernel whether it is definitionally equal to the new one. |
| **kernel gate** | `leanchecker --from-export` replaying the whole export inside `release`. |
| **axiom report** | Per theorem, the axioms it rests on: proven (standard or signed tagged axioms only) or open (`sorryAx`, or any other axiom). |
| **cause** | Why a hash moved: `own-text`, `own-body`, `dep-spec`, `cut-moved`, `untagged`. |
| **group hash** | Hash of a cycle (an inductive with its constructors, or mutual definitions) as one unit. |
| **exclude** | A maintainer's decision in `leanblame.toml` to stop counting an approve record. The dispute mechanism. Withdrawals cannot be excluded. |
| **comparator** | Lean FRO's checker for untrusted proofs against a trusted statement file. Source of the closure walk. |
| **challenge** | What a comparator checks a solution against: `ChallengeDeps.lean`, what the statements need, and `Challenge.lean`, the statements with proofs `sorry`. `leanblame challenge` writes one from pieces and checks it. |
| **piece** | One command of a library's source that a challenge needs, as written, with its scope commands. `export` stores each module's pieces. |
| **nanoda, con-ron, con-leche** | Independent re-implementations of the Lean kernel, used as extra checkers. |
| **AXLE, Kimina, Pantograph** | Fast proof-check services that trust the elaborator. Filters, not gates. |
| **verso-blueprint, LeanArchitect** | Blueprint tools: prose, Lean declarations and dependency graph in one document. verso-blueprint's manifest is a boundary-list source; both are possible `status --json` consumers. |
| **lean-eval** | Lean FRO's comparator-based benchmark. Its per-problem TOML files are the model for records. |
| **OpenID Connect / OAuth 2.0** | Login protocols. OpenReview and ORCID speak the first; GitHub only the second. |
| **ORCID / ROR** | Persistent ids for researchers / institutions. |
| **Sigstore** | Keyless cryptographic signing with an email login. Parked. |
