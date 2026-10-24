# 13. Glossary

| Term | Meaning |
|------|---------|
| **mathlib** | The main Lean 4 mathematics library. |
| **physlib** | An existing Lean physics library. Any upstream library is treated the same way. |
| **declaration / constant** | One named thing in a Lean environment: def, theorem, structure, axiom, instance. |
| **export** | Output of `leanexport`: every constant with its type and body, as the kernel sees it. |
| **closure** | A declaration plus everything it uses, recursively. |
| **boundary list** | The declarations a human must read, with their informal text. Input to LeanBlame. |
| **tagged** | On the boundary list. `@[trusted]` is the usual way. |
| **informal text** | The docstring, or the blueprint node text. The spec a signer relies on. |
| **spec** | Name, type, informal text of a declaration. What its users sign. |
| **claim hash** | Hash of what one signoff covers. See [03-trust-model.md](03-trust-model.md). |
| **record** | One signoff file: approve or withdraw. |
| **live record** | An approve record that counts for a constant: no counting withdraw covers it, signer allowed. Defined in [05-records.md](05-records.md). |
| **blocked** | Your hash is fine but a tagged dependency isn't valid. Wait for its signer. |
| **`equiv`** | Command that rebuilds an old meaning from the old export and asks the kernel whether it is definitionally equal to the new one. |
| **kernel gate** | `leanchecker --from-export` replaying the whole export inside `release`. |
| **axiom report** | Per theorem, the axioms it rests on: proven (standard or signed tagged axioms only) or open (`sorryAx`, or any other axiom). |
| **cause** | Why a hash moved: `own-text`, `own-body`, `dep-spec`, `cut-moved`, `untagged`. |
| **group hash** | Hash of a cycle (an inductive with its constructors, or mutual definitions) as one unit. |
| **exclude** | A maintainer's decision in `leanblame.toml` to stop counting an approve record. The dispute mechanism. Withdrawals cannot be excluded. |
| **comparator** | Lean FRO's checker for untrusted proofs against a trusted statement file. Source of the closure walk. |
| **nanoda, con-ron, con-leche** | Independent re-implementations of the Lean kernel, used as extra checkers. |
| **AXLE, Kimina, Pantograph** | Fast proof-check services that trust the elaborator. Filters, not gates. |
| **doc-gen4** | Lean's documentation generator. Our page base. |
| **verso-blueprint, LeanArchitect** | Blueprint tools: prose, Lean declarations and dependency graph in one document. Possible boundary-list sources and `status --json` consumers. |
| **lean-eval** | Lean FRO's comparator-based benchmark. Its per-problem TOML files are the model for records. |
| **OpenID Connect / OAuth 2.0** | Login protocols. OpenReview and ORCID speak the first; GitHub only the second. |
| **ORCID / ROR** | Persistent ids for researchers / institutions. |
| **Sigstore** | Keyless cryptographic signing with an email login. Parked. |
