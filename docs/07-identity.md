# 7. Identity

## Principle

Reviewers may not have GitHub accounts. Many physicists do not. Login goes
through any OpenID Connect or OAuth provider. The record stores the signer as
`provider:id`.

## Providers

| Provider | Notes |
|----------|-------|
| `local` | Dev and test only. |
| `openreview` | Standard OpenID Connect, Authorization Code with PKCE. `sub` is the stable profile ID, e.g. `~Jane_Doe1`; `name` and `email` by scope. No refresh tokens; access expires after 1 hour. Client registration is manual: email the OpenReview team with your `client_id`, app name, redirect URIs, scopes. No ORCID claim in the token. Source: docs.openreview.net/reference/sign-in-with-openreview, read 2026-10-23. |
| `orcid` | OAuth / OIDC. Gives the ORCID iD. Self-service client registration. |
| `github` | OAuth. For developers who prefer it. |
| institutional | Later. eduGAIN / InCommon through CILogon, which also offers ORCID login and returns affiliation claims. |

One generic OIDC adapter covers all of them. OpenPhysics configures which ones
to enable and the client IDs.

## Profiles

The page shows a signer's records and links to their provider profile
(OpenReview, ORCID, GitHub). A person who logs in through two providers is two
IDs until they link accounts on their profile. Account linking is a later
feature.

## Cryptographic signatures

Not now. Records are trusted because the sign server wrote them after a login
and the records repo is append-only.

If forgery ever becomes a real concern, add Sigstore keyless signing: the
reviewer signs with a university email in a browser, and the signature is
logged in the Rekor transparency log. Public Sigstore accepts Google and
Microsoft email logins; whether university-managed Microsoft accounts work is
unconfirmed. A private Fulcio instance could trust CILogon or ORCID directly.
Parked by decision.

## OpenReview openness

For reference: OpenReview's web frontend is AGPL-3.0, its Python and JS
clients are MIT, its backend API server is not published. You cannot self-host
OpenReview. For LeanBlame this does not matter; OpenReview is only a login
provider.
