# 8. Identity

## Principle

Reviewers may not have GitHub accounts. Login goes through a standard provider.
The record stores a **stable** id as `provider:id`.

## Providers

| Provider | Protocol | Stable id | Notes |
|----------|----------|-----------|-------|
| `local` | none | chosen name | dev and test only |
| `openreview` | OpenID Connect, code flow with PKCE | profile id, e.g. `~Jane_Doe1` | sessions last 1 hour, no silent renewal; registration by emailing the OpenReview team your client id, app name, redirect URLs, scopes; no ORCID in the token. Source: docs.openreview.net/reference/sign-in-with-openreview, read 2026-10-23 |
| `orcid` | OpenID Connect | ORCID iD | self-service registration |
| `github` | OAuth 2.0 only, no ID token | numeric user id, never the login | needs its own small adapter |
| institutional | later | eduGAIN / InCommon via CILogon, which also offers ORCID and returns affiliation |

One OpenID Connect adapter covers OpenReview and ORCID. GitHub gets a separate
OAuth adapter.

## Profiles

The page shows a signer's records and links to their provider profile. One
person with two providers is two ids until they link accounts. Later feature.

## Who you are trusting

Records are trusted because the sign server wrote them after a login and CI
rejects edits to existing records. The trusted party is whoever holds the sign
server's push credential, normally the hosting institution. Name it.

## Cryptographic signatures

Not now. If forgery becomes a concern, add Sigstore keyless signing: the
reviewer signs with a university email in a browser; the signature is logged in
Rekor. Public Sigstore accepts Google and Microsoft email logins; whether
university Microsoft accounts work is unconfirmed. Parked.

## OpenReview openness

Web frontend AGPL-3.0, Python and JS clients MIT, backend not published. You
cannot self-host OpenReview. Irrelevant for login use.
