# Clearance

**The approval, spend-control, and billing layer for production AI agents.**

Galuxium Nexus V2 submission — a production-shaped SaaS control plane where every high-impact agent action must pass policy + CHP governance before spend executes, with Stripe monetization and a tamper-evident audit ledger.

**Live demo:** [https://clearance-sand.vercel.app](https://clearance-sand.vercel.app)

**Demo video (~2.5 min):** [`docs/demo/clearance-demo.mp4`](docs/demo/clearance-demo.mp4) · [GitHub Release](https://github.com/icohangar-ops/clearance/releases/tag/demo-v1)

[![Next.js](https://img.shields.io/badge/Next.js-15-black)](https://nextjs.org/)
[![TypeScript](https://img.shields.io/badge/TypeScript-5.9-3178C6?logo=typescript&logoColor=white)](https://www.typescriptlang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Deployed on Vercel](https://img.shields.io/badge/Deployed-Vercel-black?logo=vercel)](https://clearance-sand.vercel.app)

---

## Market friction

Companies are shipping AI agents into support, sales, research, and finance — but finance still has no control plane. Spend is opaque, approvals live in Slack folklore, and audit trails die in chat logs.

**Clearance** is the gate: agents call one API before any paid or high-risk action. Policy packs decide auto-lock vs human review. Every decision is signed into an append-only ledger. Seats and clearances are billed through Stripe.

## Who it's for

VP Engineering + Finance Ops at mid-market companies running 10+ production agents.

## Core workflow

```text
Agent → POST /api/v1/clearance
     → Policy pack (caps, allowlists, blocked vendors)
     → CHP gate (R0 + adversarial review)
     → Memory retrieval (demo RAG / Backboard-ready)
     → Approve | Deny | Escalate to human
     → Usage meter event
     → HMAC-chained audit ledger
```

## Quick start

```bash
bun install
cp .env.example .env
bun run dev
```

Open [http://localhost:3000](http://localhost:3000) — or use the live deploy: [https://clearance-sand.vercel.app](https://clearance-sand.vercel.app).

Zero external credentials required. Demo org, agents, and policies seed automatically into `data/clearance-store.json` (on Vercel, state lives in `/tmp` per instance).

### Demo script (2–5 minutes)

Recorded walkthrough: [`docs/demo/clearance-demo.mp4`](docs/demo/clearance-demo.mp4) (captions on-screen). Re-record with:

```bash
bun add -d playwright && bunx playwright install chromium
BASE_URL=https://clearance-sand.vercel.app bun scripts/record-demo.mjs
```

Manual path:

1. Open **Dashboard** → Request clearance for `research.query` / `sec.gov` / `$12` → auto-**LOCKED**.
2. Switch to PayOps → `payment.transfer` / `stripe.com` / `$600` → `pending_human` → **Approvals**.
3. **Lock approve** → spend meter updates → **Audit** shows chained signatures.
4. Try vendor `darkweb-market` → **DENIED**.
5. **Billing** → choose a plan (demo mode updates locally; set Stripe keys for live Checkout).

Demo API key (Research Scout): `clr_live_demo_key_nexus_v2`

```bash
curl -X POST https://clearance-sand.vercel.app/api/v1/clearance \
  -H "Content-Type: application/json" \
  -H "x-api-key: clr_live_demo_key_nexus_v2" \
  -d '{"action":"research.query","vendor":"sec.gov","amountCents":1200}'
```

## Fiscal architecture

| Plan | Price | Includes |
|------|-------|----------|
| Starter | $49/mo | 3 agents, 2k clearances, email HITL, ledger export |
| Pro | $199/mo | 25 agents, 25k clearances, usage overage |
| Enterprise | Custom | SSO, audit API, dedicated memory namespace |

Live path: Stripe Checkout Sessions + webhook provisioning (`/api/stripe/webhook`). Without `STRIPE_SECRET_KEY`, billing runs in **demo mode** and updates the local plan.

### Optional live keys

Not configured on the public Vercel deploy yet (demo mode is active):

| Variable | Effect when set on Vercel |
|----------|---------------------------|
| `STRIPE_SECRET_KEY` + `STRIPE_WEBHOOK_SECRET` | Live Checkout + plan provisioning |
| `BACKBOARD_API_KEY` | Production memory / RAG hosting |

```bash
bunx vercel env add STRIPE_SECRET_KEY production
bunx vercel env add STRIPE_WEBHOOK_SECRET production
bunx vercel env add BACKBOARD_API_KEY production
bunx vercel --prod
```

## Architecture

| Layer | Implementation |
|-------|----------------|
| UI | Next.js 15 App Router, Manrope + Fraunces, server-rendered console |
| API | Route handlers under `/api/*` |
| Governance | `@cubiczan/chp` Profile B gate + Clearance adapter (`src/lib/chp.ts`) |
| Memory | Namespace retrieval; Backboard-ready via `BACKBOARD_API_KEY` |
| Persistence | JSON store (`./data` locally, `/tmp` on Vercel) |
| Audit | HMAC-SHA256 signature-chained JSONL export |
| Payments | Stripe Checkout + webhooks |

```
src/
  app/                  # Landing + console pages + API routes
  components/           # Shell, playground, approvals, billing
  lib/                  # store, chp, clearance, memory, stripe, types
docs/                   # Executive brief + fiscal blueprint + demo video
scripts/record-demo.mjs # Headless demo recorder
```

## Environment

See [`.env.example`](.env.example).

| Variable | Purpose |
|----------|---------|
| `CLEARANCE_AUDIT_KEY` | HMAC key for audit ledger |
| `CLEARANCE_DEMO_API_KEY` | Seed API key for Research Scout |
| `STRIPE_SECRET_KEY` | Enables live Checkout |
| `STRIPE_WEBHOOK_SECRET` | Verifies subscription webhooks |
| `BACKBOARD_API_KEY` | Optional production memory/RAG |

## API surface

| Method | Path | Description |
|--------|------|-------------|
| `POST` | `/api/v1/clearance` | Evaluate clearance (requires `x-api-key`) |
| `GET` | `/api/v1/clearance` | Recent clearances |
| `GET/POST` | `/api/agents` | List / register agents |
| `GET/POST` | `/api/approvals` | HITL queue + resolve |
| `GET` | `/api/audit` | Ledger JSON (`?format=jsonl` to download) |
| `GET` | `/api/usage` | Dashboard aggregate |
| `POST` | `/api/stripe/checkout` | Start subscription Checkout |
| `POST` | `/api/stripe/webhook` | Provision plan from Stripe |
| `POST` | `/api/demo` | Reset store / set plan |

## Nexus V2 submission checklist

- [x] Production-ready app deployed on Vercel: https://clearance-sand.vercel.app
- [x] Public GitHub + Codeberg repositories with architecture README
- [x] Operational MVP: clearance → CHP → HITL → meter → audit
- [x] Executive brief: [`docs/EXECUTIVE_BRIEF.md`](docs/EXECUTIVE_BRIEF.md)
- [x] Fiscal architecture: [`docs/FISCAL_ARCHITECTURE.md`](docs/FISCAL_ARCHITECTURE.md)
- [x] Demo video (2–5 min): [`docs/demo/clearance-demo.mp4`](docs/demo/clearance-demo.mp4)

## Deploy

```bash
# Vercel (already live)
bunx vercel --prod

# Docker
docker build -t clearance .
docker run -p 3000:3000 -e CLEARANCE_AUDIT_KEY=change-me clearance
```

Production URL: **https://clearance-sand.vercel.app**

For durable multi-instance production, replace the JSON store with Postgres/Turso and put `data/` on a volume only for single-node demos.

## Repositories

| Remote | URL |
|--------|-----|
| GitHub (ops) | https://github.com/icohangar-ops/clearance |
| GitHub (Cubiczan) | https://github.com/Cubiczan/clearance |
| Codeberg | https://codeberg.org/cubiczan/clearance |

## CHP dependency

Depends on **[`@cubiczan/chp`](https://www.npmjs.com/package/@cubiczan/chp)** (`^0.1.1`) for Profile B capital-gate evaluation (`evaluateGate` / `approveHuman`). Clearance keeps a thin adapter in `src/lib/chp.ts` for org policy, blocked vendors, and HITL wiring.

See also the promoted example: [icohangar-ops/chp-examples](https://github.com/icohangar-ops/chp-examples) → `typescript/clearance-gate/`.

## Cubiczan stack lineage

Clearance productizes patterns from:

- [@cubiczan/chp](https://www.npmjs.com/package/@cubiczan/chp) / [consensus-hardening-protocol](https://github.com/icohangar-ops/consensus-hardening-protocol) — CHP locks
- [cleanmandate](https://github.com/icohangar-ops/cleanmandate) — payment mandates
- [agent-observability](https://github.com/icohangar-ops/agent-observability) — spend visibility
- [meshcfo](https://github.com/icohangar-ops/meshcfo) — auditable finance agents
- [Live-Diligence](https://github.com/icohangar-ops/Live-Diligence) — Stripe subscription patterns

## License

MIT © Cubiczan / Shyam Desigan
