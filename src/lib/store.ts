import { createHash, createHmac, randomBytes, timingSafeEqual } from "crypto";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "fs";
import path from "path";
import type {
  Agent,
  ApprovalItem,
  AuditRecord,
  ClearanceRequest,
  MemoryDoc,
  Org,
  PolicyPack,
  StoreShape,
  UsageEvent,
} from "./types";

// Local: ./data — Vercel/serverless: /tmp (writable). Override with CLEARANCE_DATA_DIR.
const DATA_DIR =
  process.env.CLEARANCE_DATA_DIR ||
  (process.env.VERCEL || process.env.AWS_LAMBDA_FUNCTION_NAME
    ? path.join("/tmp", "clearance-data")
    : path.join(process.cwd(), "data"));
const DATA_FILE = path.join(DATA_DIR, "clearance-store.json");

function hashKey(raw: string): string {
  return createHash("sha256").update(raw).digest("hex");
}

function previewKey(raw: string): string {
  return `${raw.slice(0, 8)}…${raw.slice(-4)}`;
}

export function getAuditSigningKey(): string {
  return process.env.CLEARANCE_AUDIT_KEY || "clearance-demo-audit-key-change-me";
}

function seedStore(): StoreShape {
  const demoApiKey = process.env.CLEARANCE_DEMO_API_KEY || "clr_live_demo_key_nexus_v2";
  const orgId = "org_acme";
  const agentResearchId = "agt_research";
  const agentPayId = "agt_payops";
  const agentSupportId = "agt_support";

  const org: Org = {
    id: orgId,
    name: "Acme Operations",
    plan: "pro",
    clearanceQuota: 25000,
    clearanceUsed: 128,
    createdAt: new Date().toISOString(),
  };

  const agents: Agent[] = [
    {
      id: agentResearchId,
      orgId,
      name: "Research Scout",
      description: "Web + filings research agent for diligence memos",
      riskTier: ["routine", "elevated"],
      spendCapCents: 50000,
      spendUsedCents: 12400,
      allowlist: ["sec.gov", "exa.ai", "backboard.io"],
      apiKeyHash: hashKey(demoApiKey),
      apiKeyPreview: previewKey(demoApiKey),
      memoryNamespace: "acme/research",
      active: true,
      createdAt: new Date().toISOString(),
    },
    {
      id: agentPayId,
      orgId,
      name: "PayOps Runner",
      description: "Vendor payment and invoice follow-up agent",
      riskTier: ["routine", "elevated", "critical"],
      spendCapCents: 250000,
      spendUsedCents: 78000,
      allowlist: ["stripe.com", "quickbooks", "xero"],
      apiKeyHash: hashKey(`${demoApiKey}_pay`),
      apiKeyPreview: previewKey(`${demoApiKey}_pay`),
      memoryNamespace: "acme/payops",
      active: true,
      createdAt: new Date().toISOString(),
    },
    {
      id: agentSupportId,
      orgId,
      name: "Support Concierge",
      description: "Customer support triage with refund proposals",
      riskTier: ["routine"],
      spendCapCents: 10000,
      spendUsedCents: 2100,
      allowlist: ["zendesk", "intercom"],
      apiKeyHash: hashKey(`${demoApiKey}_support`),
      apiKeyPreview: previewKey(`${demoApiKey}_support`),
      memoryNamespace: "acme/support",
      active: true,
      createdAt: new Date().toISOString(),
    },
  ];

  const policies: PolicyPack[] = [
    {
      id: "pol_default",
      orgId,
      name: "Default enterprise pack",
      maxAutoApproveCents: 25000,
      requireHumanAboveCents: 25000,
      blockedVendors: ["darkweb-market", "unlisted-crypto-otc"],
      allowedActions: [
        "tool.invoke",
        "payment.transfer",
        "email.send",
        "refund.issue",
        "research.query",
      ],
    },
  ];

  const memory: MemoryDoc[] = [
    {
      id: "mem_1",
      namespace: "acme/research",
      text: "Prior clearance: research.query under $50 auto-approved when vendor is sec.gov or exa.ai.",
      tags: ["policy", "research"],
      createdAt: new Date().toISOString(),
    },
    {
      id: "mem_2",
      namespace: "acme/payops",
      text: "Vendor Stripe invoices under $250 auto-lock. Amounts above $250 require human CHP review.",
      tags: ["policy", "payments"],
      createdAt: new Date().toISOString(),
    },
    {
      id: "mem_3",
      namespace: "acme/payops",
      text: "Blocked vendor darkweb-market on 2026-06-12 after compliance review.",
      tags: ["blocklist", "compliance"],
      createdAt: new Date().toISOString(),
    },
    {
      id: "mem_4",
      namespace: "org/policy",
      text: "CHP R0: actions must be Solvable, Scoped, Valid, Worth_it. Finance category threshold = 100.",
      tags: ["chp", "governance"],
      createdAt: new Date().toISOString(),
    },
  ];

  return {
    org,
    agents,
    policies,
    clearances: [],
    approvals: [],
    audit: [],
    usage: [],
    memory,
    demoApiKey,
  };
}

let cache: StoreShape | null = null;

function ensureDir() {
  if (!existsSync(DATA_DIR)) mkdirSync(DATA_DIR, { recursive: true });
}

export function loadStore(): StoreShape {
  if (cache) return cache;
  ensureDir();
  if (!existsSync(DATA_FILE)) {
    cache = seedStore();
    persistStore(cache);
    return cache;
  }
  cache = JSON.parse(readFileSync(DATA_FILE, "utf8")) as StoreShape;
  return cache;
}

export function persistStore(store: StoreShape) {
  ensureDir();
  cache = store;
  writeFileSync(DATA_FILE, JSON.stringify(store, null, 2), "utf8");
}

export function resetStore(): StoreShape {
  cache = seedStore();
  persistStore(cache);
  return cache;
}

export function mutateStore<T>(fn: (store: StoreShape) => T): T {
  const store = loadStore();
  const result = fn(store);
  persistStore(store);
  return result;
}

export function verifyApiKey(raw: string | null | undefined): Agent | null {
  if (!raw) return null;
  const store = loadStore();
  const hashed = hashKey(raw);
  return store.agents.find((a) => a.active && a.apiKeyHash === hashed) ?? null;
}

export function safeCompare(a: string, b: string): boolean {
  const ba = Buffer.from(a);
  const bb = Buffer.from(b);
  if (ba.length !== bb.length) return false;
  return timingSafeEqual(ba, bb);
}

export function newId(prefix: string): string {
  return `${prefix}_${randomBytes(6).toString("hex")}`;
}

export function createAgentApiKey(): string {
  return `clr_${randomBytes(18).toString("hex")}`;
}

export function hashApiKey(raw: string): string {
  return hashKey(raw);
}

export function previewApiKey(raw: string): string {
  return previewKey(raw);
}

export function canonicalJson(value: unknown): string {
  return JSON.stringify(value, Object.keys(value as object).sort());
}

export function signAuditRecord(
  record: Omit<AuditRecord, "sig">,
  prevSig: string,
): string {
  const payload = canonicalJson({ ...record, prevSig });
  return createHmac("sha256", getAuditSigningKey())
    .update(payload + prevSig)
    .digest("hex");
}

export function appendAudit(
  store: StoreShape,
  partial: Omit<AuditRecord, "id" | "sig" | "prevSig" | "ts">,
): AuditRecord {
  const prevSig = store.audit.at(-1)?.sig ?? "GENESIS";
  const base: Omit<AuditRecord, "sig"> = {
    id: newId("aud"),
    ts: new Date().toISOString(),
    prevSig,
    ...partial,
  };
  const record: AuditRecord = {
    ...base,
    sig: signAuditRecord(base, prevSig),
  };
  store.audit.push(record);
  return record;
}

export function verifyAuditChain(store: StoreShape): {
  intact: boolean;
  firstBadIndex: number | null;
} {
  let prev = "GENESIS";
  for (let i = 0; i < store.audit.length; i++) {
    const row = store.audit[i];
    if (row.prevSig !== prev) return { intact: false, firstBadIndex: i };
    const { sig, ...rest } = row;
    const expected = signAuditRecord(rest, prev);
    if (sig !== expected) return { intact: false, firstBadIndex: i };
    prev = sig;
  }
  return { intact: true, firstBadIndex: null };
}

export type {
  Agent,
  ApprovalItem,
  AuditRecord,
  ClearanceRequest,
  MemoryDoc,
  Org,
  PolicyPack,
  StoreShape,
  UsageEvent,
};
