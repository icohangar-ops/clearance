/**
 * Headless demo recorder for Clearance (Galuxium Nexus V2).
 * Usage: BASE_URL=https://... bun run scripts/record-demo.mjs
 */
import { chromium } from "playwright";
import { mkdirSync, existsSync } from "fs";
import path from "path";
import { spawnSync } from "child_process";

const BASE = process.env.BASE_URL || "http://localhost:3000";
const OUT_DIR = path.join(process.cwd(), "docs", "demo");
const RAW_DIR = path.join(OUT_DIR, "raw");

mkdirSync(RAW_DIR, { recursive: true });

function sleep(ms) {
  return new Promise((r) => setTimeout(r, ms));
}

async function narrate(page, text, holdMs = 3200) {
  // On-screen caption bar for the recording
  await page.evaluate((t) => {
    let el = document.getElementById("demo-caption");
    if (!el) {
      el = document.createElement("div");
      el.id = "demo-caption";
      el.style.cssText =
        "position:fixed;left:24px;right:24px;bottom:24px;z-index:99999;padding:14px 18px;border-radius:14px;background:rgba(11,16,20,0.92);border:1px solid rgba(232,238,243,0.18);color:#e8eef3;font:600 16px/1.4 Manrope,system-ui,sans-serif;box-shadow:0 12px 40px rgba(0,0,0,0.35)";
      document.body.appendChild(el);
    }
    el.textContent = t;
  }, text);
  // Optional local voiceover track via macOS say
  if (process.env.SKIP_SAY !== "1") {
    spawnSync("say", ["-r", "170", text], { stdio: "ignore" });
  }
  await sleep(holdMs);
}

async function main() {
  const browser = await chromium.launch({ headless: true });
  const context = await browser.newContext({
    viewport: { width: 1440, height: 900 },
    recordVideo: { dir: RAW_DIR, size: { width: 1440, height: 900 } },
  });
  const page = await context.newPage();

  await page.goto(BASE, { waitUntil: "networkidle" });
  await narrate(
    page,
    "Clearance — the approval, spend-control, and billing layer for production AI agents.",
    4500,
  );
  await narrate(
    page,
    "Built for Galuxium Nexus V2: a live SaaS with policy gates, CHP governance, Stripe billing hooks, and a signed audit ledger.",
    5000,
  );

  await page.goto(`${BASE}/dashboard`, { waitUntil: "networkidle" });
  await narrate(
    page,
    "Open the control plane. Agents, spend caps, and the live clearance gate are ready with zero credentials.",
    4500,
  );
  await narrate(
    page,
    "Finance can finally see which agent spent what, under which policy, with evidence.",
    4000,
  );

  // Auto-approve path
  await page.selectOption("select", { label: "Research Scout" }).catch(() => {});
  const selects = page.locator("select");
  if ((await selects.count()) >= 2) {
    await selects.nth(0).selectOption({ index: 0 });
    await selects.nth(1).selectOption("research.query");
  }
  await page.locator('input[placeholder="stripe.com"]').fill("sec.gov");
  await page.locator('input[placeholder="250.00"]').fill("12.00");
  await narrate(page, "First, a routine research query under the auto-approve threshold.", 3500);
  await page.getByRole("button", { name: "Run clearance" }).click();
  await sleep(1500);
  await narrate(page, "CHP locks automatically. Status approved. Audit signature appended.", 4000);

  // Human escalate
  if ((await selects.count()) >= 2) {
    await selects.nth(0).selectOption({ label: "PayOps Runner" }).catch(async () => {
      await selects.nth(0).selectOption({ index: 1 });
    });
    await selects.nth(1).selectOption("payment.transfer");
  }
  await page.locator('input[placeholder="stripe.com"]').fill("stripe.com");
  await page.locator('input[placeholder="250.00"]').fill("600.00");
  await narrate(
    page,
    "Now a six-hundred dollar payment. That exceeds policy, so Clearance escalates to a human.",
    4500,
  );
  await page.getByRole("button", { name: "Run clearance" }).click();
  await sleep(1500);

  await page.goto(`${BASE}/approvals`, { waitUntil: "networkidle" });
  await narrate(page, "The approval queue shows the pending CHP review.", 3500);
  const approve = page.getByRole("button", { name: "Lock approve" }).first();
  if (await approve.count()) {
    await approve.click();
    await sleep(1200);
    await narrate(page, "Human validator locks the clearance. Spend is metered.", 4000);
  }

  // Deny blocked vendor
  await page.goto(`${BASE}/dashboard`, { waitUntil: "networkidle" });
  const selects2 = page.locator("select");
  if ((await selects2.count()) >= 2) {
    await selects2.nth(0).selectOption({ index: 1 });
    await selects2.nth(1).selectOption("payment.transfer");
  }
  await page.locator('input[placeholder="stripe.com"]').fill("darkweb-market");
  await page.locator('input[placeholder="250.00"]').fill("10.00");
  await narrate(page, "Blocked vendor on the policy pack — Clearance denies hard.", 4000);
  await page.getByRole("button", { name: "Run clearance" }).click();
  await sleep(1500);

  await page.goto(`${BASE}/audit`, { waitUntil: "networkidle" });
  await narrate(
    page,
    "Every decision lands in a signature-chained HMAC audit ledger. Finance can export JSONL.",
    4500,
  );

  await page.goto(`${BASE}/spend`, { waitUntil: "networkidle" });
  await narrate(page, "Spend and metering update per agent against live caps.", 4000);

  await page.goto(`${BASE}/agents`, { waitUntil: "networkidle" });
  await narrate(
    page,
    "Each agent has risk tiers, allowlists, memory namespaces, and hashed API keys.",
    4200,
  );

  await page.goto(`${BASE}/billing`, { waitUntil: "networkidle" });
  await narrate(
    page,
    "Billing is wired for Stripe Checkout — Starter, Pro, and Enterprise. Demo mode works without keys.",
    4800,
  );

  await page.goto(BASE, { waitUntil: "networkidle" });
  await narrate(
    page,
    "Clearance. Production governance for AI agents — live at clearance-sand.vercel.app. Built for Galuxium Nexus V2.",
    5500,
  );

  const videoPath = await page.video().path();
  await context.close();
  await browser.close();

  const outMp4 = path.join(OUT_DIR, "clearance-demo.mp4");
  // Normalize to H.264 mp4 for Devpost / YouTube upload
  const ff = spawnSync(
    "ffmpeg",
    [
      "-y",
      "-i",
      videoPath,
      "-vf",
      "scale=1440:900",
      "-c:v",
      "libx264",
      "-pix_fmt",
      "yuv420p",
      "-movflags",
      "+faststart",
      "-an",
      outMp4,
    ],
    { encoding: "utf8" },
  );
  if (ff.status !== 0) {
    console.error(ff.stderr);
    throw new Error("ffmpeg failed");
  }
  console.log(JSON.stringify({ base: BASE, video: outMp4, raw: videoPath }, null, 2));
  if (!existsSync(outMp4)) throw new Error("missing output");
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
