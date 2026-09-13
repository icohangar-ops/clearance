"use client";

import { useRouter } from "next/navigation";
import { useState } from "react";
import { navigateToSafeCheckoutUrl } from "@/lib/safe-navigation";
import type { PlanId } from "@/lib/types";

export function BillingPanel({
  currentPlan,
  stripeMode,
}: {
  currentPlan: PlanId;
  stripeMode: string;
}) {
  const router = useRouter();
  const [message, setMessage] = useState<string | null>(null);
  const [busy, setBusy] = useState<string | null>(null);

  async function checkout(plan: PlanId) {
    setBusy(plan);
    setMessage(null);
    const res = await fetch("/api/stripe/checkout", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ plan }),
    });
    const json = await res.json();
    setBusy(null);
    if (json.url) {
      if (navigateToSafeCheckoutUrl(json.url)) return;
      setMessage("Checkout URL was rejected — expected an HTTPS Stripe Checkout link.");
      return;
    }
    setMessage(json.message || `Plan set to ${plan} (${json.mode})`);
    router.refresh();
  }

  return (
    <div className="grid gap-4">
      <p className="text-sm text-[var(--muted)]">
        Stripe mode: <span className="mono text-[var(--ink)]">{stripeMode}</span>
        {stripeMode === "demo"
          ? " — set STRIPE_SECRET_KEY for live Checkout."
          : null}
      </p>
      <div className="grid gap-4 md:grid-cols-3">
        {(
          [
            ["starter", "$49/mo", "3 agents · 2k clearances"],
            ["pro", "$199/mo", "25 agents · 25k clearances"],
            ["enterprise", "Custom", "SSO · audit API · private memory"],
          ] as const
        ).map(([plan, price, blurb]) => (
          <div key={plan} className="panel p-5">
            <div className="mb-3 flex items-center justify-between">
              <h3 className="display text-xl font-semibold capitalize">{plan}</h3>
              {currentPlan === plan ? (
                <span className="pill tone-ok">current</span>
              ) : null}
            </div>
            <p className="text-2xl font-semibold">{price}</p>
            <p className="mt-2 text-sm text-[var(--muted)]">{blurb}</p>
            <button
              className="btn btn-primary mt-5 w-full text-sm"
              disabled={busy === plan}
              onClick={() => checkout(plan)}
              type="button"
            >
              {busy === plan ? "Working…" : currentPlan === plan ? "Active" : "Choose plan"}
            </button>
          </div>
        ))}
      </div>
      {message ? <p className="text-sm tone-ok">{message}</p> : null}
    </div>
  );
}
