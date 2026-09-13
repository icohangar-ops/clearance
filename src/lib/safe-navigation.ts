const ALLOWED_CHECKOUT_HOSTS = new Set([
  "checkout.stripe.com",
  "billing.stripe.com",
]);

const MAX_CHECKOUT_URL_LENGTH = 2048;

/**
 * Accept only HTTPS Stripe Checkout / Billing Portal URLs.
 * Reconstructs the URL from parsed parts so callers never assign the
 * original untrusted string to location.href (Aikido / DOM XSS).
 */
export function toSafeCheckoutUrl(raw: unknown): string | null {
  if (typeof raw !== "string") return null;

  const candidate = raw.trim();
  if (!candidate || candidate.length > MAX_CHECKOUT_URL_LENGTH) return null;

  let parsed: URL;
  try {
    parsed = new URL(candidate);
  } catch {
    return null;
  }

  if (parsed.protocol !== "https:") return null;
  if (parsed.username || parsed.password) return null;
  if (parsed.port) return null;
  if (!ALLOWED_CHECKOUT_HOSTS.has(parsed.hostname)) return null;

  const safe = new URL("https://checkout.stripe.com/");
  safe.hostname = parsed.hostname;
  safe.pathname = parsed.pathname;
  safe.search = parsed.search;
  return safe.href;
}

export function navigateToSafeCheckoutUrl(raw: unknown): boolean {
  const safeUrl = toSafeCheckoutUrl(raw);
  if (!safeUrl) return false;
  window.location.assign(safeUrl);
  return true;
}
