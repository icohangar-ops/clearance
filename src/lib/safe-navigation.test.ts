import assert from "node:assert/strict";
import { describe, it } from "node:test";
import { toSafeCheckoutUrl } from "./safe-navigation.ts";

describe("toSafeCheckoutUrl", () => {
  it("allows reconstructed Stripe Checkout HTTPS URLs", () => {
    const input = "https://checkout.stripe.com/c/pay/cs_test_a1b2?prefilled_email=ops%40acme.example";
    assert.equal(toSafeCheckoutUrl(input), input);
  });

  it("allows Stripe Billing Portal hosts", () => {
    assert.equal(
      toSafeCheckoutUrl("https://billing.stripe.com/p/session/test_123"),
      "https://billing.stripe.com/p/session/test_123",
    );
  });

  it("rejects javascript and data URLs", () => {
    assert.equal(toSafeCheckoutUrl("javascript:alert(1)"), null);
    assert.equal(toSafeCheckoutUrl("data:text/html,<script>alert(1)</script>"), null);
  });

  it("rejects http, credentials, ports, and off-allowlist hosts", () => {
    assert.equal(toSafeCheckoutUrl("http://checkout.stripe.com/c/pay/cs_test"), null);
    assert.equal(toSafeCheckoutUrl("https://evil.example/checkout.stripe.com"), null);
    assert.equal(toSafeCheckoutUrl("https://checkout.stripe.com.evil.example/pay"), null);
    assert.equal(toSafeCheckoutUrl("https://user:pass@checkout.stripe.com/pay"), null);
    assert.equal(toSafeCheckoutUrl("https://checkout.stripe.com:4443/pay"), null);
    assert.equal(toSafeCheckoutUrl("//checkout.stripe.com/pay"), null);
    assert.equal(toSafeCheckoutUrl("/billing?success=1"), null);
  });

  it("rejects non-strings, blanks, and oversized values", () => {
    assert.equal(toSafeCheckoutUrl(undefined), null);
    assert.equal(toSafeCheckoutUrl({ url: "https://checkout.stripe.com/pay" }), null);
    assert.equal(toSafeCheckoutUrl("   "), null);
    assert.equal(toSafeCheckoutUrl(`https://checkout.stripe.com/${"a".repeat(3000)}`), null);
  });
});
