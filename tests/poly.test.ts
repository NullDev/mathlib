import { expect, test, describe } from "bun:test";
import { quadraticPoly, mod } from "../lib/mathlib";

// quadraticPoly - f(x) = x² + c (mod n)
describe("mathlib - quadraticPoly", () => {
    test("simple case: x=3, c=1, n=10  ⇒  (3²+1) mod 10 = 0", () => {
        expect(quadraticPoly(3n, 1n, 10n)).toBe(0n);
    });

    test("handles negatives via true modulo", () => {
        // (−4)² + (−3) = 16 − 3 = 13; 13 mod 10 = 3
        expect(quadraticPoly(-4n, -3n, 10n)).toBe(3n);
    });

    test("large inputs still correct", () => {
        const x = 9_223_372_036_854_775_807n;  // 2⁶³−1
        const c = 1_234_567_890_123_456_789n;
        const n = 18_446_744_073_709_551_557n; // 2⁶⁴−59 (prime)

        const expected = mod(x * x + c, n); // reference using existing mod()
        expect(quadraticPoly(x, c, n)).toBe(expected);
    });
});
