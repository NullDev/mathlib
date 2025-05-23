import { expect, test, describe } from "bun:test";
import { pollardRho, isPrime } from "../lib/mathlib";

// pollardRho - non‑trivial factor finder
describe("mathlib - pollardRho", () => {
    test("returns a non-trivial factor for composite numbers", () => {
        // 5 959
        const n = 59n * 101n;
        const f = pollardRho(n);
        expect(f > 1n && f < n).toBe(true);
        expect(n % f).toBe(0n);
        expect(isPrime(f)).toBe(true);
    });

    test("returns n itself when n is prime", () => {
        // 10 000th prime
        const p = 104_729n;
        expect(pollardRho(p)).toBe(p);
    });
});
