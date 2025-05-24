import { expect, test, describe } from "bun:test";
import { fibPair, fib } from "../lib/mathlib";

// fibPair - fast-doubling Fibonacci (mod m)
describe("mathlib - fibPair", () => {
    test("F₁₀ and F₁₁ mod 1000", () => {
        const [f10, f11] = fibPair(10n, 1000n);
        expect(f10).toBe(55n); // F₁₀
        expect(f11).toBe(89n); // F₁₁
    });

    test("F₀ pair modulo arbitrary m (sanity/edge case)", () => {
        const [f0, f1] = fibPair(0n, 987_654_321n);
        expect(f0).toBe(0n); // F₀
        expect(f1).toBe(1n); // F₁
    });

    test("large n = 50 modulo 1 000 000 007", () => {
        const [f50, f51] = fibPair(50n, 1_000_000_007n);
        expect(f50).toBe(586_268_941n); // pre-computed F₅₀ mod 1e9+7
        expect(f51).toBe(365_010_934n); // F₅₁ mod 1e9+7
    });

    test("modulus 1 always returns (0, 0)", () => {
        const [f, fNext] = fibPair(123_456_789n, 1n);
        expect(f).toBe(0n);
        expect(fNext).toBe(0n);
    });
});

// fib - Fibonacci number Fₙ for any integer n
describe("mathlib - fib", () => {
    test("negative n uses F₋ₙ = (-1)^{n+1}·Fₙ", () => {
        // Even n → sign +1,  F₋₈ = 21
        expect(fib(-8n)).toBe(21n);
        // Odd  n → sign −1,  F₋₉ = −34
        expect(fib(-9n)).toBe(-34n);
    });

    test("handles n = 0 and n = 1", () => {
        expect(fib(0n)).toBe(0n);
        expect(fib(1n)).toBe(1n);
    });

    test("small positive n: fib(2) = 1", () => {
        expect(fib(2n)).toBe(1n);
    });

    test("moderately large n: fib(100)", () => {
        // F₁₀₀ = 354224848179261915075
        expect(fib(100n)).toBe(354_224_848_179_261_915_075n);
    });
});
