import { expect, test, describe } from "bun:test";
import { totient } from "../lib/mathlib";

//  totient - Euler's φ(n)
describe("mathlib - totient", () => {
    test("φ(1) = 1 (definition edge-case)", () => {
        expect(totient(1n)).toBe(1n);
    });

    test("primes and prime powers", () => {
        // φ(p) = p - 1
        expect(totient(17n)).toBe(16n);
        // φ(2¹⁰) = 2⁹
        expect(totient(1024n)).toBe(512n);
    });

    test("composite with several prime factors (36 → 12)", () => {
        // 36 = 2²·3²  → 36·(1−1/2)·(1−1/3) = 12
        expect(totient(36n)).toBe(12n);
    });

    test("throws for n ≤ 0", () => {
        expect(() => totient(0n)).toThrow(RangeError);
        expect(() => totient(-5n)).toThrow(RangeError);
    });
});
