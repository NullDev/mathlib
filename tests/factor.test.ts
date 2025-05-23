import { expect, test, describe } from "bun:test";
import { factor } from "../lib/mathlib";

// factor - full prime factorisation
describe("mathlib - factor", () => {
    test("correctly factors a highly composite number", () => {
        // 2¹⁰·3⁴·5² = 2 073 600
        const n = 2n ** 10n * 3n ** 4n * 5n ** 2n;
        const expected = new Map<bigint, bigint>([
            [2n, 10n],
            [3n, 4n],
            [5n, 2n],
        ]);
        const result = factor(n);
        expect(Array.from(result.entries()).sort()).toEqual(
            Array.from(expected.entries()).sort(),
        );
    });

    test("factors a 64-bit semi-prime quickly", () => {
        // Two distinct 32-bit primes just below 2³²
        const p = 4_294_967_291n; // 2³² − 5  (prime)
        const q = 4_294_967_279n; // 2³² − 17 (prime)
        const n = p * q;          // ≈ 1.84 × 10¹⁹, still in 64-bit range

        const factors = factor(n);

        expect(factors.get(p)).toBe(1n);
        expect(factors.get(q)).toBe(1n);
        expect(factors.size).toBe(2);
    });

    test("factor(1) returns empty map", () => {
        expect(factor(1n)).toEqual(new Map());
    });
});
