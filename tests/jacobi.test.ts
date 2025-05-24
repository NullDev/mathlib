import { expect, test, describe } from "bun:test";
import { jacobi } from "../lib/mathlib";

// jacobi - (a | n) for odd n ≥ 1
describe("mathlib - jacobi", () => {
    test("gcd(a,n) ≠ 1 yields 0", () => {
        // gcd(6, 9) = 3
        expect(jacobi(6n, 9n)).toBe(0n);
    });

    test("composite modulus examples", () => {
        // 21 = 3·7  → (5|21) = (5|3)(5|7) = (−1)(−1) = 1
        expect(jacobi(5n, 21n)).toBe(1n);

        // 15 = 3·5  → (2|15) = (2|3)(2|5) = (−1)(−1) = 1
        expect(jacobi(2n, 15n)).toBe(1n);
    });

    test("matches Legendre symbol for prime modulus", () => {
        // For prime 11: (7|11) = −1
        expect(jacobi(7n, 11n)).toBe(-1n);
    });

    test("throws when n is even or non-positive", () => {
        expect(() => jacobi(1n, 0n)).toThrow(RangeError);
        expect(() => jacobi(1n, 8n)).toThrow(RangeError);
    });
});
