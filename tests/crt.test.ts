import { expect, test, describe } from "bun:test";
import { crt } from "../lib/mathlib";

/* eslint-disable @typescript-eslint/no-non-null-assertion */

// crt - Chinese Remainder Theorem solver
describe("mathlib - crt", () => {
    test("coprime moduli, unique solution", () => {
        // x ≡ 3 (mod 5) and x ≡ 4 (mod 7) → x = 18 (mod 35)
        const [x, M] = crt([3n, 4n], [5n, 7n])!;
        expect(M).toBe(35n);
        expect(x).toBe(18n);
        expect(x % 5n).toBe(3n);
        expect(x % 7n).toBe(4n);
    });

    test("non-coprime but consistent system", () => {
        // x ≡ 2 (mod 4) and x ≡ 4 (mod 6) → x = 10 (mod 12)
        const result = crt([2n, 4n], [4n, 6n]);
        expect(result).not.toBeNull();
        const [x, M] = result!;
        expect(M).toBe(12n);
        expect(x).toBe(10n);
        expect(x % 4n).toBe(2n);
        expect(x % 6n).toBe(4n);
    });

    test("inconsistent system returns null", () => {
        // x ≡ 1 (mod 2) vs x ≡ 2 (mod 4) → no solution
        expect(crt([1n, 2n], [2n, 4n])).toBeNull();
    });

    test("throws on invalid input length or modulus ≤ 0", () => {
        // zero length
        expect(() => crt([], [])).toThrow(RangeError);
        // unequal
        expect(() => crt([1n], [2n, 3n])).toThrow(RangeError);
        // non-positive modulus
        expect(() => crt([1n], [0n])).toThrow(RangeError);
    });
});
