import { expect, test, describe } from "bun:test";
import { modInv } from "../lib/mathlib";

// modInv - modular inverse
describe("mathlib - modInv", () => {
    test("finds inverse (3 mod 11 → 4)", () => {
        // 3·4 ≡ 1 (mod 11)
        expect(modInv(3n, 11n)).toBe(4n);
    });

    test("handles negative base (-3 mod 11 → 7)", () => {
        const inv = modInv(-3n, 11n);

        // -3·7 ≡ 1 (mod 11)
        expect(modInv(-3n, 11n)).toBe(7n);

        // verify that (-3 · inv) ≡ 1 (mod 11)
        expect(((-3n * inv) % 11n + 11n) % 11n).toBe(1n);

        // ensure the inverse is reported in the canonical range 0 … 10
        expect(inv >= 0n && inv < 11n).toBe(true);
    });

    test("throws when numbers are not coprime", () => {
        expect(() => modInv(6n, 9n)).toThrow(RangeError);
    });
});
