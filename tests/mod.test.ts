import { expect, test, describe } from "bun:test";
import { mod } from "../lib/mathlib";

// mod - true modulo for BigInt
describe("mathlib - mod", () => {
    test("works for negative dividend", () => {
        // -17 ≡ 3 (mod 5)
        expect(mod(-17n, 5n)).toBe(3n);
    });

    test("works when divisor is negative", () => {
        // 7 ≡ 2 (mod 5)
        expect(mod(7n, -5n)).toBe(2n);
    });

    test("throws when divisor is zero", () => {
        expect(() => mod(1n, 0n)).toThrow(RangeError);
    });
});
