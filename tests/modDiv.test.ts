import { expect, test, describe } from "bun:test";
import { modDiv } from "../lib/mathlib";

// modDiv - modular division
describe("mathlib - modDiv", () => {
    test("(10 / 4) mod 13 = 9", () => {
        expect(modDiv(10n, 4n, 13n)).toBe(9n);
    });

    test("handles negative divisor", () => {
        expect(modDiv(10n, -4n, 13n)).toBe(4n);
    });

    test("throws when divisor has no inverse modulo m", () => {
        // 6,9 not coprime
        expect(() => modDiv(5n, 6n, 9n)).toThrow(RangeError);
    });
});
