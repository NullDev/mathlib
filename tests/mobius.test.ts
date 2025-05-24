import { expect, test, describe } from "bun:test";
import { mobius } from "../lib/mathlib";

// mobius - Möbius function μ(n) for positive integer n ≥ 1
describe("mathlib - mobius", () => {
    test("μ(1) = 1 (definition)", () => {
        expect(mobius(1n)).toBe(1n);
    });

    test("square-free products: 6 → +1, 30 → -1", () => {
        // 6 = 2·3  (k = 2 even)
        expect(mobius(6n)).toBe(1n);

        // 30 = 2·3·5  (k = 3 odd)
        expect(mobius(30n)).toBe(-1n);
    });

    test("non-square-free number returns 0 (12 = 2²·3)", () => {
        expect(mobius(12n)).toBe(0n);
    });

    test("throws for n ≤ 0", () => {
        expect(() => mobius(0n)).toThrow(RangeError);
        expect(() => mobius(-7n)).toThrow(RangeError);
    });
});
