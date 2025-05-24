import { expect, test, describe } from "bun:test";
import { factorial } from "../lib/mathlib";

// factorial - exact factorial n! of a number for bigint n ≥ 0
describe("mathlib - factorial", () => {
    test("0! and 1! both equal 1", () => {
        expect(factorial(0n)).toBe(1n);
        expect(factorial(1n)).toBe(1n);
    });

    test("small values: 5! = 120", () => {
        expect(factorial(5n)).toBe(120n);
    });

    test("moderate value: 20! = 2 432 902 008 176 640 000", () => {
        expect(factorial(20n)).toBe(2_432_902_008_176_640_000n);
    });

    test("large value: 100! = 93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864000000000000000000000000", () => {
        expect(factorial(100n)).toBe(
            93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864000000000000000000000000n,
        );
        // honestly, I'm surprised as well that this works.
    });

    test("throws on negative input", () => {
        expect(() => factorial(-1n)).toThrow(RangeError);
    });

    test("throws when n exceeds 4 294 967 296", () => {
        expect(() => factorial(4_294_967_297n)).toThrow(RangeError);
    });
});
