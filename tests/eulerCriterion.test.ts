import { expect, test, describe } from "bun:test";
import { eulerCriterion } from "../lib/mathlib";

// eulerCriterion - quadratic residue test
describe("mathlib - eulerCriterion", () => {
    test("returns 1 for a quadratic residue (a = 2 mod 7)", () => {
        expect(eulerCriterion(2n, 7n)).toBe(1n);
    });

    test("returns -1 for a non-residue (a = 3 mod 7)", () => {
        expect(eulerCriterion(3n, 7n)).toBe(-1n);
    });

    test("returns 0 when a ≡ 0 (mod p)", () => {
        expect(eulerCriterion(0n, 13n)).toBe(0n);
    });
});
