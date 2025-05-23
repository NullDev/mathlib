import { expect, test, describe } from "bun:test";
import { abs } from "../lib/mathlib";

// abs - absolute value for BigInt
describe("mathlib - abs", () => {
    test("positive number is unchanged", () => {
        expect(abs(123n)).toBe(123n);
    });

    test("negative number becomes positive", () => {
        expect(abs(-987654321n)).toBe(987654321n);
    });

    test("zero stays zero", () => {
        expect(abs(0n)).toBe(0n);
    });
});
