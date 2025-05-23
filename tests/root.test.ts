import { expect, test, describe } from "bun:test";
import { nthRoot, sqrt, pow } from "../lib/mathlib";

// nthRoot - integer floor n-th root
describe("mathlib - nthRoot", () => {
    test("cube root of 27 = 3", () => {
        expect(nthRoot(27n, 3)).toBe(3n);
    });

    test("100-th root of 2¹⁰⁰ = 2", () => {
        const big = pow(2n, 100); // 2¹⁰⁰
        expect(nthRoot(big, 100)).toBe(2n);
    });

    test("even root of negative throws", () => {
        expect(() => nthRoot(-8n, 2)).toThrow(RangeError);
    });

    test("odd root of a negative returns the negative root", () => {
        expect(nthRoot(-27n, 3)).toBe(-3n);
    });
});

// sqrt - shortcut for nthRoot(·, 2)
describe("mathlib - sqrt", () => {
    test("sqrt(144) = 12", () => {
        expect(sqrt(144n)).toBe(12n);
    });

    test("floor behaviour: sqrt(2) = 1", () => {
        expect(sqrt(2n)).toBe(1n);
    });

    test("sqrt(0) = 0", () => {
        expect(sqrt(0n)).toBe(0n);
    });
});
