import { expect, test, describe } from "bun:test";
import { extendedGCD } from "../lib/mathlib";

// extendedGCD - Bézout coefficients
describe("mathlib - extendedGCD", () => {
    test("gcd(240, 46) = 2 with correct Bézout identity", () => {
        const [g, x, y] = extendedGCD(240n, 46n);
        expect(g).toBe(2n);
        expect(240n * x + 46n * y).toBe(2n);
    });

    test("handles negative inputs (-25, 15)", () => {
        const [g, x, y] = extendedGCD(-25n, 15n);
        // gcd is always non-negative
        expect(g).toBe(5n);
        // Bézout identity
        expect((-25n) * x + 15n * y).toBe(5n);
    });

    test("coprime inputs give gcd 1", () => {
        const [g, x, y] = extendedGCD(17n, 31n);
        expect(g).toBe(1n);
        expect(17n * x + 31n * y).toBe(1n);
    });
});
