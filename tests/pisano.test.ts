import { expect, test, describe } from "bun:test";
import { pisanoPeriod, primePisano } from "../lib/mathlib";

// primePisano - Pisano period π(p) for prime p
describe("mathlib - primePisano", () => {
    test("π(7) = 16", () => {
        expect(primePisano(7n)).toBe(16n);
    });

    test("special-case prime 5 ⇒ π(5) = 20", () => {
        expect(primePisano(5n)).toBe(20n);
    });

    test("π(11) = 10", () => {
        expect(primePisano(11n)).toBe(10n);
    });

    test("throws for non-prime input (15)", () => {
        expect(() => primePisano(15n)).toThrow();
    });
});

// pisanoPeriod - general π(n) for composite n
describe("mathlib - pisanoPeriod", () => {
    test("π(10) = 60", () => {
        expect(pisanoPeriod(10n)).toBe(60n);
    });

    test("π(8) = 12", () => {
        expect(pisanoPeriod(8n)).toBe(12n);
    });

    test("π(12) = 24", () => {
        expect(pisanoPeriod(12n)).toBe(24n);
    });

    test("π(1) = 1 (identity case)", () => {
        expect(pisanoPeriod(1n)).toBe(1n);
    });
});
