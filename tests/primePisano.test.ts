import { expect, test, describe } from "bun:test";
import { primePisano } from "../lib/mathlib";

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
