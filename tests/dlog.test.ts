import { expect, test, describe } from "bun:test";
import { discreteLog, modPow } from "../lib/mathlib";

describe("mathlib - discreteLog", () => {
    test("finds x for small subgroup (p=23, order=11)", () => {
        const p = 23n;
        const order = 11n;
        const g = 2n; // order 11 modulo 23
        const x = 7n;
        const h = modPow(g, x, p);
        const result = discreteLog(g, h, p, order);
        expect(result).toBe(x);
    });

    test("returns 0 when h = 1 (identity)", () => {
        const p = 23n;
        const order = 11n;
        const g = 2n;
        expect(discreteLog(g, 1n, p, order)).toBe(0n);
    });

    test("returns null when no solution exists", () => {
        const p = 23n;
        const order = 11n;
        const g = 2n; // subgroup of size 11
        const h = 5n; // not in subgroup (5^11 mod 23 != 1)
        expect(discreteLog(g, h, p, order)).toBeNull();
    });
});
