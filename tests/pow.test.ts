import { expect, test, describe } from "bun:test";
import { pow } from "../lib/mathlib";

// pow - integer exponentiation
describe("mathlib - pow", () => {
    test("2^10 = 1024", () => {
        expect(pow(2n, 10)).toBe(1024n);
    });

    test("any base ^0 = 1", () => {
        expect(pow(987654321n, 0)).toBe(1n);
    });

    test("3^20 = 3 486 784 401", () => {
        expect(pow(3n, 20)).toBe(3_486_784_401n);
    });
});
