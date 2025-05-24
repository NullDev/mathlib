import { expect, test, describe } from "bun:test";
import { abs, clamp, floorLog2 } from "../lib/mathlib";

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

// clamp - Clamp a number between min and max
describe("mathlib - clamp", () => {
    test("clamp - small numbers", () => {
        expect(clamp(5n, 1n, 10n)).toBe(5n);
        expect(clamp(0n, 1n, 10n)).toBe(1n);
        expect(clamp(15n, 1n, 10n)).toBe(10n);
    });

    test("clamp - negative numbers", () => {
        expect(clamp(-5n, -10n, -1n)).toBe(-5n);
        expect(clamp(-15n, -10n, -1n)).toBe(-10n);
        expect(clamp(-5n, -20n, -10n)).toBe(-10n);
    });

    test("clamp - large numbers", () => {
        expect(clamp(
            1_234_567_890_123_456_789n, 1_000_000_000_000_000_000n, 2_000_000_000_000_000_000n,
        )).toBe(1_234_567_890_123_456_789n);
        expect(clamp(
            5_000_000_000_000_000_000n, 1_000_000_000_000_000_000n, 2_000_000_000_000_000_000n,
        )).toBe(2_000_000_000_000_000_000n);
    });
});

// floorLog2 - Calculate the floor of the base-2 logarithm of a number
describe("mathlib - floorLog2", () => {
    test("floorLog2 - small numbers", () => {
        expect(floorLog2(1)).toBe(0);
        expect(floorLog2(2)).toBe(1);
        expect(floorLog2(3)).toBe(1);
    });

    test("floorLog2 - large numbers", () => {
        expect(floorLog2(1024)).toBe(10);
        expect(floorLog2(1025)).toBe(10);
    });
});
