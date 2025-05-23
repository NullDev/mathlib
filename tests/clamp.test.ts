import { expect, test, describe } from "bun:test";
import { clamp } from "../lib/mathlib";

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
