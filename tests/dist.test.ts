import { expect, test, describe } from "bun:test";
import { manhattanDist, euclideanDist } from "../lib/mathlib";

// manhattanDist - taxicab geometry
describe("mathlib - manhattanDist", () => {
    test("distance between identical points is 0", () => {
        expect(manhattanDist(3n, 4n, 3n, 4n)).toBe(0n);
    });

    test("simple positive coordinates", () => {
        expect(manhattanDist(1n, 2n, 4n, 6n)).toBe(7n); // |1-4| + |2-6|
    });

    test("handles negatives correctly", () => {
        expect(manhattanDist(-5n, -5n, 5n, 5n)).toBe(20n);
    });
});

// euclideanDist - Pythagorean distance (floor)
describe("mathlib - euclideanDist", () => {
    test("(0,0) ↔ (3,4) gives 5", () => {
        expect(euclideanDist(0n, 0n, 3n, 4n)).toBe(5n);
    });

    test("identical points give 0", () => {
        expect(euclideanDist(-7n, 8n, -7n, 8n)).toBe(0n);
    });

    test("mixed signs, perfect square", () => {
        // Δx = 8, Δy = 6 ⇒ Δx² + Δy² = 100 ⇒ sqrt = 10
        expect(euclideanDist(-7n, 4n, 1n, -2n)).toBe(10n);
    });
});
