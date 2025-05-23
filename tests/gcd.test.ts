import { expect, test, describe } from "bun:test";
import { gcd, gcdMulti } from "../lib/mathlib";

// gcd - Euclidean algorithm
describe("mathlib - gcd", () => {
    test("gcd - small numbers", () => {
        expect(gcd(12n, 18n)).toBe(6n);
        expect(gcd(48n, 180n)).toBe(12n);
        expect(gcd(101n, 103n)).toBe(1n);
    });

    test("gcd - medium numbers", () => {
        expect(gcd(123456n, 789012n)).toBe(12n);
        expect(gcd(65536n, 4294967296n)).toBe(65536n);
    });

    test("gcd - large numbers", () => {
        expect(gcd(2305843009213693952n, 9223372036854775808n)).toBe(2305843009213693952n);
        expect(gcd(18446744073709551615n, 9223372036854775807n)).toBe(1n);
    });
});

// gcdMulti - GCD of multiple numbers
describe("mathlib - gcdMulti", () => {
    test("gcdMulti - small numbers", () => {
        expect(gcdMulti(12n, 18n, 24n)).toBe(6n);
        expect(gcdMulti(48n, 180n, 36n)).toBe(12n);
        expect(gcdMulti(101n, 103n, 107n)).toBe(1n);
    });

    test("gcdMulti - medium numbers", () => {
        expect(gcdMulti(123456n, 789012n, 345678n)).toBe(6n);
        expect(gcdMulti(65536n, 4294967296n, 65536n)).toBe(65536n);
    });

    test("gcdMulti - large numbers", () => {
        expect(
            gcdMulti(
                2305843009213693952n,
                9223372036854775808n,
                18446744073709551615n,
            ),
        ).toBe(1n);
        expect(
            gcdMulti(
                18446744073709551615n,
                9223372036854775807n,
                2305843009213693952n,
            ),
        ).toBe(1n);
    });

    test("gcdMulti - edge cases", () => {
        expect(() => gcdMulti()).toThrow(TypeError);
        expect(gcdMulti(0n, 0n)).toBe(0n);
        expect(gcdMulti(0n, 1n)).toBe(1n);
        expect(gcdMulti(1n, 0n)).toBe(1n);
        expect(gcdMulti(1n, 1n)).toBe(1n);
    });
});
