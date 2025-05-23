import { expect, test, describe } from "bun:test";
import { lcm, lcmMulti } from "../lib/mathlib";

// lcm - Least common multiple
describe("mathlib - lcm", () => {
    test("lcm - small numbers", () => {
        expect(lcm(4n, 6n)).toBe(12n);
        expect(lcm(21n, 6n)).toBe(42n);
        expect(lcm(13n, 17n)).toBe(221n);
    });

    test("lcm - medium numbers", () => {
        expect(lcm(123456n, 789012n)).toBe(8117355456n);
        expect(lcm(65536n, 4294967296n)).toBe(4294967296n);
    });

    test("lcm - large numbers", () => {
        expect(lcm(2305843009213693952n, 9223372036854775808n)).toBe(9223372036854775808n);
        // lcm of two coprime 64‑bit numbers is their product, verified ahead of time.
        expect(lcm(9223372036854775783n, 18446744073709551557n)).toBe(170141183460469230726339751698713544131n);
    });
});

// lcmMulti - LCM of multiple numbers
describe("mathlib - lcmMulti", () => {
    test("lcmMulti - small numbers", () => {
        expect(lcmMulti(4n, 6n, 8n)).toBe(24n);
        expect(lcmMulti(21n, 6n, 14n)).toBe(42n);
        expect(lcmMulti(13n, 17n, 19n)).toBe(4199n);
    });

    test("lcmMulti - medium numbers", () => {
        expect(lcmMulti(123456n, 789012n, 345678n)).toBe(467665199886528n);
        expect(lcmMulti(65536n, 4294967296n, 65536n)).toBe(4294967296n);
    });

    test("lcmMulti - large numbers", () => {
        expect(
            lcmMulti(
                2305843009213693952n,
                9223372036854775808n,
                18446744073709551615n,
            ),
        ).toBe(170141183460469231722463931679029329920n);
        expect(
            lcmMulti(
                9223372036854775783n,
                18446744073709551557n,
                2305843009213693952n,
            ),
        ).toBe(392318858461667545421563214301585872063276140740279795712n);
    });

    test("lcmMulti - edge cases", () => {
        expect(() => lcmMulti()).toThrow(TypeError);
        expect(lcmMulti(0n, 0n)).toBe(0n);
        expect(lcmMulti(0n, 1n)).toBe(0n);
        expect(lcmMulti(1n, 0n)).toBe(0n);
        expect(lcmMulti(1n, 1n)).toBe(1n);
    });
});
