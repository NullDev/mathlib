import { expect, test, describe } from "bun:test";
import { modPow } from "../lib/mathlib";

// modPow - Modular exponentiation
describe("mathlib - modPow", () => {
    test("modPow - small numbers", () => {
        // 2^10 ≡ 24 (mod 1000)
        expect(modPow(2n, 10n, 1000n)).toBe(24n);
        // 27 ≡ 6 (mod 7)
        expect(modPow(3n, 3n, 7n)).toBe(6n);
        // x^0 ≡ 1 (mod m)
        expect(modPow(10n, 0n, 13n)).toBe(1n);
    });

    test("modPow - medium numbers", () => {
        expect(modPow(123456789n, 12345n, 1000000007n)).toBe(614455772n);
        expect(modPow(987654321n, 123456n, 4294967291n)).toBe(3452667444n);
    });

    test("modPow - large numbers", () => {
        expect(
            modPow(
                18446744073709551557n,
                9223372036854775783n,
                2305843009213693951n,
            ),
        ).toBe(622515688022284824n);
    });
});
