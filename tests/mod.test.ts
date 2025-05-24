import { expect, test, describe } from "bun:test";
import { mod, modDiv, modInv, modPow, modSqrt, modNthRoot } from "../lib/mathlib";

// mod - true modulo for BigInt
describe("mathlib - mod", () => {
    test("works for negative dividend", () => {
        // -17 ≡ 3 (mod 5)
        expect(mod(-17n, 5n)).toBe(3n);
    });

    test("works when divisor is negative", () => {
        // 7 ≡ 2 (mod 5)
        expect(mod(7n, -5n)).toBe(2n);
    });

    test("throws when divisor is zero", () => {
        expect(() => mod(1n, 0n)).toThrow(RangeError);
    });
});

// modDiv - modular division
describe("mathlib - modDiv", () => {
    test("(10 / 4) mod 13 = 9", () => {
        expect(modDiv(10n, 4n, 13n)).toBe(9n);
    });

    test("handles negative divisor", () => {
        expect(modDiv(10n, -4n, 13n)).toBe(4n);
    });

    test("throws when divisor has no inverse modulo m", () => {
        // 6,9 not coprime
        expect(() => modDiv(5n, 6n, 9n)).toThrow(RangeError);
    });
});

// modInv - modular inverse
describe("mathlib - modInv", () => {
    test("finds inverse (3 mod 11 → 4)", () => {
        // 3·4 ≡ 1 (mod 11)
        expect(modInv(3n, 11n)).toBe(4n);
    });

    test("handles negative base (-3 mod 11 → 7)", () => {
        const inv = modInv(-3n, 11n);

        // -3·7 ≡ 1 (mod 11)
        expect(modInv(-3n, 11n)).toBe(7n);

        // verify that (-3 · inv) ≡ 1 (mod 11)
        expect(((-3n * inv) % 11n + 11n) % 11n).toBe(1n);

        // ensure the inverse is reported in the canonical range 0 … 10
        expect(inv >= 0n && inv < 11n).toBe(true);
    });

    test("throws when numbers are not coprime", () => {
        expect(() => modInv(6n, 9n)).toThrow(RangeError);
    });
});

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

// modSqrt - Tonelli–Shanks modular square root
describe("mathlib - modSqrt", () => {
    test("returns 0 when a ≡ 0 (mod p)", () => {
        expect(modSqrt(0n, 13n)).toBe(0n);
    });

    test("small prime 11: residue 9 → root 3 (least root)", () => {
        const p = 11n;
        // 3² ≡ 9 (mod 11)
        const a = 9n;
        const r = modSqrt(a, p);
        // expect non-null
        expect(r).not.toBeNull();
        // for the linter...
        if (!r) return;
        // least root
        expect(r).toBe(3n);
        expect((r * r) % p).toBe(a);
    });

    test("small prime 11: non-residue 2 returns null", () => {
        expect(modSqrt(2n, 11n)).toBeNull();
    });

    test("large 64-bit prime: a = 4 ⇒ root 2", () => {
        // 2⁶⁴ − 59 (prime)
        const p = 18_446_744_073_709_551_557n;
        const r = modSqrt(4n, p);
        // expect non-null
        expect(r).not.toBeNull();
        // for the linter...
        if (!r) return;
        // canonical least root
        expect(r).toBe(2n);
        // verify that r² ≡ 4 (mod p)
        expect((r * r) % p).toBe(4n);
    });

    test("throws if modulus is not an odd prime", () => {
        // composite
        expect(() => modSqrt(4n, 15n)).toThrow(RangeError);
        // even
        expect(() => modSqrt(5n, 8n)).toThrow(RangeError);
    });
});

// modNthRoot - Tonelli–Shanks nth root mod an odd prime p
describe("mathlib - modNthRoot", () => {
    test("k = 1 returns a mod p", () => {
        const p = 13n;
        const a = 10n;
        expect(modNthRoot(a, p, 1n)).toBe(a % p);
    });

    test("cube root exists: x³ ≡ 8 (mod 11) ⇒ x = 2", () => {
        const p = 11n;
        const k = 3n;
        // 2³ ≡ 8 (mod 11)
        const a = 8n;
        const r = modNthRoot(a, p, k);
        expect(r).not.toBeNull();
        // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
        expect(modPow(r!, k, p)).toBe(a); // verifies root
    });

    test("throws when gcd(k, p-1) ≠ 1 (k = 5, p = 11)", () => {
        // gcd(5, 10) = 5 – unsupported
        expect(() => modNthRoot(2n, 11n, 5n)).toThrow(RangeError);
    });
});
