import { expect, test, describe } from "bun:test";
import { bitLength, highestSetBit, randomBigInt } from "../lib/mathlib";

// bitLength - number of bits in a BigInt
describe("mathlib - bitLength", () => {
    test("bitLength(0) = 0", () => {
        expect(bitLength(0n)).toBe(0);
    });

    test("small numbers", () => {
        expect(bitLength(1n)).toBe(1); // 1      → 1 bit
        expect(bitLength(2n)).toBe(2); // 10     → 2 bits
        expect(bitLength(3n)).toBe(2); // 11     → 2 bits
        expect(bitLength(7n)).toBe(3); // 111    → 3 bits
    });

    test("large power-of-two boundary (2⁶³)", () => {
        const n = 1n << 63n;           // 2^63
        expect(bitLength(n)).toBe(64); // needs 64 bits (MSB position +1)
        expect(bitLength(n - 1n)).toBe(63); // one less → 63 bits
    });
});

// highestSetBit - position of MSB (1-based)
describe("mathlib - highestSetBit", () => {
    test("highest bit of 0 is 0", () => {
        expect(highestSetBit(0n)).toBe(0n);
    });

    test("highest bit of 13 (1101₂) is 4", () => {
        expect(highestSetBit(13n)).toBe(4n);
    });

    test("highest bit of 2⁶³ is 64", () => {
        expect(highestSetBit(1n << 63n)).toBe(64n);
    });
});

// randomBigInt - cryptographically‑strong random BigInt
describe("mathlib - randomBigInt", () => {
    test("throws RangeError when max < min", () => {
        expect(() => randomBigInt(10n, 5n)).toThrow(RangeError);
    });

    test("degenerate range (min == max) returns that value", () => {
        expect(randomBigInt(42n, 42n)).toBe(42n);
    });

    test("result is always inside [min, max]", () => {
        const min = 1_000_000n;
        const max = 1_000_050n;
        for (let i = 0; i < 1_000; i++) {
            const v = randomBigInt(min, max);
            expect(v >= min && v <= max).toBe(true);
        }
    });

    test("uses crypto.getRandomValues when available", () => {
        const originalCrypto = globalThis.crypto;
        let called = false;

        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        const stubCrypto: any = {
            getRandomValues: (arr: Uint8Array) => {
                called = true;
                for (let i = 0; i < arr.length; i++) arr[i] = i % 2 === 0 ? 0x12 : 0x34;
                return arr;
            },
        };
        globalThis.crypto = stubCrypto;

        const min = 0n;
        // 32 767 → range 32 768 → 2 bytes
        const max = 0x7FFFn;
        const result = randomBigInt(min, max);
        expect(called).toBe(true);
        expect(result).toBe(0x1234n);

        globalThis.crypto = originalCrypto;
    });

    test("falls back to Math.random when crypto is missing", () => {
        const savedCrypto = globalThis.crypto;
        // Remove crypto to force fallback
        // @ts-ignore
        delete globalThis.crypto;

        const savedRandom = Math.random;
        // Always zero, so rnd → 0 ⇒ result == min
        Math.random = (): number => 0;

        const min = 50n;
        const max = 100n;
        expect(randomBigInt(min, max)).toBe(min);

        // restore
        Math.random = savedRandom;
        globalThis.crypto = savedCrypto;
    });
});
