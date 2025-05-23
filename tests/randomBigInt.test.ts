import { expect, test, describe } from "bun:test";
import { randomBigInt } from "../lib/mathlib";

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
