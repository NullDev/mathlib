import { expect, test, describe } from "bun:test";
import { isPrime } from "../lib/mathlib";

// isPrime - Miller-Rabin primality test
describe("mathlib - isPrime", () => {
    test("isPrime - small primes", () => {
        const smallPrimes = [11n, 13n, 17n, 19n, 23n, 29n];
        for (const p of smallPrimes) {
            expect(isPrime(p)).toBe(true);
        }
    });

    test("isPrime - small composites", () => {
        const smallComposites = [4n, 6n, 8n, 9n, 10n, 12n];
        for (const c of smallComposites) {
            expect(isPrime(c)).toBe(false);
        }
    });

    test("isPrime - medium primes", () => {
        // 10 000th, 100 000th & 1 000 000th primes
        const mediumPrimes = [104_729n, 1_299_709n, 15_485_863n];
        for (const p of mediumPrimes) {
            expect(isPrime(p)).toBe(true);
        }
    });

    test("isPrime - medium composites", () => {
        const mediumComposites = [104_730n, 1_299_710n, 15_485_864n];
        for (const c of mediumComposites) {
            expect(isPrime(c)).toBe(false);
        }
    });

    test("isPrime - large primes", () => {
        const largePrimes = [
            // 2^61 − 1, Mersenne prime
            2_305_843_009_213_693_951n,
            // largest signed 64‑bit prime
            9_223_372_036_854_775_783n,
        ];
        for (const p of largePrimes) {
            expect(isPrime(p)).toBe(true);
        }
    });

    test("isPrime - large composites", () => {
        const largeComposites = [
            // 2^61 − 0, even
            2_305_843_009_213_693_952n,
            // 2^63
            9_223_372_036_854_775_808n,
        ];
        for (const c of largeComposites) {
            expect(isPrime(c)).toBe(false);
        }
    });

    test("isPrime - max 64-bit bigint prime", () => {
        // Largest unsigned 64‑bit prime
        const max64Prime = 18_446_744_073_709_551_557n;
        expect(isPrime(max64Prime)).toBe(true);
    });

    test("isPrime - max 64-bit bigint composite", () => {
        // 2^64 − 1 is composite (Fermat number F4)
        const max64Composite = 18_446_744_073_709_551_615n;
        expect(isPrime(max64Composite)).toBe(false);
    });

    test("isPrime - edge cases", () => {
        expect(isPrime(0n)).toBe(false);
        expect(isPrime(1n)).toBe(false);
        expect(isPrime(2n)).toBe(true);
        expect(isPrime(3n)).toBe(true);
        expect(isPrime(4n)).toBe(false);
        expect(isPrime(5n)).toBe(true);
        expect(isPrime(6n)).toBe(false);
        expect(isPrime(7n)).toBe(true);
        expect(isPrime(8n)).toBe(false);
        expect(isPrime(9n)).toBe(false);
    });
});
