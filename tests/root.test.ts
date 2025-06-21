import { expect, test, describe } from "bun:test";
import { nthRoot, sqrt, pow, primitiveRoot, modPow } from "../lib/mathlib";

// nthRoot - integer floor n-th root
describe("mathlib - nthRoot", () => {
    test("cube root of 27 = 3", () => {
        expect(nthRoot(27n, 3)).toBe(3n);
    });

    test("100-th root of 2¹⁰⁰ = 2", () => {
        const big = pow(2n, 100); // 2¹⁰⁰
        expect(nthRoot(big, 100)).toBe(2n);
    });

    test("even root of negative throws", () => {
        expect(() => nthRoot(-8n, 2)).toThrow(RangeError);
    });

    test("odd root of a negative returns the negative root", () => {
        expect(nthRoot(-27n, 3)).toBe(-3n);
    });
});

// sqrt - shortcut for nthRoot(·, 2)
describe("mathlib - sqrt", () => {
    test("sqrt(144) = 12", () => {
        expect(sqrt(144n)).toBe(12n);
    });

    test("floor behaviour: sqrt(2) = 1", () => {
        expect(sqrt(2n)).toBe(1n);
    });

    test("sqrt(0) = 0", () => {
        expect(sqrt(0n)).toBe(0n);
    });
});

// primitiveRoot - find a primitive root modulo p
describe("mathlib - primitiveRoot", () => {
    // helper: true iff g generates ℤ_p×
    const isGenerator = (g: bigint, p: bigint): boolean => {
        const residues = new Set<bigint>();
        for (let k = 0n; k < p - 1n; k++) {
            residues.add(modPow(g, k, p));
        }
        return residues.size === Number(p - 1n);
    };

    test("special case p = 2 → 1", () => {
        expect(primitiveRoot(2n)).toBe(1n);
    });

    const primes = [3n, 5n, 11n, 23n];
    for (const p of primes) {
        test(`generator property for p = ${p}`, () => {
            const g = primitiveRoot(p);
            expect(modPow(g, p - 1n, p)).toBe(1n); // g^{p-1} ≡ 1 (mod p)
            expect(isGenerator(g, p)).toBe(true);  // hits every non-zero residue
        });
    }

    test("non-prime modulus throws", () => {
        expect(() => primitiveRoot(15n)).toThrow(RangeError);
        expect(() => primitiveRoot(8n)).toThrow(RangeError);
    });
});
