/**
 * MathLib - A zero-dependency collection of advanced mathematical functions using BigInts.
 *
 * Functions are in no particular order, unless they depend on each other.
 * Functions are optimized for performance and accuracy, and are safe for large numbers.
 *
 * Copyright (c) 2025, NullDev
 */

/* eslint-disable no-param-reassign */

/**
 * Calculate the absolute value of a BigInt.
 *
 * @param {bigint} n - The number to calculate the absolute value for.
 * @return {bigint} The absolute value of the number.
 */
export const abs = (n: bigint): bigint => n < 0n ? -n : n;

/**
 * Clamp a number to a given range.
 *
 * @param {bigint} n - The number to clamp.
 * @param {bigint} min - The minimum value (inclusive).
 * @param {bigint} max - The maximum value (inclusive).
 * @return {bigint} The clamped value.
 * @throws {RangeError} If min is greater than max.
 */
export const clamp = function(n: bigint, min: bigint, max: bigint): bigint {
    if (min > max) throw new RangeError("clamp(): min must be ≤ max");
    // eslint-disable-next-line no-nested-ternary
    return n < min ? min : n > max ? max : n;
};

/**
 * Calculate the greatest common divisor (GCD) of two numbers (negative allowed) using
 * the non-recursive Euclidean algorithm. The GCD is the largest positive integer that
 * divides both numbers without leaving a remainder. We intentionally avoid recursion to
 * prevent stack overflow for large numbers.
 *
 * @param a - The first number.
 * @param b - The second number.
 * @returns The GCD of the two numbers.
 */
export const gcd = function(a: bigint, b: bigint): bigint {
    // work with absolute values so gcd(−8, 12) === 4
    a = abs(a);
    b = abs(b);

    while (b !== 0n) [a, b] = [b, a % b];
    return a; // already non-negative
};

/**
 * Calculate the least common multiple (LCM) of two numbers using the GCD.
 * The LCM is the smallest positive integer that is divisible by both numbers.
 * We use a / gcd(a, b) * b instead of a * b / gcd(a, b) to reduces the chance of overflows,
 * which avoids one super-wide intermediate.
 *
 * Returns 0n if either argument is 0n (conventional definition).
 * Result has the sign of (a * b) so it is non-negative.
 *
 * The LCM of two coprime 64‑bit numbers is their product.
 *
 * @param a - The first number.
 * @param b - The second number.
 * @returns The LCM of the two numbers.
 */
export const lcm = (a: bigint, b: bigint): bigint => (a === 0n || b === 0n) ? 0n : (a / gcd(a, b)) * b;

/**
 * Calculate the greatest common divisor (GCD) of multiple numbers using the GCD function.
 *
 * @param {...bigint[]} nums - The numbers to calculate the GCD for.
 * @return {bigint} The GCD of the numbers.
 * @throws {TypeError} If no arguments are provided.
 */
export const gcdMulti = function(...nums: bigint[]): bigint {
    if (nums.length === 0) throw new TypeError("gcdMulti() requires at least one argument");
    return nums.reduce((acc, n) => gcd(acc, n));
};

/**
 * Calculate the least common multiple (LCM) of multiple numbers using the LCM function.
 *
 * @param {...bigint[]} nums - The numbers to calculate the LCM for.
 * @return {bigint} The LCM of the numbers.
 * @throws {TypeError} If no arguments are provided.
 */
export const lcmMulti = function(...nums: bigint[]): bigint {
    if (nums.length === 0) throw new TypeError("lcm() requires at least one argument");
    return nums.reduce((acc, n) => lcm(acc, n));
};

/**
 * Extended Euclidean algorithm to find the GCD of two numbers and
 * the coefficients x and y such that ax + by = gcd(a, b) -> The Bézout identity.
 *
 * @param a - The first number.
 * @param b - The second number.
 * @returns An array containing the GCD and the Bézout coefficients x and y.
 * @see {@link https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm}
 * @see {@link https://en.wikipedia.org/wiki/B%C3%A9zout%27s_identity}
 */
export const gcdExt = function(a: bigint, b: bigint): [bigint, bigint, bigint] {
    let x0 = 1n;
    let x1 = 0n;
    let y0 = 0n;
    let y1 = 1n;

    while (b !== 0n) {
        const q = a / b;
        [a, b] = [b, a % b];
        [x0, x1] = [x1, x0 - q * x1];
        [y0, y1] = [y1, y0 - q * y1];
    }
    return [a >= 0n ? a : -a, x0, y0];
};

/**
 * Modulo operation for BigInt - Actual modulo instead of remainder (%).
 * This is useful for negative numbers, as the result is always non-negative.
 *
 * @param {bigint} a - The dividend.
 * @param {bigint} b - The divisor.
 * @return {bigint} The result of a mod b.
 * @throws {RangeError} If b is 0.
 */
export const mod = function(a: bigint, b: bigint): bigint {
    if (b === 0n) throw new RangeError("mod(): divisor must not be 0");
    const r = a % b;
    return r >= 0n ? r : r + (b > 0n ? b : -b);
};

/**
 * Calculate the modular exponentiation of a base raised to an exponent modulo a number.
 * This is useful for large numbers and cryptography.
 *
 * @param base - The base number.
 * @param exp - The exponent.
 * @param m - The modulus.
 * @returns The result of (base ^ exp) % mod.
 */
export const modPow = function(base: bigint, exp: bigint, m: bigint): bigint {
    // avoid huge first square
    base %= m;
    let res = 1n;
    while (exp > 0n) {
        if (exp & 1n) res = (res * base) % m;
        base = (base * base) % m;
        exp >>= 1n;
    }
    return res;
};

/**
 * Calculate the modular inverse of a number using the Extended Euclidean algorithm.
 * This is useful for cryptography and modular arithmetic.
 *
 * @param a - The number to find the modular inverse for.
 * @param m - The modulus.
 * @returns The modular inverse of a modulo m.
 * @throws {RangeError} If m is 0 or if a and m are not coprime.
 */
export const modInv = function(a: bigint, m: bigint): bigint {
    if (m === 0n) throw new RangeError("modInv() modulus must not be 0");
    a = mod(a, m); // a may be negative: 0 ≤ a < m
    const [g, x] = gcdExt(a, m);
    if (g !== 1n) throw new RangeError("modInv() a and m are not coprime");
    return mod(x, m); // ensure positive result
};

/**
 * Calculate the modular division of two numbers.
 *
 * @param {bigint} a - The dividend.
 * @param {bigint} b - The divisor.
 * @param {bigint} m - The modulus.
 * @return {bigint} The result of (a / b) mod m.
 * @throws {RangeError} If b or m is 0.
 */
export const modDiv = function(a: bigint, b: bigint, m: bigint): bigint {
    if (b === 0n) throw new RangeError("modDiv() divisor must not be 0");
    if (m === 0n) throw new RangeError("modDiv() modulus must not be 0");
    return mod(a * modInv(b, m), m);
};

/**
 * Miller-Rabin primality test on 64-bit-size BigInts with deterministic base set.
 * This is a test to determine is a number is prime or composite.
 * It is deterministic for all numbers up to 2^64.
 *
 * @param n - The number to test for primality.
 * @returns true if the number is prime, false if it is composite.
 * @see {@link https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test}
 */
export const isPrime = function(n: bigint): boolean {
    if (n < 2n) return false;

    // quick exits for small primes / trivial divisors
    const SMALL = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n] as const;
    for (const p of SMALL) {
        if (n === p) return true;
        if (n % p === 0n) return false;
    }

    // write n-1 = 2^s · d with d odd
    let d = n - 1n;
    let s = 0n;
    while ((d & 1n) === 0n) {
        d >>= 1n;
        s++;
    }

    // Seven deterministic witnesses cover all 64-bit n
    const BASES = [2n, 3n, 5n, 7n, 11n, 13n, 17n] as const;

    WitnessLoop: for (const a of BASES) {
        // (a | n) = 1 when n ≤ a, so skip in that rare case
        if (a >= n) continue;

        let x = modPow(a, d, n);
        if (x === 1n || x === n - 1n) continue;

        for (let r = 1n; r < s; r++) {
            // cheaper than calling modPow again
            x = (x * x) % n;
            if (x === n - 1n) continue WitnessLoop;
        }
        return false; // composite
    }
    return true; // prime
};

/**
 * Return a cryptographically-strong random bigint in the
 * inclusive range [min, max]. Falls back to Math.random
 * when Web Crypto is missing (non-CSPRNG).
 *
 * @param min - The minimum value (inclusive).
 * @param max - The maximum value (inclusive).
 * @returns A random bigint in the range [min, max].
 * @throws {RangeError} If max is less than min.
 */
export const randomBigInt = function(min: bigint, max: bigint): bigint {
    const range = max - min + 1n;
    if (range <= 0n) throw new RangeError("max must be ≥ min");

    const bitLength = range.toString(2).length;
    const byteLength = Math.ceil(bitLength / 8);

    const getRandomBytes = (len: number): Uint8Array => {
        if (typeof crypto !== "undefined" && crypto.getRandomValues) {
            // Browser, Bun, Node ≥ 20
            return crypto.getRandomValues(new Uint8Array(len));
        }
        /* non-CSPRNG fallback */
        const out = new Uint8Array(len);
        for (let i = 0; i < len; i++) out[i] = Math.floor(Math.random() * 256);
        return out;
    };

    // Draw rnd ∈ [0 , 2^bits - 1] and accept when rnd < range
    // Acceptance probability is around P(accept) = (range / 2^bits) >= 0.5
    // so, reaching 30 iterations is already below 1 in 2^29
    while (true) {
        const bytes = getRandomBytes(byteLength);
        let rnd = 0n;
        for (const b of bytes) rnd = (rnd << 8n) | BigInt(b);
        // uniform via rejection-sampling
        if (rnd < range) return min + rnd;
    }
};

/**
 * Pollard's ρ algorithm for integer factorization using
 * Brent's cycle detection / batching variant for speed.
 *
 * @param n - The number to factor.
 * @returns a non-trivial factor of n (or n itself if n is prime).
 * @see {@link https://en.wikipedia.org/wiki/Pollard%27s_rho_algorithm}
 */
export const pollardRho = (n: bigint): bigint => {
    // Quick outs for even or prime n
    if (n % 2n === 0n) return 2n;
    if (isPrime(n)) return n;

    // Polynomial f(x) = x² + c (mod n)
    const f = (x: bigint, c: bigint): bigint => (x * x + c) % n;

    while (true) {
        // Fresh random parameters for each restart
        const y0 = randomBigInt(2n, n - 2n); // initial value
        const c  = randomBigInt(1n, n - 1n); // polynomial constant
        const m  = 128n;                     // batch size for Brent
        let y = y0;                          // "powering" value
        let r = 1n;                          // cycle length estimate
        let q = 1n;                          // product of |x-y| mod n
        let g = 1n;                          // current gcd
        let x: bigint = y0;                  // last x position
        let ys: bigint = y0;                 // back-tracking pointer

        // Main Brent loop
        while (g === 1n) {
            x = y;
            /* Advance y by r steps (hare) */
            for (let i = 0n; i < r; i++) y = f(y, c);

            // Batch multiplications of |x − y| mod n
            let k = 0n;
            while (k < r && g === 1n) {
                ys = y;
                const lim = (m < r - k) ? m : r - k;
                for (let i = 0n; i < lim; i++) {
                    y = f(y, c);
                    const diff = x > y ? x - y : y - x;
                    q = (q * diff) % n;
                }
                // gcd once per batch
                g = gcd(q, n);
                k += lim;
            }
            // r *= 2
            r <<= 1n;
        }

        // If we only detected failure (g == n) walk back one-by-one
        if (g === n) {
            do {
                ys = f(ys, c);
                const diff = x > ys ? x - ys : ys - x;
                g = gcd(diff, n);
            } while (g === 1n);
        }

        // Non-trivial factor found
        if (g !== n) return g;
        // otherwise restart with new parameters
    }
};

/**
 * Factor a number into its prime factors using Pollard's rho algorithm.
 * Iterative: no recursion → safe for very composite inputs.
 *
 * @param {bigint} n - The number to factor.
 * @return {Map<bigint, bigint>} A map of prime factors and their powers.
 */
export const factor = function(n: bigint): Map<bigint, bigint> {
    const factors = new Map<bigint, bigint>();
    const stack: bigint[] = [n];

    while (stack.length) {
        // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
        const current = stack.pop()!;
        if (current === 1n) continue;

        if (isPrime(current)) {
            // tally prime power
            factors.set(current, (factors.get(current) ?? 0n) + 1n);
            continue;
        }

        // split composite and keep working on the parts
        const divisor = pollardRho(current);
        stack.push(divisor, current / divisor);
    }
    return factors;
};

/**
 * Calculate the nth Fibonacci number modulo m using
 * iterative fast-doubling over the bits of n.
 * Works for n ≥ 0, m ≥ 1, all bigint.
 *
 * @param {bigint} n - The Fibonacci number to calculate.
 * @param {bigint} m - The modulus.
 * @return {bigint} The nth Fibonacci number modulo m (Fₙ mod m, Fₙ₊₁ mod m).
 * @see {@link https://www.nayuki.io/page/fast-fibonacci-algorithms}
 * @see {@link https://oeis.org/A000045}
 */
export const fibPair = function(n: bigint, m: bigint): [bigint, bigint] {
    // everything ≡ 0 mod 1
    if (m === 1n) return [0n, 0n];

    let a = 0n; // F₀
    let b = 1n; // F₁

    // find highest set bit without String()
    let bit = 0n;
    for (let tmp = n; tmp > 0n; tmp >>= 1n) bit++;

    // scan bits from MSB → LSB
    for (bit -= 1n; bit >= 0n; bit--) {
        // 2·Fₖ (mod m)
        const twoB = (b << 1n) % m;
        // F₂k
        const d = (a * ((twoB - a + m) % m)) % m;
        // F₂k+1
        const e = (a * a + b * b) % m;

        const isOdd = (n >> bit) & 1n;
        // next = (F₂k+1, F₂k + F₂k+1)
        if (isOdd) {
            a = e;
            b = (d + e) % m;
        }
        // next = (F₂k  , F₂k+1)
        else {
            a = d;
            b = e;
        }
    }
    return [a, b];
};

/**
 * Calculate the Pisano period π(p) for a prime p.
 * Handles the special primes 2 and 5 explicitly.
 * Safe for large p (≤ 2⁶⁴ in practice because of factorisation speed).
 *
 * @param {bigint} p - The prime number to calculate the Pisano period for (prime modulus).
 * @return {bigint} The Pisano period π(p) - (or throws if p is not prime).
 * @throws {Error} If p is not prime.
 */
export const primePisano = (p: bigint): bigint => {
    if (!isPrime(p)) throw new Error("primePisano: p must be prime");
    if (p === 2n) return 3n;
    if (p === 5n) return 20n;

    // 1. Choose the bound that π(p) must divide
    // Legendre symbol (5 | p) via Euler’s criterion
    // https://en.wikipedia.org/wiki/Euler%27s_criterion
    const legendre5 = modPow(5n, (p - 1n) / 2n, p); // 1n or p-1n
    const bound = (legendre5 === 1n)
        ? (p - 1n)       // 5 is a square → p-1
        : 2n * (p + 1n); // otherwise     → 2(p+1)

    // 2. Factor the bound and enumerate all its divisors
    const factors = Array.from(factor(bound)); // [[prime, exp], …]

    // Build the set of divisors by progressive multiplication
    const divisors: bigint[] = [1n];
    for (const [prime, expBig] of factors) {
        const exp = expBig <= 9_007_199_254_740_991n // 2⁵³-1
            ? Number(expBig)
            : ((): never => {
                throw new Error("Exponent too large");
            })();

        const currentLen = divisors.length;
        let power = 1n;
        for (let i = 1; i <= exp; i++) {
            power *= prime;
            for (let j = 0; j < currentLen; j++) {
                const divisor = divisors[j];
                if (divisor !== undefined) divisors.push(divisor * power);
            }
        }
    }

    // Sort strictly with bigint comparison
    // eslint-disable-next-line no-nested-ternary
    divisors.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));

    // 3. Test each divisor with fast‐doubling Fibonacci mod p
    for (const d of divisors) {
        const [Fd, Fd1] = fibPair(d, p);       // returns (F_d mod p, F_{d+1} mod p)
        if (Fd === 0n && Fd1 === 1n) return d; // first hit is the period
    }

    // Should never happen if factorisation is correct
    throw new Error("primePisano: period not found (factorisation error?)");
};

/**
 * Calculate the Pisano period π(n) for any positive integer n ≥ 1.
 * The period is lcm { π(pᵉ) } over the prime-power decomposition of n.
 * The result is the smallest period of the Fibonacci sequence modulo n.
 *
 * @param {bigint} n - The composite number to calculate the Pisano period for.
 * @return {bigint} The Pisano period π(n).
 * @see {@link https://en.wikipedia.org/wiki/Pisano_period}
 * @see {@link https://oeis.org/A001175}
 */
export const pisanoPeriod = function(n: bigint): bigint {
    if (n === 1n) return 1n;

    // Map<prime, exp>
    const primeFactors = factor(n);
    let period = 1n;

    for (const [p, e] of primeFactors) {
        // π(pᵉ) = π(p)·p^{e-1}  for all primes except 2,5 (rule still works for >1)
        const primePart = primePisano(p) * p ** (e - 1n);
        period = lcm(period, primePart);
    }
    return period;
};
