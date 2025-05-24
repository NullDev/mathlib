# mathlib
[![License](https://img.shields.io/github/license/NullDev/mathlib?label=License&logo=Creative%20Commons)](https://github.com/NullDev/mathlib/blob/master/LICENSE)

<p align="center"><img height="150" width="auto" src="https://arithmetica.xyz/img/img.png" /></p>
<p align="center"><b>Zero-dependency collection of advanced mathematical functions using BigInts.</b></p>

<hr>

## ✅ What this is

This is my personal zero-dependency collection of various mathematical functions using BigInts, <br>
completely written from scratch. <br>

Functions _should_ be optimized for performance and accuracy, and _should_ be safe for large numbers. <br>
But I can give zero guarentees. If you're using this, you're on your own. <br>
I do write tests for every single function implemented, but I can't guarentee, that the tests are sane either... <br>
All functions are documented - and I tried to comment the code as well as the tests as good as possible.

<hr>

## ⛔ What this isn't

This is not a fully fledge mathematical library like [mathjs](https://mathjs.org/). <br>
It's a collection of functions I re-use occasionally. And it's **BigInt only!**

<hr>

## 📜 What's implemented:

- abs - Absolute value of a BigInt
- clamp - Clamp a BigInt to a given range
- bitLength - Bit length of a BigInt
- pow - Power of a BigInt (x^y)
- nthRoot - nth root of a BigInt (x^(1/n))
- sqrt - Square root of a BigInt
- manhattanDist - Manhattan distance between two BigInts
- euclideanDist - Euclidean distance between two BigInts
- gcd - Greatest common divisor (2 inputs)
- gcdMulti - Greatest common divisor of multiple numbers (variadic)
- gcdExt - Extended Euclidean gcd algorithm for Bézout coefficients
- lcm - Least common multiple (2 inputs)
- lcmMulti - Least common multiple of multiple numbers (variadic)
- mod - True modulo operation for BigInt (not remainder)
- modPow - Modular exponentiation of a base raised to an exponent modulo a number
- modInv - Modular inverse of a number using the Extended Euclidean algorithm
- modDiv - Modular division of two numbers
- isPrime - Miller-Rabin primality test on 64-bit-size BigInts with deterministic base set
- eulerCriterion - Euler's criterion for quadratic residues modulo a prime p
- randomBigInt - Cryptographically-strong (hopefully) random bigint in given range
- quadraticPoly - Quadratic polynomial f(x) = x² + c modulo n
- pollardRho - Pollard's ρ algorithm for integer factorization using Brent's cycle detection
- factor - Prime factorization using Pollard's rho
- highestSetBit - Position of the highest set bit in a BigInt
- fibPair - Calculate the nth Fibonacci number modulo m using iterative fast-doubling
- primePisano - Pisano period π(p) for a prime p
- pisanoPeriod - Pisano period π(n) for any positive integer n ≥ 1
- totient - Euler's totient function φ(n)

... more to come

<hr>

## 📋 To-Do

- [ ] Test coverage overview / reporting
- [ ] Build step & minification for browser
- [ ] Better test setup (still figuring out bun:test)
- [ ] Add more functions (only with tests)
- [ ] NPM package maybe

<hr>

## :octocat: Contributing

Don't really expect anyone to contribute but...
- Bun is needed to run the tests
- TypeScript only
- Adhere to style guide (eslint)
- Every function should have a test
- Every function should be documented

<br>
