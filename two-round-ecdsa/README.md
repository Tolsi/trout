# 2-round Threshold ECDSA

This is an implementation of a simulatable 2-round threshold ECDSA protocol, for arbitrary
thresholds. It uses class groups as a Partially-Homomorphic Encryption system, and is configurable
to the number libraries/ZK proofs used.

### Proofs

Only four relations in total are needed.

1) [An eVRF](https://eprint.iacr.org/2024/397)
2) $R_{CL-EC}$: A proof a class-groups ciphertext encrypts the discrete logarithm of an EC point
3) $R_{ComKwlg}$: A proof of knowledge for the opening of a Pedersen Commitment over the class group
4) $R_{affCom}$: A proof of a transformation of a ciphertext by the opening of commitments

The first three are needed for `RoundOneProofs` to achieve unforgeability. The final proof is needed
by `RoundTwoProofs` only to achieve identifiable aborts. An implementation of `RoundOneProofs`,
`NoIdentifiableAborts`, is provided which does nothing to sacrifice identifiable aborts for
efficiency.

For the full set of proofs (other than the eVRF), Handong Cui, Kwan Yin Chan, Tsz Hon Yuen,
Xin Kang, and Cheng-Kang Chu's "Bandwidth-Efficient Zero-Knowledge Proofs for Threshold ECDSA" is
preferred. These proofs do require a hash-to-prime number, of which three implementations are
provided in the codebase:

1) `CryptoPrimesStack`: A hash-to-prime internally using
   [`crypto-primes`](https://docs.rs/crypto-primes). This isn't safe per
   <https://github.com/entropyxyz/crypto-primes/issues/23> and
   <https://github.com/entropyxyz/crypto-primes/issues/25>. Additionally, this implementation may
   panic if too large a prime is requested (though `CryptoPrimesStackCcykc` is guaranteed to not
   panic with `Ccykc2023RoundOne` and `Ccykc2023RoundTwo`).
2) `CryptoPrimesHeap`: A hash-to-prime internally using
   [`crypto-primes`](https://docs.rs/crypto-primes), again unsafe per the prior reasons. It won't
   panic if too large a prime is requested though due to using a heap-allocated dynamically-sized
   integer instead of a stack-allocated fixed-sized integer. It is roughly twice as slow as
   `CryptoPrimesStack`.
3) `GmpPrimes`: A hash-to-prime internally using `gmp`'s `next_prime`. This is unsafe to use as it's
   biased to an unqualified degree. It is consistent across versions of `gmp`, ~4x faster than
   `CryptoPrimesStack`, and ~9x faster than `CryptoPrimesHeap`. It is the recommended choice.

### Future Work

The prover executes in variable-time, raising the question of side-channel analysis. The underlying
`class-groups` library is variable to the backend not only to experiment with different backends,
yet so a *constant-time* backend may be used. One should be implemented, with the prover migrated,
before this is deployed to any security-sensitive environment.

Currently, elements of the class group are always of the class group with discriminant $\delta_p$.
Some elements can be left in the class group with discriminant $\delta_k$, shortening them ~10%.
Since such elements also would lack a subgroup component where the discrete-log problem is easy,
more efficient ZK proofs should exist for such elements (as CCYCK responses are of the form
$D \in \hat{G}, e \in Z$ where $e = (r + c * x) \mod ql$, where $q$ is the order of the subgroup and
$l$ is a randomly sampled prime. Simply $\mod l$ should be valid).

The protocol itself only requires the determination of signing set and message for the second round.
It's solely the security proofs which require these to be determined before the protocol begins. The
code allows the caller to delay determination, trusting the caller to do so securely. This either
means not doing so (the only proven-secure and endorsed solution at this time) or having additional
proofs for the security of such a scheme. Such proofs may be possible, as potentially implied by
Xianrui Qin, Cailing Cai, and Tsz Hon Yuen's
[One-more unforgeability of Blind ECDSA](https://eprint.iacr.org/2021/1449).

The $U$ commitment is of the form $\beta_i \cdot G + u_i \cdot Y$. Since $G$ is a generator of $G_q$
and the unknown order is not divisible by $q$, the order of the subgroup where the discrete-log
problem is easy, it may be sufficient to define $U$ as $((\beta_i * q) + u_i) \cdot G$. This is
binding to the discrete logarithm unless the prover knows the order of the unknown-order subgroup.
This is presumably also perfectly hiding as for the opening $((\beta_i * q) + u_i) \cdot G$, there
is the alternative opening $(((\beta_i * q) + u_i) + s) \cdot G$ where $s$ is the unknown order.
Since $gcd(s, q) == 1$, $((\beta_i * q) + u_i) != (((\beta_i * q) + u_i) + s) \mod q$, meaning
that any commitment can be opened to any value (given a sufficiently large choice of $\beta_i$).
This would enable replacing the class-group ciphertexts with solely their second term as we would no
longer need the commitments to their randomness over an alternate generator to perform decryption.
