"""Compare the ordered prime-pair count and catalogue model on dyadic progression windows."""

import argparse
from functools import lru_cache
from math import cos, fsum, gcd, isqrt, pi
from typing import NamedTuple

import numpy as np
from scipy.fft import irfft, next_fast_len, rfft
from scipy.integrate import quad
from scipy.special import sici


def prime_weights(limit):
    prime = np.ones(limit + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, isqrt(limit) + 1):
        if prime[p]:
            prime[p * p :: p] = False
    weights = np.zeros(limit + 1)
    weights[prime] = np.log(np.flatnonzero(prime))
    return weights


def mobius_totient(limit):
    mu = [1] * (limit + 1)
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for n in range(p, limit + 1, p):
                phi[n] -= phi[n] // p
                mu[n] *= -1
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
    return mu, phi


def ordered_counts(weights):
    size = next_fast_len(2 * len(weights) - 1, real=True)
    return irfft(rfft(weights, size) ** 2, size)[:len(weights)]


@lru_cache(maxsize=None)
def arc_mass(z):
    phase = 2 * pi * z
    return 2 / pi * sici(phase)[0] - (1 - cos(phase)) / (pi ** 2 * z)


def model_ratios(limit, mu, phi):
    # On each log-cutoff block, collect the Ramanujan divisor sums by divisor.
    ratios = np.zeros(limit + 1)
    for j in range(1, (limit + 2).bit_length()):
        lo, hi = 2**j - 2, min(2**(j + 1) - 2, limit + 1)
        cutoff = j**2
        for d in range(1, cutoff + 1):
            coefficient = d * fsum(
                mu[q // d] * arc_mass(cutoff / q) / phi[q]**2
                for q in range(d, cutoff + 1, d) if mu[q]
            )
            first = (lo + d - 1) // d * d
            ratios[first:hi:d] += coefficient
    return ratios


def progression_prefix(weights, stop, modulus):
    """Independent sum of actual pair weights with p+r <= stop and modulus | p+r."""
    total = 0.0
    for a in range(min(modulus, stop + 1)):
        p = np.arange(a, stop + 1, modulus)
        b = -a % modulus
        prefix = np.concatenate(([0.0], np.cumsum(weights[b:stop + 1:modulus])))
        lengths = np.maximum(0, (stop - p - b) // modulus + 1)
        total += np.sum(weights[p] * prefix[lengths])
    return total


def sum_multiples(lo, hi, step):
    first, last = lo // step, hi // step
    return step * (last * (last + 1) - first * (first + 1)) // 2


def direct_model_total(lo, hi, modulus, mu, phi):
    """Independent window sum from c_q(n) = mu(q/g) phi(q) / phi(q/g), g = gcd(q,n)."""
    terms = []
    for j in range(1, (hi + 2).bit_length()):
        left, right = max(lo, 2**j - 3), min(hi, 2**(j + 1) - 3)
        if left >= right:
            continue
        for q in range(1, j*j + 1):
            if not mu[q]:
                continue
            period = q // gcd(modulus, q)
            weighted = 0
            for a in range(1, period + 1):
                reduced = q // gcd(q, modulus * a)
                ram = mu[reduced] * (phi[q] // phi[reduced])
                step = period * modulus
                start = left + 1 + (modulus * a - left - 1) % step
                if start <= right:
                    count = (right - start) // step + 1
                    weighted += ram * (count * start + step * count * (count - 1) // 2)
            terms.append(weighted * arc_mass(j*j / q) / phi[q]**2)
    return fsum(terms)


class Window(NamedTuple):
    limit: int
    modulus: int
    count: int
    pairs: float
    model: float


def compare(weights, counts, ratios, limit, modulus, mu, phi):
    lo = limit // 2
    first = (lo // modulus + 1) * modulus
    targets = np.arange(first, limit + 1, modulus)
    if not len(targets):
        return None
    denominator = sum_multiples(lo, limit, modulus)
    pairs = float(counts[targets].sum()) / denominator
    model = float(np.dot(ratios[targets], targets)) / denominator
    direct_pairs = (progression_prefix(weights, limit, modulus)
                    - progression_prefix(weights, lo, modulus)) / denominator
    direct_model = direct_model_total(lo, limit, modulus, mu, phi) / denominator
    np.testing.assert_allclose([pairs, model], [direct_pairs, direct_model], rtol=1e-9, atol=1e-11)
    return Window(limit, modulus, len(targets), pairs, model)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--powers', type=int, nargs='+', default=[14, 17, 20])
    parser.add_argument('--moduli', type=int, nargs='+', default=[2, 6, 24, 120, 720])
    args = parser.parse_args()
    if min(args.powers) < 1 or min(args.moduli) < 1:
        parser.error('powers and moduli must be positive')
    limit = 2 ** max(args.powers)
    weights = prime_weights(limit)
    mu, phi = mobius_totient(((limit + 2).bit_length() - 1)**2)
    counts = ordered_counts(weights)
    ratios = model_ratios(limit, mu, phi)
    # Check the factor of two and the integral endpoint normalization independently.
    for n in {2, min(10, limit), limit - 1}:
        direct = np.dot(weights[:n + 1], weights[n::-1])
        np.testing.assert_allclose(counts[n], direct, rtol=1e-9, atol=1e-9)
    for z in (1, 1.5, 5):
        direct = 2 * quad(lambda t: float(np.sinc(t))**2, 0, z)[0]
        np.testing.assert_allclose(arc_mass(z), direct, rtol=1e-12)
    print('limit modulus targets sum_R/sum_n sum_M/sum_n difference')
    for power in args.powers:
        for modulus in args.moduli:
            row = compare(weights, counts, ratios, 2**power, modulus, mu, phi)
            if row:
                print(*row[:3], f'{row.pairs:.8f}', f'{row.model:.8f}', f'{row.pairs-row.model:+.8f}')


if __name__ == '__main__':
    main()
