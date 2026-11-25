"""Enclose the square-root conductor moment with outward-rounded integer arithmetic."""

from fractions import Fraction
from math import isqrt


def primes_up_to(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            count = (limit - p * p) // p + 1
            sieve[p * p :: p] = bytes(count)
    return (p for p in range(2, limit + 1) if sieve[p])


def moment_interval(limit=1_000_000, scale=10**16):
    """Return rational endpoints for the entire Euler product."""
    if limit < 2 or scale < 1:
        raise ValueError("A sieve limit of at least two and a positive scale are required.")
    # The tail sum is at most 4 / ((1 - 1/limit)^2 * sqrt(limit)).
    tail = Fraction(4 * limit**2, (limit - 1) ** 2 * isqrt(limit))
    if tail >= 1:
        raise ValueError("Increase the sieve limit until the tail bound is below one.")

    lower = upper = scale
    for p in primes_up_to(limit):
        root = isqrt(p * scale**2)
        denominator = scale * (p - 1) ** 2
        # Each scaled endpoint encloses the partial product after rounding.
        lower = lower * (denominator + 2 * root) // denominator
        numerator = upper * (denominator + 2 * (root + 1))
        upper = (numerator + denominator - 1) // denominator

    # For nonnegative increments of total mass at most t < 1, their product
    # of (1 + increment) is at most 1 / (1 - t), by the geometric series.
    return Fraction(lower, scale), Fraction(upper, scale) / (1 - tail)


if __name__ == "__main__":
    lo, hi = moment_interval()
    assert Fraction(148, 10) < lo <= hi < 15
    print(f"Lower endpoint: {lo}")
    print(f"Upper endpoint: {hi}")
    print("14.8 < conductorSqrtMoment < 15")
