/// Erdos Problem 396 / OEIS A375077
///
/// Find smallest n >= k+1 such that n*(n-1)*...*(n-k) divides C(2n,n).
///
/// Known values:
///   a(0)=1, a(1)=2, a(2)=2480, a(3)=8178, a(4)=45153,
///   a(5)=3648841, a(6)=7979090, a(7)=101130029
///   a(8)=??? (our target!)
///
/// Algorithm: For each n, check divisibility using p-adic valuations.
///   v_p(C(2n,n)) = sum_{i>=1} (floor(2n/p^i) - 2*floor(n/p^i))
///   v_p(n*(n-1)*...*(n-k)) = sum_{j=0}^{k} v_p(n-j)
///
/// We need v_p(C(2n,n)) >= v_p(product) for ALL primes p.

use rayon::prelude::*;
use std::env;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

/// Sieve primes up to `limit` using Sieve of Eratosthenes
fn sieve_primes(limit: usize) -> Vec<u64> {
    let mut is_prime = vec![true; limit + 1];
    is_prime[0] = false;
    if limit >= 1 {
        is_prime[1] = false;
    }
    let mut i = 2;
    while i * i <= limit {
        if is_prime[i] {
            let mut j = i * i;
            while j <= limit {
                is_prime[j] = false;
                j += i;
            }
        }
        i += 1;
    }
    (2..=limit).filter(|&i| is_prime[i]).map(|i| i as u64).collect()
}

/// Compute v_p(n) — the p-adic valuation of n
#[inline]
fn v_p(mut n: u64, p: u64) -> u32 {
    if n == 0 {
        return u32::MAX;
    }
    let mut v = 0u32;
    while n % p == 0 {
        n /= p;
        v += 1;
    }
    v
}

/// Compute v_p(C(2n, n)) using Legendre's formula
/// v_p(C(2n,n)) = sum_{i>=1} (floor(2n/p^i) - 2*floor(n/p^i))
#[inline]
fn v_p_central_binom(n: u64, p: u64) -> u32 {
    let mut total = 0u32;
    let mut pk = p;
    let two_n = 2 * n;
    loop {
        let term = (two_n / pk) - 2 * (n / pk);
        total += term as u32;
        // Check if next power would overflow or exceed 2n
        if pk > two_n / p {
            break;
        }
        pk *= p;
    }
    total
}

/// Check if n*(n-1)*...*(n-k) divides C(2n,n)
fn check_n(n: u64, k: u64, primes: &[u64]) -> bool {
    // Quick reject: check p=2 using popcount
    {
        let popcount = n.count_ones();
        let mut v2_product = 0u32;
        for j in 0..=k {
            v2_product += (n - j).trailing_zeros();
        }
        if popcount < v2_product {
            return false;
        }
    }

    // Check each small prime
    for &p in primes.iter().skip(1) {
        // skip p=2 (already checked above)
        if p > n {
            break;
        }

        // Compute v_p of the product n*(n-1)*...*(n-k)
        let mut vp_product = 0u32;
        for j in 0..=k {
            let val = n - j;
            if val % p == 0 {
                vp_product += v_p(val, p);
            }
        }

        if vp_product == 0 {
            continue;
        }

        let vp_binom = v_p_central_binom(n, p);
        if vp_binom < vp_product {
            return false;
        }
    }

    // Check large prime factors (those > sieve limit)
    // After trial division by small primes, any remaining factor > 1 is prime
    for j in 0..=k {
        let mut val = n - j;
        if val <= 1 {
            continue;
        }
        // Divide out all small prime factors
        for &p in primes {
            if p * p > val {
                break;
            }
            while val % p == 0 {
                val /= p;
            }
        }
        // If val > 1, it's a large prime factor with multiplicity 1
        if val > 1 {
            let large_p = val;
            // Among k+1 consecutive numbers, at most one is divisible by large_p
            // (since large_p > k+1 for large n), so v_p(product) = v_p(n-j) = 1
            let vp_binom = v_p_central_binom(n, large_p);
            if vp_binom < 1 {
                return false;
            }
        }
    }

    true
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let k: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(8);
    let start: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(k + 1);
    let end: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(10_000_000_000);
    let chunk_size: u64 = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(1_000_000);

    eprintln!("=== Erdos 396 / OEIS A375077 ===");
    eprintln!("Searching for a({k})");
    eprintln!("Range: [{start}, {end})");
    eprintln!("Chunk size: {chunk_size}");

    // First verify known values
    let known: Vec<(u64, u64)> = vec![
        (0, 1), (1, 2), (2, 2480), (3, 8178), (4, 45153),
        (5, 3648841), (6, 7979090), (7, 101130029),
    ];

    // Sieve primes up to sqrt(end) + some buffer
    let sieve_limit = ((end as f64).sqrt() as usize) + 1000;
    eprintln!("Sieving primes up to {sieve_limit}...");
    let primes = sieve_primes(sieve_limit);
    eprintln!("Found {} primes", primes.len());

    // Verify known values
    eprintln!("\nVerifying known values:");
    for &(ki, ni) in &known {
        if ki <= k {
            let ok = check_n(ni, ki, &primes);
            eprintln!("  a({ki}) = {ni}: {}", if ok { "PASS" } else { "FAIL" });
        }
    }
    eprintln!();

    let found = Arc::new(AtomicBool::new(false));
    let best_n = Arc::new(AtomicU64::new(u64::MAX));
    let start_time = Instant::now();

    let mut chunk_start = start;
    let mut last_report = Instant::now();

    while chunk_start < end && !found.load(Ordering::Relaxed) {
        let chunk_end = (chunk_start + chunk_size).min(end);

        let found_ref = Arc::clone(&found);
        let result: Option<u64> = (chunk_start..chunk_end)
            .into_par_iter()
            .find_first(|&n| {
                if found_ref.load(Ordering::Relaxed) {
                    return false;
                }
                check_n(n, k, &primes)
            });

        if let Some(n) = result {
            let current_best = best_n.load(Ordering::Relaxed);
            if n < current_best {
                best_n.store(n, Ordering::Relaxed);
                found.store(true, Ordering::Relaxed);
                let elapsed = start_time.elapsed();
                println!("a({k}) = {n}");
                eprintln!("Found at n={n} after {:.1}s", elapsed.as_secs_f64());

                // Double-verify
                let ok = check_n(n, k, &primes);
                eprintln!("Verification: {}", if ok { "PASS" } else { "FAIL" });

                // Also check that no smaller n in this chunk works
                // (find_first should handle this, but verify)
                eprintln!("Checking no smaller n exists in this chunk...");
                let smaller: Option<u64> = (chunk_start..n)
                    .into_par_iter()
                    .find_first(|&m| check_n(m, k, &primes));
                if let Some(m) = smaller {
                    println!("WARNING: found smaller a({k}) = {m}");
                }
                break;
            }
        }

        chunk_start = chunk_end;

        if last_report.elapsed().as_secs() >= 10 {
            let elapsed = start_time.elapsed();
            let checked = chunk_start - start;
            let rate = checked as f64 / elapsed.as_secs_f64();
            let remaining = end - chunk_start;
            eprintln!(
                "n={chunk_start} ({:.2}M/s, {:.0}s elapsed, ~{:.0}s remaining)",
                rate / 1e6,
                elapsed.as_secs_f64(),
                remaining as f64 / rate
            );
            last_report = Instant::now();
        }
    }

    if !found.load(Ordering::Relaxed) {
        let elapsed = start_time.elapsed();
        eprintln!("NOT FOUND in [{start}, {end})");
        eprintln!("Elapsed: {:.1}s", elapsed.as_secs_f64());
    }
}
