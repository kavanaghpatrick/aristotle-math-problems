//! A375071: Erdős 389 minimal k computation
//!
//! a(n) = smallest k >= 1 such that prod(n+1..n+k) | prod(n+k+1..n+2k)
//!
//! Equivalent to: for every prime p,
//!   v_p((n+2k)!) + v_p(n!) >= 2 * v_p((n+k)!)
//!
//! For primes p > sieve_limit with p^2 > n+2k, only j=1 of Legendre matters.
//! The j=1 condition for p > n fails iff (n+k) mod p ∈ {0,...,floor((n-1)/2)}.
//! We post-filter by checking if {k+ceil((n+1)/2),...,k+n} has prime factors > sieve_limit.

use std::env;
use std::time::Instant;

const SIEVE_LIMIT: usize = 100_000_000;

/// Sieve of Eratosthenes up to limit, returning Vec<u64>
fn sieve_primes(limit: usize) -> Vec<u64> {
    if limit < 2 {
        return vec![];
    }
    let mut is_prime = vec![true; limit + 1];
    is_prime[0] = false;
    is_prime[1] = false;
    let sqrt_limit = (limit as f64).sqrt() as usize;
    for i in 2..=sqrt_limit {
        if is_prime[i] {
            let mut j = i * i;
            while j <= limit {
                is_prime[j] = false;
                j += i;
            }
        }
    }
    is_prime
        .iter()
        .enumerate()
        .filter(|(_, &b)| b)
        .map(|(i, _)| i as u64)
        .collect()
}

/// Legendre's formula: v_p(m!) = sum_{i>=1} floor(m / p^i)
#[inline(always)]
fn legendre(m: u64, p: u64) -> u64 {
    let mut s = 0u64;
    let mut pk = p;
    while pk <= m {
        s += m / pk;
        if pk > m / p {
            break;
        }
        pk *= p;
    }
    s
}

/// Check divisibility using sieved primes only.
/// May produce false positives when sieve doesn't cover all primes up to n+2k.
#[inline(always)]
fn check_divisibility_sieved(n: u64, k: u64, primes: &[u64]) -> bool {
    let upper = n + 2 * k;
    let mid = n + k;

    // Inline check for first 4 primes (catches ~95% of failures)
    {
        let v = legendre(upper, 2) + legendre(n, 2);
        if v < 2 * legendre(mid, 2) {
            return false;
        }
    }
    if upper >= 3 {
        let v = legendre(upper, 3) + legendre(n, 3);
        if v < 2 * legendre(mid, 3) {
            return false;
        }
    }
    if upper >= 5 {
        let v = legendre(upper, 5) + legendre(n, 5);
        if v < 2 * legendre(mid, 5) {
            return false;
        }
    }
    if upper >= 7 {
        let v = legendre(upper, 7) + legendre(n, 7);
        if v < 2 * legendre(mid, 7) {
            return false;
        }
    }

    // Check remaining sieved primes (from index 4 = prime 11)
    for &p in &primes[4..] {
        if p > upper {
            break;
        }
        if legendre(upper, p) + legendre(n, p) < 2 * legendre(mid, p) {
            return false;
        }
    }
    true
}

/// Verify no prime > sieve_limit causes the Legendre condition to fail.
///
/// For prime p > n with p^2 > n+2k (guaranteed when sieve_limit >= sqrt(n+2k)):
///   only j=1 contributes. Condition fails iff (n+k) mod p ∈ {0,...,floor((n-1)/2)}.
///   Equivalently: p divides some m ∈ {k+ceil((n+1)/2), ..., k+n}.
///
/// After trial division by primes up to sqrt(m), any cofactor > 1 is prime.
/// If that prime > sieve_limit, it wasn't checked → FAIL.
#[inline]
fn verify_no_large_prime_factors(n: u64, k: u64, primes: &[u64], sieve_limit: u64) -> bool {
    let half_floor = (n - 1) / 2; // floor((n-1)/2)

    for j in 0..=half_floor {
        let m = n + k - j;
        let sqrt_m = (m as f64).sqrt() as u64 + 1;
        let mut c = m;
        for &p in primes {
            if p > sqrt_m {
                break;
            }
            while c % p == 0 {
                c /= p;
            }
            if c == 1 {
                break;
            }
        }
        if c > 1 && c > sieve_limit {
            return false;
        }
    }
    true
}

/// Full divisibility check: sieved primes + large prime verification
#[inline]
fn check_full(n: u64, k: u64, primes: &[u64], sieve_limit: u64) -> bool {
    if !check_divisibility_sieved(n, k, primes) {
        return false;
    }
    if sieve_limit >= n + 2 * k {
        return true; // sieve covers everything
    }
    verify_no_large_prime_factors(n, k, primes, sieve_limit)
}

fn verify_known(primes: &[u64], sieve_limit: u64) {
    let known: Vec<(u64, u64)> = vec![
        (0, 1),
        (1, 5),
        (2, 4),
        (3, 207),
        (4, 206),
        (5, 2475),
        (6, 984),
        (7, 8171),
        (8, 8170),
        (9, 45144),
        (10, 45143),
        (11, 3648830),
        (12, 3648829),
        (13, 7979077),
        (14, 7979076),
        (15, 58068862),
        (16, 58068861),
        (17, 255278295),
        (18, 255278294),
    ];

    println!("=== Verifying known A375071 values ===");
    let mut all_ok = true;
    for &(n, expected_k) in &known {
        let result = check_full(n, expected_k, primes, sieve_limit);
        let prev_fails = if expected_k > 1 {
            !check_full(n, expected_k - 1, primes, sieve_limit)
        } else {
            true
        };
        let status = if result && prev_fails {
            "OK"
        } else {
            all_ok = false;
            "FAIL"
        };
        println!("  a({:>2}) = {:>10}: {}", n, expected_k, status);
    }
    if all_ok {
        println!("All 19 known values verified correctly.");
    } else {
        println!("WARNING: Some values FAILED verification!");
    }
    println!();
}

fn search(n: u64, max_k: u64, report_interval: u64, primes: &[u64], sieve_limit: u64) {
    println!("Searching for a({}) with max_k={}...", n, max_k);
    let start = Instant::now();
    let mut checked: u64 = 0;
    let mut false_positives: u64 = 0;

    let need_large_check = sieve_limit < n + 2 * max_k;
    if need_large_check {
        println!(
            "  Note: sieve covers up to {}, need up to {}. Using large-prime post-filter.",
            sieve_limit,
            n + 2 * max_k
        );
    }

    for k in 1..=max_k {
        if check_divisibility_sieved(n, k, primes) {
            if !need_large_check || sieve_limit >= n + 2 * k {
                // Sieve covers this k fully
                let elapsed = start.elapsed().as_secs_f64();
                println!();
                println!("========================================");
                println!("FOUND: a({}) = {}", n, k);
                println!("========================================");
                println!("Time: {:.2}s, Rate: {:.0} k/s", elapsed, checked as f64 / elapsed);
                println!("False positives filtered: {}", false_positives);
                check_pairing(n, k, primes, sieve_limit);
                return;
            }
            // Need large-prime verification
            if verify_no_large_prime_factors(n, k, primes, sieve_limit) {
                let elapsed = start.elapsed().as_secs_f64();
                println!();
                println!("========================================");
                println!("FOUND: a({}) = {}", n, k);
                println!("========================================");
                println!("Time: {:.2}s, Rate: {:.0} k/s", elapsed, checked as f64 / elapsed);
                println!("False positives filtered: {}", false_positives);
                check_pairing(n, k, primes, sieve_limit);
                return;
            } else {
                false_positives += 1;
                if false_positives <= 10 || false_positives % 100 == 0 {
                    println!(
                        "  [FP #{}] k={} passed sieve but failed large-prime check",
                        false_positives, k
                    );
                }
            }
        }
        checked += 1;
        if checked % report_interval == 0 {
            let elapsed = start.elapsed().as_secs_f64();
            let rate = checked as f64 / elapsed;
            let remaining = max_k - checked;
            let eta = remaining as f64 / rate;
            println!(
                "  k up to {:>12}: {:.0} k/s, {:.1}s elapsed, ETA {:.0}s ({:.1}h), FP={}",
                checked, rate, elapsed, eta, eta / 3600.0, false_positives
            );
        }
    }

    let elapsed = start.elapsed().as_secs_f64();
    println!();
    println!("NOT FOUND: a({}) > {}", n, max_k);
    println!("Time: {:.2}s, False positives: {}", elapsed, false_positives);
}

fn check_pairing(n: u64, k: u64, primes: &[u64], sieve_limit: u64) {
    if k < 2 {
        return;
    }
    println!();
    println!("Checking pairing pattern: a({}) = {} ?", n + 1, k - 1);
    let pair = check_full(n + 1, k - 1, primes, sieve_limit);
    if pair {
        let prev = check_full(n + 1, k - 2, primes, sieve_limit);
        if !prev {
            println!("  CONFIRMED: a({}) = {} (minimal)", n + 1, k - 1);
        } else {
            println!("  a({}) divides at k={} but k-2={} also works — NOT minimal", n + 1, k - 1, k - 2);
        }
    } else {
        println!("  Pairing does NOT hold for a({})", n + 1);
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        println!("Usage:");
        println!("  a375071 verify             -- Verify all 19 known values");
        println!("  a375071 bench              -- Benchmark speed");
        println!("  a375071 search <n> [max_k] -- Search for a(n)");
        println!("  a375071 all <start> <end>   -- Compute a(start)..a(end)");
        return;
    }

    // Sieve primes up to SIEVE_LIMIT
    eprintln!("Sieving primes up to {}...", SIEVE_LIMIT);
    let sieve_start = Instant::now();
    let primes = sieve_primes(SIEVE_LIMIT);
    eprintln!(
        "Sieved {} primes in {:.2}s",
        primes.len(),
        sieve_start.elapsed().as_secs_f64()
    );

    let sieve_limit = SIEVE_LIMIT as u64;

    match args[1].as_str() {
        "verify" => verify_known(&primes, sieve_limit),
        "bench" => {
            println!("=== Benchmark (1M iterations each) ===");
            for &n in &[10u64, 15, 17, 19, 20, 25] {
                let start = Instant::now();
                let k_max = 1_000_000u64;
                let mut found_k = None;
                for k in 1..=k_max {
                    if check_full(n, k, &primes, sieve_limit) {
                        found_k = Some(k);
                        break;
                    }
                }
                let elapsed = start.elapsed().as_secs_f64();
                let checked = found_k.unwrap_or(k_max);
                let rate = checked as f64 / elapsed;
                match found_k {
                    Some(k) => println!("  n={:>2}: found k={} at {:.0} k/s ({:.3}s)", n, k, rate, elapsed),
                    None => println!("  n={:>2}: not found in 1M, {:.0} k/s ({:.3}s)", n, rate, elapsed),
                }
            }
        }
        "search" => {
            let n: u64 = args.get(2).expect("need n").parse().expect("n must be integer");
            let max_k: u64 = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(5_000_000_000);
            search(n, max_k, 10_000_000, &primes, sieve_limit);
        }
        "all" => {
            let start: u64 = args.get(2).expect("need start").parse().expect("integer");
            let end: u64 = args.get(3).expect("need end").parse().expect("integer");
            for n in start..=end {
                search(n, 500_000_000, 50_000_000, &primes, sieve_limit);
                println!();
            }
        }
        _ => eprintln!("Unknown command: {}", args[1]),
    }
}
