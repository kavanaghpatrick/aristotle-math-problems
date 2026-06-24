// Erdős 647 segmented τ-sieve (reduction-free, self-checking).
//
// Decides: does some n > 24 with lo < n ≤ hi satisfy
//     max_{0 ≤ m < n} ( m + τ(m) ) ≤ n + 2 ?     (τ = number of divisors = σ_0)
//
// Method: single monotone pass. Maintain running_max = max over all m seen of (m + τ(m)).
// n is a witness iff running_max(over k < n) ≤ n + 2. Witnesses are exactly the n where the
// running max has not yet overshot n+2. running_max is monotone nondecreasing.
//
// τ(m) per segment: classic segmented factor-count sieve. For each prime p ≤ √hi, strike its
// multiples in [lo, hi), extract the full p-adic valuation a, multiply the divisor count by (a+1);
// a remaining cofactor > 1 (a single prime > √hi) contributes one more factor (×2). Reduction-free.
//
// Usage: e647_sieve <lo> <hi> [--seg N] [--seed-runmax R] [--start S]
//   lo, hi, N, R, S accept "1e10" / "1.2e9" / plain integers.
//   <lo> = report floor: witnesses are reported for n in (lo, hi].
//   --start S : first m actually sieved (default = lo+1, i.e. assume seed covers m ≤ lo).
//   --seed-runmax R : running_max over all m ≤ lo, computed by a prior run. REQUIRED for soundness
//       when start > 2, because the predicate needs the max over ALL k < n.
//   Validation run starts at 2 with seed 0 and prints running_max at hi (feed it forward).

use std::env;
use std::io::Write;

const WINDOW: u64 = 12_000; // certificate window; live τ tripwire fires at τ ≥ WINDOW-2.

fn parse_num(s: &str) -> u64 {
    if let Some(idx) = s.find(['e', 'E']) {
        let mant: f64 = s[..idx].parse().expect("bad mantissa");
        let exp: i32 = s[idx + 1..].parse().expect("bad exponent");
        (mant * 10f64.powi(exp)).round() as u64
    } else {
        s.parse().expect("bad integer")
    }
}

fn primes_up_to(limit: u64) -> Vec<u64> {
    let limit = limit as usize;
    let mut is_comp = vec![false; limit + 1];
    let mut ps = Vec::new();
    let mut i = 2usize;
    while i <= limit {
        if !is_comp[i] {
            ps.push(i as u64);
            let mut j = i * i;
            while j <= limit {
                is_comp[j] = true;
                j += i;
            }
        }
        i += 1;
    }
    ps
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: e647_sieve <lo> <hi> [--seg N] [--seed-runmax R] [--start S]");
        std::process::exit(2);
    }
    let report_lo = parse_num(&args[1]);
    let hi = parse_num(&args[2]);
    let mut seg: u64 = 1 << 26; // ~67M
    let mut seed_runmax: u64 = 0;
    let mut start: u64 = 2;
    let mut start_set = false;
    let mut i = 3;
    while i < args.len() {
        match args[i].as_str() {
            "--seg" => { seg = parse_num(&args[i + 1]); i += 2; }
            "--seed-runmax" => { seed_runmax = parse_num(&args[i + 1]); i += 2; }
            "--start" => { start = parse_num(&args[i + 1]); start_set = true; i += 2; }
            other => { eprintln!("unknown arg {other}"); std::process::exit(2); }
        }
    }
    // If a seed running-max is supplied and no explicit start, assume the seed covers m ≤ report_lo.
    if seed_runmax > 0 && !start_set {
        start = report_lo + 1;
    }

    let root = (hi as f64).sqrt() as u64 + 2;
    let base_primes = primes_up_to(root);
    eprintln!(
        "[e647] primes ≤ √hi={} : {}. seg={}. sieve m∈[{},{}). report n∈({},{}]. seed_runmax={}.",
        root, base_primes.len(), seg, start, hi, report_lo, hi, seed_runmax
    );

    let stdout = std::io::stdout();
    let mut out = stdout.lock();

    let mut running_max: u64 = seed_runmax;
    let mut witnesses: Vec<u64> = Vec::new();
    let mut global_max_tau: u32 = 0;
    let mut min_margin: i64 = i64::MAX; // min over reported n of (running_max - (n+2)); ≤0 ⟺ a witness

    let mut lo_seg = start;
    let mut progress_next = start;
    while lo_seg < hi {
        let hi_seg = (lo_seg + seg).min(hi);
        let len = (hi_seg - lo_seg) as usize;

        let mut tau = vec![1u32; len];
        let mut rem: Vec<u64> = (0..len as u64).map(|k| lo_seg + k).collect();

        for &p in &base_primes {
            if p * p > hi_seg {
                break;
            }
            let first = (lo_seg + p - 1) / p * p; // least multiple of p that is ≥ lo_seg
            let mut x = first;
            while x < hi_seg {
                let idx = (x - lo_seg) as usize;
                let mut a = 0u32;
                while rem[idx] % p == 0 {
                    rem[idx] /= p;
                    a += 1;
                }
                tau[idx] *= a + 1;
                x += p;
            }
        }

        let mut seg_max_tau: u32 = 0;
        for idx in 0..len {
            if rem[idx] > 1 {
                tau[idx] *= 2; // one leftover prime > √hi
            }
            if tau[idx] > seg_max_tau {
                seg_max_tau = tau[idx];
            }
        }
        if seg_max_tau > global_max_tau {
            global_max_tau = seg_max_tau;
        }
        if (seg_max_tau as u64) >= WINDOW - 2 {
            let _ = writeln!(
                out,
                "[HALT] segment [{},{}) max τ={} ≥ WINDOW-2={}. Widen WINDOW and rerun.",
                lo_seg, hi_seg, seg_max_tau, WINDOW - 2
            );
            let _ = out.flush();
            std::process::exit(3);
        }

        for idx in 0..len {
            let m = lo_seg + idx as u64;
            let v = m + tau[idx] as u64;
            if v > running_max {
                running_max = v;
            }
            let n = m + 1; // running_max now covers all k < n
            // Witness floor: the problem requires n > 24; we report n in (report_lo, hi].
            // For the production run report_lo ≥ 24 enforces n > 24. For validation set report_lo
            // small (e.g. 4) to reproduce the published small witnesses 5,6,8,10,12,24.
            if n > report_lo && n <= hi {
                let margin = running_max as i64 - (n as i64 + 2);
                if margin < min_margin {
                    min_margin = margin;
                }
                if running_max <= n + 2 {
                    witnesses.push(n);
                    let _ = writeln!(out, "[WITNESS] n={} (running_max={} ≤ n+2={})", n, running_max, n + 2);
                    let _ = out.flush();
                }
            }
        }

        if hi_seg >= progress_next {
            let _ = writeln!(
                out,
                "[progress] m={} | running_max={} | global_max_τ={} | min(running_max-(n+2))={}",
                hi_seg, running_max, global_max_tau, if min_margin == i64::MAX { 0 } else { min_margin }
            );
            let _ = out.flush();
            progress_next = hi_seg + 1_000_000_000;
        }

        lo_seg = hi_seg;
    }

    let _ = writeln!(
        out,
        "[done] reported n∈({},{}]: witnesses={:?}. running_max(at hi)={}. global_max_τ={}. min(running_max-(n+2))={} (≤0 ⟺ witness).",
        report_lo, hi, witnesses, running_max, global_max_tau,
        if min_margin == i64::MAX { 0 } else { min_margin }
    );
    let _ = out.flush();
}
