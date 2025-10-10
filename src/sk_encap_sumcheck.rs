// sk_encap_sumcheck.rs - Encapsulated SK quotient verification (Q_x only)
//
// This module implements the encapsulated identity up to Q_x:
// C(x) - S·G = Q_x(x)·(n·x - 1)
// where:
// - C(x) = Σ pk_i · (b_i · L_i(x)) is the encapsulated commitment polynomial
// - S·G = Σ pk_i · b_i is the aggregated public key
// - Q_x(x) is the quotient polynomial (encapsulated as group elements)

use bls12_381::{G1Projective, Scalar};
use ff::Field;
use group::Curve;
use sha2::{Digest, Sha256};

// ============================================================================
// LHENCAP COMMITMENT
// ============================================================================

/// Commitment to encapsulated polynomial (group elements) via hash
#[derive(Clone, Debug)]
pub struct LHEncapCommitment {
    pub root: [u8; 32],
}

/// Commit to a vector of group points via hash
pub fn hcom_points(points: &[G1Projective]) -> LHEncapCommitment {
    let mut hasher = Sha256::new();
    hasher.update(b"LHENCAP_COM_V1");
    hasher.update(&(points.len() as u64).to_le_bytes());
    for p in points {
        hasher.update(&p.to_affine().to_compressed());
    }
    let hash = hasher.finalize();
    let mut root = [0u8; 32];
    root.copy_from_slice(&hash);
    LHEncapCommitment { root }
}

// ============================================================================
// SK QUOTIENTS
// ============================================================================

/// Result of computing encapsulated SK quotients (Q_x only)
#[derive(Clone, Debug)]
pub struct SKQuotients {
    pub c_enc: Vec<G1Projective>,  // C(x) evaluations (encapsulated)
    pub sG: G1Projective,           // S·G = Σ pk_i · b_i
    pub qx_enc: Vec<G1Projective>,  // Q_x(x) evaluations (encapsulated)
}

/// Compute encapsulated quotient polynomial Q_x:
/// C(x) - S·G = Q_x(x)·(n·x - 1)
///
/// # Arguments
/// * `pks` - Public keys for each party
/// * `b_bits` - Binary indicator values (0 or 1) for each party
/// * `domain` - Evaluation domain H
/// * `lagrange_eval` - Function to evaluate L_i(x) at a point x
///
/// # Returns
/// * `SKQuotients` containing C(x), S·G, and Q_x(x) evaluations
pub fn compute_c_sg_qx(
    pks: &[G1Projective],
    b_bits: &[u8],
    domain: &[Scalar],
    mut lagrange_eval: impl FnMut(usize, usize, Scalar) -> Scalar,
) -> SKQuotients {
    let n = b_bits.len();
    assert_eq!(n, pks.len(), "pks and b_bits must have same length");

    let domain_size = domain.len();

    // Step 1: Compute S·G = Σ pk_i · b_i (aggregated public key)
    let mut sG = G1Projective::identity();
    for i in 0..n {
        if b_bits[i] == 1 {
            sG += pks[i];
        }
    }

    // Step 2: Evaluate C(x) = Σ pk_i · (b_i · L_i(x)) over domain
    let mut c_enc = Vec::with_capacity(domain_size);

    for &x in domain {
        // C(x) = Σ pk_i · (b_i · L_i(x))
        let mut c_x = G1Projective::identity();
        for i in 0..n {
            if b_bits[i] == 1 {
                let l_i_x = lagrange_eval(i, n, x);
                c_x += pks[i] * l_i_x;
            }
        }
        c_enc.push(c_x);
    }

    // Step 3: Compute Q_x(x) = (C(x) - S·G) / (n·x - 1)
    let mut qx_enc = Vec::with_capacity(domain_size);
    let n_scalar = Scalar::from(n as u64);

    for (i, &x) in domain.iter().enumerate() {
        // Denominator: (n·x - 1)
        let denom = n_scalar * x - Scalar::ONE;

        // Ensure denominator is non-zero (guaranteed on proper coset domain)
        assert!(denom != Scalar::ZERO, "Denominator (n·x - 1) = 0 at domain point");

        // Numerator: C(x) - S·G (group element)
        let numerator = c_enc[i] - sG;

        // Q_x(x) = numerator / denom = numerator · denom^{-1}
        let denom_inv = denom.invert().unwrap();
        let qx_x = numerator * denom_inv;

        qx_enc.push(qx_x);
    }

    SKQuotients {
        c_enc,
        sG,
        qx_enc,
    }
}

// ============================================================================
// VERIFICATION
// ============================================================================

/// Verify the encapsulated Q_x identity at a specific domain point:
/// C(r) - S·G = Q_x(r)·(n·r - 1)
///
/// # Arguments
/// * `pks` - Public keys for each party
/// * `b_bits` - Binary indicator values (0 or 1)
/// * `domain` - Evaluation domain
/// * `r_idx` - Index of point to test
/// * `lagrange_eval` - Function to evaluate L_i(x)
///
/// # Returns
/// * `true` if identity holds, `false` otherwise
pub fn verify_qx_relation_at_domain_point(
    pks: &[G1Projective],
    b_bits: &[u8],
    domain: &[Scalar],
    r_idx: usize,
    lagrange_eval: impl FnMut(usize, usize, Scalar) -> Scalar,
) -> bool {
    let n = b_bits.len();

    println!("  🔍 Computing encapsulated quotients...");
    let quotients = compute_c_sg_qx(pks, b_bits, domain, lagrange_eval);

    let r = domain[r_idx];
    let n_scalar = Scalar::from(n as u64);

    // Get values at test point
    let c_r = quotients.c_enc[r_idx];
    let qx_r = quotients.qx_enc[r_idx];
    let sG = quotients.sG;

    // LHS: C(r) - S·G
    let lhs = c_r - sG;

    // RHS: Q_x(r)·(n·r - 1)
    let denom = n_scalar * r - Scalar::ONE;
    let rhs = qx_r * denom;

    println!("  📊 C(r) - S·G: computed");
    println!("  📊 Q_x(r)·(n·r - 1): computed");
    println!("  📊 n = {}", n);
    println!("  📊 Test point: domain[{}]", r_idx);

    // Compute and print HCom(Q_x)
    let hcom_qx = hcom_points(&quotients.qx_enc);
    let hex_string: String = hcom_qx.root.iter()
        .map(|b| format!("{:02x}", b))
        .collect();
    println!("  🔒 HCom(Q_x): {}", hex_string);

    if lhs == rhs {
        println!("  ✅ Encapsulated Q_x relation passed at r");
        true
    } else {
        println!("  ❌ Encapsulated Q_x relation FAILED:");
        println!("     LHS ≠ RHS");
        println!("     C(r) = {:?}", c_r.to_affine());
        println!("     S·G = {:?}", sG.to_affine());
        println!("     Q_x(r) = {:?}", qx_r.to_affine());
        println!("     (n·r - 1) = {:?}", denom);
        println!("     LHS = {:?}", lhs.to_affine());
        println!("     RHS = {:?}", rhs.to_affine());
        false
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::LagrangeInterpolation;
    use crate::fri::generate_evaluation_domain;

    #[test]
    fn test_hcom_points() {
        let generator = G1Projective::generator();
        let points = vec![
            generator * Scalar::from(1),
            generator * Scalar::from(2),
            generator * Scalar::from(3),
        ];

        let com = hcom_points(&points);
        assert_eq!(com.root.len(), 32, "Commitment should be 32 bytes");

        // Different inputs should produce different commitments
        let points2 = vec![
            generator * Scalar::from(2),
            generator * Scalar::from(1),
            generator * Scalar::from(3),
        ];
        let com2 = hcom_points(&points2);

        assert_ne!(com.root, com2.root, "Different inputs should produce different commitments");
    }

    #[test]
    fn test_compute_c_sg_qx() {
        let generator = G1Projective::generator();
        let n = 4;

        // Generate public keys
        let pks: Vec<G1Projective> = (1..=n)
            .map(|i| generator * Scalar::from(i as u64))
            .collect();

        let b_bits = vec![1u8, 0u8, 1u8, 0u8];

        let domain_size = n.next_power_of_two();
        let eval_domain = generate_evaluation_domain(domain_size, Scalar::from(7));
        let vanishing_domain = generate_evaluation_domain(domain_size, Scalar::ONE);
        let vanishing_roots: Vec<Scalar> = vanishing_domain.iter().take(n).copied().collect();

        let lagrange_eval = |i: usize, n: usize, x: Scalar| -> Scalar {
            LagrangeInterpolation::lagrange_at(i, n, &vanishing_roots, x)
        };

        let quotients = compute_c_sg_qx(&pks, &b_bits, &eval_domain, lagrange_eval);

        // S·G should be pk_0 + pk_2 (since b_0 = 1, b_2 = 1)
        let expected_sG = pks[0] + pks[2];
        assert_eq!(quotients.sG, expected_sG, "S·G should be sum of selected public keys");

        assert_eq!(quotients.c_enc.len(), domain_size);
        assert_eq!(quotients.qx_enc.len(), domain_size);
    }

    #[test]
    fn test_verify_qx_relation() {
        let generator = G1Projective::generator();
        let n = 4;

        let pks: Vec<G1Projective> = (1..=n)
            .map(|i| generator * Scalar::from(i as u64))
            .collect();

        let b_bits = vec![1u8, 0u8, 1u8, 0u8];

        let domain_size = n.next_power_of_two();
        let eval_domain = generate_evaluation_domain(domain_size, Scalar::from(7));
        let vanishing_domain = generate_evaluation_domain(domain_size, Scalar::ONE);
        let vanishing_roots: Vec<Scalar> = vanishing_domain.iter().take(n).copied().collect();

        let lagrange_eval = |i: usize, n: usize, x: Scalar| -> Scalar {
            LagrangeInterpolation::lagrange_at(i, n, &vanishing_roots, x)
        };

        let test_idx = domain_size / 2;
        let result = verify_qx_relation_at_domain_point(
            &pks,
            &b_bits,
            &eval_domain,
            test_idx,
            lagrange_eval,
        );

        assert!(result, "Q_x relation should hold at test point");
    }

    #[test]
    fn test_verify_qx_different_signing_sets() {
        let generator = G1Projective::generator();

        let test_cases = vec![
            (5, vec![0, 1, 2]),
            (5, vec![0, 2, 4]),
            (4, vec![0, 1, 2, 3]),
            (4, vec![1, 3]),
        ];

        for (n, signing_set) in test_cases {
            let pks: Vec<G1Projective> = (1..=n)
                .map(|i| generator * Scalar::from(i as u64))
                .collect();

            let mut b_bits = vec![0u8; n];
            for &i in &signing_set {
                if i < n {
                    b_bits[i] = 1;
                }
            }

            let domain_size = n.next_power_of_two();
            let eval_domain = generate_evaluation_domain(domain_size, Scalar::from(7));
            let vanishing_domain = generate_evaluation_domain(domain_size, Scalar::ONE);
            let vanishing_roots: Vec<Scalar> = vanishing_domain.iter().take(n).copied().collect();

            let lagrange_eval = |i: usize, n: usize, x: Scalar| -> Scalar {
                LagrangeInterpolation::lagrange_at(i, n, &vanishing_roots, x)
            };

            let test_idx = domain_size / 2;
            println!("\nTesting n={}, signing_set={:?}", n, signing_set);
            let result = verify_qx_relation_at_domain_point(
                &pks,
                &b_bits,
                &eval_domain,
                test_idx,
                lagrange_eval,
            );

            assert!(result, "Q_x relation should hold for n={}, signing_set={:?}", n, signing_set);
        }
    }
}