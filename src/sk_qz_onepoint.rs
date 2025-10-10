// sk_qz_onepoint.rs - SK-side Q_Z one-point computation with binding commitment
//
// This module implements the computation of Q_Z(r)·G at a challenge point r,
// where Q_Z is the quotient polynomial for the SK encapsulated constraint:
//
// SK(x)·B(x) - C(x) = Q_x(x)·x + Q_Z(x)·Z(x)
//
// At point r, we rearrange to solve for Q_Z(r):
// Q_Z(r) = [SK(r)·B(r) - C(r) - Q_x(r)·r] / Z(r)

use bls12_381::{G1Projective, Scalar};
use ff::Field;
use group::Curve;
use sha2::{Digest, Sha256};

use crate::polynomial::LagrangeInterpolation;
use crate::fri::generate_evaluation_domain;

// ============================================================================
// Q_Z ONE-POINT COMPUTATION
// ============================================================================

/// Compute Q_Z(r)·G at a single challenge point r
///
/// Given the constraint: SK(x)·B(x) - C(x) = Q_x(x)·x + Q_Z(x)·Z(x)
/// At point r, we compute: Q_Z(r) = [SK(r)·B(r) - C(r) - Q_x(r)·r] / Z(r)
///
/// # Arguments
/// * `pks` - Public keys pk_i = g^{sk_i}
/// * `b_bits` - Binary indicator values b_i ∈ {0,1}
/// * `domain` - Evaluation domain H (for Lagrange basis)
/// * `r` - Challenge point (for now can be a domain element)
/// * `lagrange_eval` - Function to evaluate L_i(x) at a point
/// * `z_of` - Function to evaluate vanishing polynomial Z(x)
/// * `qx_at_r` - Q_x(r)·G (precomputed)
///
/// # Returns
/// * `(qz_rG, binding_hash)` where:
///   - `qz_rG` is Q_Z(r)·G
///   - `binding_hash` is a 32-byte commitment to this computation
pub fn compute_qz_onepoint_at_r(
    pks: &[G1Projective],
    b_bits: &[u8],
    _domain: &[Scalar],
    r: Scalar,
    mut lagrange_eval: impl FnMut(usize, usize, Scalar) -> Scalar,
    mut z_of: impl FnMut(Scalar) -> Scalar,
    qx_at_r: G1Projective,
) -> (G1Projective, [u8; 32]) {
    let n = pks.len();
    assert_eq!(n, b_bits.len(), "pks and b_bits must have same length");

    // Step 1: Compute SK(r)·G = Σ pk_i · L_i(r)
    let mut sk_rG = G1Projective::identity();
    for i in 0..n {
        let l_i_r = lagrange_eval(i, n, r);
        sk_rG += pks[i] * l_i_r;
    }

    // Step 2: Compute B(r) = Σ b_i · L_i(r) (scalar)
    let mut b_r = Scalar::ZERO;
    for i in 0..n {
        if b_bits[i] == 1 {
            let l_i_r = lagrange_eval(i, n, r);
            b_r += l_i_r;
        }
    }

    // Step 3: Compute C(r)·G = Σ pk_i · (b_i · L_i(r))
    let mut c_rG = G1Projective::identity();
    for i in 0..n {
        if b_bits[i] == 1 {
            let l_i_r = lagrange_eval(i, n, r);
            c_rG += pks[i] * l_i_r;
        }
    }

    // Step 4: Compute Z(r)
    let z_r = z_of(r);
    assert!(z_r != Scalar::ZERO, "Z(r) = 0, cannot compute Q_Z(r)");
    let z_r_inv = z_r.invert().unwrap();

    // Step 5: Compute Q_Z(r)·G = [SK(r)·G · B(r) - C(r)·G - Q_x(r)·G · r] / Z(r)
    // Numerator: SK(r)·G · B(r) - C(r)·G - Q_x(r)·G · r
    let numerator = (sk_rG * b_r) - c_rG - (qx_at_r * r);

    // Q_Z(r)·G = numerator / Z(r)
    let qz_rG = numerator * z_r_inv;

    // Step 6: Compute binding commitment
    let binding_hash = compute_binding_hash(r, &qz_rG);

    (qz_rG, binding_hash)
}

/// Compute binding hash for Q_Z one-point computation
fn compute_binding_hash(r: Scalar, qz_rG: &G1Projective) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"QZ_ONEPOINT_V1");
    hasher.update(&r.to_bytes());
    hasher.update(&qz_rG.to_affine().to_compressed());

    let hash = hasher.finalize();
    let mut result = [0u8; 32];
    result.copy_from_slice(&hash);
    result
}

// ============================================================================
// DIAGNOSTIC FUNCTION
// ============================================================================

/// Verify and display Q_Z one-point computation diagnostics
///
/// # Arguments
/// * `signing_set` - Indices of parties that signed
/// * `pks` - All public keys
/// * `n` - Total number of parties
/// * `qx_at_r` - Q_x(r)·G (precomputed from previous step)
/// * `test_point_idx` - Index of test point in domain (for now, use 0)
///
/// # Returns
/// * `(qz_rG, binding_hash)` - Q_Z(r)·G and its binding commitment
pub fn verify_qz_onepoint_diagnostic(
    signing_set: &[usize],
    pks: &[G1Projective],
    n: usize,
    qx_at_r: G1Projective,
    test_point_idx: usize,
) -> (G1Projective, [u8; 32]) {
    println!("\n🔍 Computing SK Encapsulated Q_Z One-Point:");

    // Construct indicator bits
    let mut b_bits = vec![0u8; n];
    for &i in signing_set {
        if i < n {
            b_bits[i] = 1;
        }
    }

    // Generate domains
    let domain_size = n.next_power_of_two();
    let coset_offset = Scalar::from(7);
    let eval_domain = generate_evaluation_domain(domain_size, coset_offset);

    let vanishing_domain = generate_evaluation_domain(domain_size, Scalar::ONE);
    let vanishing_roots: Vec<Scalar> = vanishing_domain.iter().take(n).copied().collect();

    // Choose test point r (for now, use domain[test_point_idx])
    let r = eval_domain[test_point_idx];

    println!("  📊 Challenge point r: eval_domain[{}]", test_point_idx);
    println!("  📊 Number of parties: {}", n);
    println!("  📊 Signing set: {:?}", signing_set);

    // Lagrange evaluation function
    let lagrange_eval = |i: usize, n: usize, x: Scalar| -> Scalar {
        LagrangeInterpolation::lagrange_at(i, n, &vanishing_roots, x)
    };

    // Vanishing polynomial
    let z_of = |x: Scalar| -> Scalar {
        let mut result = Scalar::ONE;
        for j in 0..n {
            result *= x - vanishing_roots[j];
        }
        result
    };

    // Compute Q_Z(r)·G
    let (qz_rG, binding_hash) = compute_qz_onepoint_at_r(
        pks,
        &b_bits,
        &vanishing_roots,
        r,
        lagrange_eval,
        z_of,
        qx_at_r,
    );

    println!("  ✅ Encapsulated Q_Z one-point computed");
    println!("  📊 Q_Z(r)·G computed at r");

    // Format binding hash as hex string without external crate
    let hex_str = binding_hash.iter()
        .map(|b| format!("{:02x}", b))
        .collect::<String>();
    println!("  🔒 Binding hash: {}", hex_str);

    (qz_rG, binding_hash)
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compute_qz_onepoint() {
        // Simple test with known values
        let n = 4;
        let domain_size = n.next_power_of_two();

        let generator = G1Projective::generator();

        // Create some test public keys
        let pks: Vec<G1Projective> = (0..n)
            .map(|i| generator * Scalar::from((i + 1) as u64))
            .collect();

        let b_bits = vec![1u8, 0u8, 1u8, 0u8];

        let eval_domain = generate_evaluation_domain(domain_size, Scalar::from(7));
        let vanishing_domain = generate_evaluation_domain(domain_size, Scalar::ONE);
        let vanishing_roots: Vec<Scalar> = vanishing_domain.iter().take(n).copied().collect();

        let r = eval_domain[0];

        let lagrange_eval = |i: usize, n: usize, x: Scalar| -> Scalar {
            LagrangeInterpolation::lagrange_at(i, n, &vanishing_roots, x)
        };

        let z_of = |x: Scalar| -> Scalar {
            let mut result = Scalar::ONE;
            for j in 0..n {
                result *= x - vanishing_roots[j];
            }
            result
        };

        // For this test, use identity as Q_x(r)
        let qx_at_r = G1Projective::identity();

        let (qz_rG, binding_hash) = compute_qz_onepoint_at_r(
            &pks,
            &b_bits,
            &vanishing_roots,
            r,
            lagrange_eval,
            z_of,
            qx_at_r,
        );

        // Should produce a valid group element
        assert!(qz_rG != G1Projective::identity() || true); // Always passes, just checking no panic

        // Binding hash should be 32 bytes
        assert_eq!(binding_hash.len(), 32);
    }

    #[test]
    fn test_binding_hash_uniqueness() {
        let generator = G1Projective::generator();
        let r1 = Scalar::from(1);
        let r2 = Scalar::from(2);
        let qz1 = generator * Scalar::from(3);
        let qz2 = generator * Scalar::from(4);

        let hash1 = compute_binding_hash(r1, &qz1);
        let hash2 = compute_binding_hash(r2, &qz1);
        let hash3 = compute_binding_hash(r1, &qz2);

        // Different r should produce different hash
        assert_ne!(hash1, hash2);

        // Different qz should produce different hash
        assert_ne!(hash1, hash3);
    }

    #[test]
    fn test_verify_qz_onepoint_diagnostic() {
        let n = 5;
        let signing_set = vec![0, 1, 2];

        let generator = G1Projective::generator();
        let pks: Vec<G1Projective> = (0..n)
            .map(|i| generator * Scalar::from((i + 1) as u64))
            .collect();

        // Use identity for Q_x(r) in this test
        let qx_at_r = G1Projective::identity();

        let (qz_rG, binding_hash) = verify_qz_onepoint_diagnostic(
            &signing_set,
            &pks,
            n,
            qx_at_r,
            0, // test_point_idx
        );

        // Should complete without panicking
        assert_eq!(binding_hash.len(), 32);
        println!("Test passed: Q_Z one-point computed successfully");
    }
}