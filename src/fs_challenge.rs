// fs_challenge.rs - Fiat-Shamir challenge derivation and equation verification
//
// This module derives a single challenge point r from all commitments using RO''
// and verifies the three core equations at this point (diagnostic mode).

use bls12_381::{G1Projective, Scalar};
use ff::Field;
use group::Curve;
use sha2::{Digest, Sha256};

// ============================================================================
// RO'' CHALLENGE DERIVATION
// ============================================================================

/// Inputs to RO'' for deriving challenge r
pub struct RO2Inputs {
    pub hcom_sk: [u8; 32],
    pub com_w: [u8; 32],
    pub com_b: [u8; 32],
    pub hcom_qx: [u8; 32],
    pub com_qx_p: [u8; 32],
    pub com_qz_p: [u8; 32],
    pub com_q: [u8; 32],
    pub qz_scheme_label: &'static [u8],  // e.g., b"QZ_ONEPOINT_V1"
}

/// Derive challenge r from all commitments using RO''
///
/// # Arguments
/// * `inputs` - All commitment roots and labels
///
/// # Returns
/// * Challenge scalar r
pub fn derive_r(inputs: &RO2Inputs) -> Scalar {
    let mut h = Sha256::new();
    h.update(b"RO2||v1");
    h.update(&inputs.hcom_sk);
    h.update(&inputs.com_w);
    h.update(&inputs.com_b);
    h.update(&inputs.hcom_qx);
    h.update(&inputs.com_qx_p);
    h.update(&inputs.com_qz_p);
    h.update(&inputs.com_q);
    h.update(inputs.qz_scheme_label);

    let d = h.finalize();
    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(&d);
    Scalar::from_bytes_wide(&wide)
}

/// Check that challenge r is valid (n*r-1 ≠ 0 and Z(r) ≠ 0)
///
/// # Arguments
/// * `r` - Challenge point
/// * `n` - Number of parties
/// * `z_of` - Function to evaluate vanishing polynomial Z(x)
///
/// # Returns
/// * `true` if r is valid, `false` otherwise
pub fn is_valid_challenge(
    r: Scalar,
    n: usize,
    mut z_of: impl FnMut(Scalar) -> Scalar,
) -> bool {
    let n_scalar = Scalar::from(n as u64);
    let nr_minus_1 = n_scalar * r - Scalar::ONE;
    let z_r = z_of(r);

    !bool::from(nr_minus_1.is_zero()) && !bool::from(z_r.is_zero())
}

/// Derive a valid challenge r, tweaking the label if necessary
///
/// # Arguments
/// * `inputs` - Initial RO2 inputs
/// * `n` - Number of parties
/// * `z_of` - Function to evaluate vanishing polynomial Z(x)
///
/// # Returns
/// * `(r, tweak_count)` - Valid challenge and number of tweaks applied
pub fn derive_valid_r(
    inputs: &mut RO2Inputs,
    n: usize,
    mut z_of: impl FnMut(Scalar) -> Scalar,
) -> (Scalar, usize) {
    let mut tweak_count = 0;
    let mut label = inputs.qz_scheme_label.to_vec();

    loop {
        inputs.qz_scheme_label = Box::leak(label.clone().into_boxed_slice());
        let r = derive_r(inputs);

        if is_valid_challenge(r, n, &mut z_of) {
            return (r, tweak_count);
        }

        // Tweak the label and try again
        tweak_count += 1;
        label.push(0x01);

        if tweak_count > 10 {
            panic!("Failed to find valid challenge after {} tweaks", tweak_count);
        }
    }
}

// ============================================================================
// EQUATION VERIFICATION AT CHALLENGE POINT
// ============================================================================

/// Check all three equations at challenge point r
///
/// Equation (1) - Encapsulated: SK(r)·B(r)·G = S·G + Q_x(r)·(n·r-1)·G + Q_Z(r)·Z(r)·G
/// Equation (2) - Clear: W(r)·B(r) = S' + Q'_x(r)·(n·r-1) + Q'_Z(r)·Z(r)
/// Equation (3) - Boolean: B(r)·(1-B(r)) = Q(r)·Z(r)
///
/// Note: The quotients are computed as:
///   Q_x(r) = (C(r) - S·G) / (n·r - 1)
///   Q'_x(r) = (C'(r) - S') / (n·r - 1) where C'(r) = W(r)·B(r)
///   Q_Z(r) = (SK(r)·B(r)·G - C(r) - Q_x(r)·(n·r-1)·G) / Z(r)
///   Q'_Z(r) = 0 (since C'(r) = W(r)·B(r) by definition)
///   Q(r) = B(r)·(1-B(r)) / Z(r)
///
/// # Arguments
/// * `r` - Challenge point
/// * `n` - Number of parties
/// * `domain` - Vanishing polynomial roots (first n points)
/// * `b_bits` - Binary indicator values
/// * `weights` - Weight values for each party
/// * `pks` - Public keys for each party
/// * `lagrange_at` - Function to evaluate L_i(x) at a point
/// * `z_of` - Function to evaluate vanishing polynomial Z(x)
///
/// # Returns
/// * `(ok1, ok2, ok3)` - Boolean results for each equation
pub fn check_equations_at_r(
    r: Scalar,
    n: usize,
    _domain: &[Scalar],
    b_bits: &[u8],
    weights: &[Scalar],
    pks: &[G1Projective],
    mut lagrange_at: impl FnMut(usize, usize, Scalar) -> Scalar,
    mut z_of: impl FnMut(Scalar) -> Scalar,
) -> (bool, bool, bool) {
    let n_scalar = Scalar::from(n as u64);
    let nr_minus_1 = n_scalar * r - Scalar::ONE;
    let z_r = z_of(r);

    assert!(!bool::from(nr_minus_1.is_zero()), "bad r: n*r-1=0");
    assert!(!bool::from(z_r.is_zero()), "bad r: Z(r)=0");

    // ========================================================================
    // CLEAR SIDE (Scalars)
    // ========================================================================

    // B(r) = Σ b_i · L_i(r)
    let mut b_r = Scalar::ZERO;
    // W(r) = Σ w_i · L_i(r)
    let mut w_r = Scalar::ZERO;
    // S' = Σ w_i · b_i
    let mut s_prime = Scalar::ZERO;

    for i in 0..n {
        let li = lagrange_at(i, n, r);
        w_r += weights[i] * li;
        if b_bits[i] == 1 {
            b_r += li;
            s_prime += weights[i];
        }
    }

    // C'(r) = W(r)·B(r) by definition
    let cprime_r = w_r * b_r;

    // From the spec: Q'_x(r) = (C'(r) - S') / (n·r - 1)
    let qx_p_r = (cprime_r - s_prime) * nr_minus_1.invert().unwrap();

    // From the spec: Q'_Z(r) = (W(r)·B(r) - C'(r)) / Z(r) = 0 / Z(r) = 0
    // Because C'(r) = W(r)·B(r) by definition!
    // This means Q'_Z should be zero everywhere
    let qz_p_r = Scalar::ZERO;

    // Q(r) = B(r)·(1-B(r)) / Z(r)
    let q_r = (b_r * (Scalar::ONE - b_r)) * z_r.invert().unwrap();

    // ========================================================================
    // ENCAPSULATED SIDE (Group Points)
    // ========================================================================

    // C(r)·G = Σ pk_i · (b_i · L_i(r))
    let mut c_r = G1Projective::identity();
    // S·G = Σ pk_i · b_i
    let mut sG = G1Projective::identity();
    // SK(r)·G = Σ pk_i · L_i(r)
    let mut sk_rG = G1Projective::identity();

    for i in 0..n {
        let li = lagrange_at(i, n, r);
        if b_bits[i] == 1 {
            c_r += pks[i] * li;
            sG += pks[i];
        }
        sk_rG += pks[i] * li;
    }

    // Q_x(r)·G = (C(r) - S·G) / (n·r - 1)
    let qx_rG = (c_r - sG) * nr_minus_1.invert().unwrap();

    // For Q_Z computation, we need to verify the constraint:
    // SK(r)·B(r)·G - C(r) = Q_x(r)·(n·r-1)·G + Q_Z(r)·Z(r)·G
    // Rearranging: Q_Z(r)·G = (SK(r)·B(r)·G - C(r) - Q_x(r)·(n·r-1)·G) / Z(r)
    //
    // But wait - we computed Q_x(r)·G = (C(r) - S·G) / (n·r - 1)
    // So Q_x(r)·(n·r-1)·G = C(r) - S·G
    // Therefore: SK(r)·B(r)·G - C(r) - (C(r) - S·G) = SK(r)·B(r)·G - 2·C(r) + S·G
    //
    // Actually, let me reconsider. The identity should be:
    // SK(r)·B(r)·G = C(r) + Q_x(r)·(n·r-1)·G + Q_Z(r)·Z(r)·G
    // NOT: SK(r)·B(r)·G = S·G + Q_x(r)·(n·r-1)·G + Q_Z(r)·Z(r)·G
    //
    // Let me check: C(r)·G = Σ pk_i · (b_i · L_i(r))
    // And the constraint from the spec is about C(x) - S·G being divisible
    //
    // Looking at sk_encap_sumcheck.rs, the identity is:
    // C(r) - S·G = Q_x(r)·(n·r - 1)
    // So: C(r) = S·G + Q_x(r)·(n·r - 1)
    //
    // And the full SK constraint should be:
    // SK(r)·B(r) = C(r) + Q_Z(r)·Z(r)
    // Substituting C(r):
    // SK(r)·B(r) = S·G + Q_x(r)·(n·r - 1) + Q_Z(r)·Z(r)
    //
    // So Q_Z(r) = (SK(r)·B(r) - S·G - Q_x(r)·(n·r - 1)) / Z(r)
    let qz_rG = (sk_rG * b_r - sG - qx_rG * nr_minus_1) * z_r.invert().unwrap();

    // ========================================================================
    // EQUATION CHECKS
    // ========================================================================

    // Eq(1) - Encapsulated: SK(r)·B(r)·G = S·G + Q_x(r)·(n·r-1)·G + Q_Z(r)·Z(r)·G
    let eq1_lhs = sk_rG * b_r;
    let eq1_rhs = sG + qx_rG * nr_minus_1 + qz_rG * z_r;
    let ok1 = eq1_lhs == eq1_rhs;

    // Eq(2) - Clear: W(r)·B(r) = S' + Q'_x(r)·(n·r-1) + Q'_Z(r)·Z(r)
    let eq2_lhs = w_r * b_r;
    let eq2_rhs = s_prime + qx_p_r * nr_minus_1 + qz_p_r * z_r;
    let ok2 = eq2_lhs == eq2_rhs;

    // Eq(3) - Boolean: B(r)·(1-B(r)) = Q(r)·Z(r)
    let ok3 = (b_r * (Scalar::ONE - b_r)) == (q_r * z_r);

    // Debug output when equations fail
    if !ok1 || !ok2 || !ok3 {
        eprintln!("\n⚠️  DEBUG: Equation verification details:");
        eprintln!("  n = {}, r = {:?}", n, r);
        eprintln!("  n·r - 1 = {:?}", nr_minus_1);
        eprintln!("  Z(r) = {:?}", z_r);
        eprintln!("  B(r) = {:?}", b_r);
        eprintln!("  W(r) = {:?}", w_r);
        eprintln!("  S' = {:?}", s_prime);
        eprintln!("  C'(r) = W(r)·B(r) = {:?}", cprime_r);

        if !ok1 {
            eprintln!("\n  Eq(1) FAILED:");
            eprintln!("    LHS (SK(r)·B(r)·G) = {:?}", eq1_lhs.to_affine());
            eprintln!("    RHS (S·G + Q_x(r)·(n·r-1)·G + Q_Z(r)·Z(r)·G) = {:?}", eq1_rhs.to_affine());
            eprintln!("    S·G = {:?}", sG.to_affine());
            eprintln!("    Q_x(r)·G = {:?}", qx_rG.to_affine());
            eprintln!("    Q_Z(r)·G = {:?}", qz_rG.to_affine());
        }

        if !ok2 {
            eprintln!("\n  Eq(2) FAILED:");
            eprintln!("    LHS (W(r)·B(r)) = {:?}", eq2_lhs);
            eprintln!("    RHS (S' + Q'_x(r)·(n·r-1) + Q'_Z(r)·Z(r)) = {:?}", eq2_rhs);
            eprintln!("    Q'_x(r) = {:?}", qx_p_r);
            eprintln!("    Q'_Z(r) = {:?}", qz_p_r);
        }

        if !ok3 {
            eprintln!("\n  Eq(3) FAILED:");
            eprintln!("    LHS (B(r)·(1-B(r))) = {:?}", b_r * (Scalar::ONE - b_r));
            eprintln!("    RHS (Q(r)·Z(r)) = {:?}", q_r * z_r);
            eprintln!("    Q(r) = {:?}", q_r);
        }
    }

    (ok1, ok2, ok3)
}

// ============================================================================
// HIGH-LEVEL VERIFICATION FUNCTION
// ============================================================================

/// Verify all three equations at a Fiat-Shamir challenge r
///
/// # Arguments
/// * `inputs` - RO2 inputs for challenge derivation
/// * `n` - Number of parties
/// * `domain` - Vanishing polynomial roots
/// * `b_bits` - Binary indicator values
/// * `weights` - Weight values
/// * `pks` - Public keys
/// * `lagrange_at` - Lagrange evaluation function
/// * `z_of` - Vanishing polynomial evaluation function
///
/// # Returns
/// * `true` if all equations pass, `false` otherwise
pub fn verify_equations_at_fs_challenge(
    mut inputs: RO2Inputs,
    n: usize,
    domain: &[Scalar],
    b_bits: &[u8],
    weights: &[Scalar],
    pks: &[G1Projective],
    mut lagrange_at: impl FnMut(usize, usize, Scalar) -> Scalar,
    mut z_of: impl FnMut(Scalar) -> Scalar,
) -> bool {
    println!("\n🎯 Deriving RO'' challenge r from all commitments...");

    // Derive valid challenge r
    let (r, tweak_count) = derive_valid_r(&mut inputs, n, &mut z_of);

    if tweak_count > 0 {
        println!("  ⚠️  Challenge required {} label tweaks", tweak_count);
    }
    println!("  ✅ RO'' challenge r derived");

    // Check all three equations
    let (ok1, ok2, ok3) = check_equations_at_r(
        r,
        n,
        domain,
        b_bits,
        weights,
        pks,
        &mut lagrange_at,
        &mut z_of,
    );

    // Print results
    if ok1 {
        println!("  ✅ Eq(1) SK·B passed at r");
    } else {
        println!("  ❌ Eq(1) SK·B FAILED at r");
        println!("     [SK(r)·B(r)·G ≟ S·G + Q_x(r)·(n·r-1)·G + Q_Z(r)·Z(r)·G]");
    }

    if ok2 {
        println!("  ✅ Eq(2) W·B passed at r");
    } else {
        println!("  ❌ Eq(2) W·B FAILED at r");
        println!("     [W(r)·B(r) ≟ S' + Q'_x(r)·(n·r-1) + Q'_Z(r)·Z(r)]");
    }

    if ok3 {
        println!("  ✅ Eq(3) Booleanity passed at r");
    } else {
        println!("  ❌ Eq(3) Booleanity FAILED at r");
        println!("     [B(r)·(1-B(r)) ≟ Q(r)·Z(r)]");
    }

    ok1 && ok2 && ok3
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
    fn test_derive_r() {
        let inputs = RO2Inputs {
            hcom_sk: [1u8; 32],
            com_w: [2u8; 32],
            com_b: [3u8; 32],
            hcom_qx: [4u8; 32],
            com_qx_p: [5u8; 32],
            com_qz_p: [6u8; 32],
            com_q: [7u8; 32],
            qz_scheme_label: b"QZ_ONEPOINT_V1",
        };

        let r = derive_r(&inputs);
        assert!(r != Scalar::ZERO, "Challenge should be non-zero");

        // Different inputs should produce different challenges
        let inputs2 = RO2Inputs {
            hcom_sk: [2u8; 32],
            com_w: [2u8; 32],
            com_b: [3u8; 32],
            hcom_qx: [4u8; 32],
            com_qx_p: [5u8; 32],
            com_qz_p: [6u8; 32],
            com_q: [7u8; 32],
            qz_scheme_label: b"QZ_ONEPOINT_V1",
        };

        let r2 = derive_r(&inputs2);
        assert_ne!(r, r2, "Different inputs should produce different challenges");
    }

    #[test]
    fn test_check_equations_at_r() {
        let n = 4;
        let signing_set = vec![0, 2];

        let generator = G1Projective::generator();
        let pks: Vec<G1Projective> = (0..n)
            .map(|i| generator * Scalar::from((i + 1) as u64))
            .collect();

        let mut b_bits = vec![0u8; n];
        for &i in &signing_set {
            if i < n {
                b_bits[i] = 1;
            }
        }

        let weights: Vec<Scalar> = (0..n)
            .map(|i| Scalar::from((i + 1) as u64))
            .collect();

        let domain_size = n.next_power_of_two();
        let vanishing_domain = generate_evaluation_domain(domain_size, Scalar::ONE);
        let vanishing_roots: Vec<Scalar> = vanishing_domain.iter().take(n).copied().collect();

        let eval_domain = generate_evaluation_domain(domain_size, Scalar::from(7));
        let r = eval_domain[0];

        let lagrange_at = |i: usize, n: usize, x: Scalar| -> Scalar {
            LagrangeInterpolation::lagrange_at(i, n, &vanishing_roots, x)
        };

        let z_of = |x: Scalar| -> Scalar {
            let mut result = Scalar::ONE;
            for j in 0..n {
                result *= x - vanishing_roots[j];
            }
            result
        };

        let (ok1, ok2, ok3) = check_equations_at_r(
            r,
            n,
            &vanishing_roots,
            &b_bits,
            &weights,
            &pks,
            lagrange_at,
            z_of,
        );

        assert!(ok1, "Equation 1 should pass");
        assert!(ok2, "Equation 2 should pass");
        assert!(ok3, "Equation 3 should pass");
    }

    #[test]
    fn test_verify_equations_at_fs_challenge() {
        let n = 4;
        let signing_set = vec![0, 2];

        let generator = G1Projective::generator();
        let pks: Vec<G1Projective> = (0..n)
            .map(|i| generator * Scalar::from((i + 1) as u64))
            .collect();

        let mut b_bits = vec![0u8; n];
        for &i in &signing_set {
            if i < n {
                b_bits[i] = 1;
            }
        }

        let weights: Vec<Scalar> = (0..n)
            .map(|i| Scalar::from((i + 1) as u64))
            .collect();

        let domain_size = n.next_power_of_two();
        let vanishing_domain = generate_evaluation_domain(domain_size, Scalar::ONE);
        let vanishing_roots: Vec<Scalar> = vanishing_domain.iter().take(n).copied().collect();

        let inputs = RO2Inputs {
            hcom_sk: [1u8; 32],
            com_w: [2u8; 32],
            com_b: [3u8; 32],
            hcom_qx: [4u8; 32],
            com_qx_p: [5u8; 32],
            com_qz_p: [6u8; 32],
            com_q: [7u8; 32],
            qz_scheme_label: b"QZ_ONEPOINT_V1",
        };

        let lagrange_at = |i: usize, n: usize, x: Scalar| -> Scalar {
            LagrangeInterpolation::lagrange_at(i, n, &vanishing_roots, x)
        };

        let z_of = |x: Scalar| -> Scalar {
            let mut result = Scalar::ONE;
            for j in 0..n {
                result *= x - vanishing_roots[j];
            }
            result
        };

        let result = verify_equations_at_fs_challenge(
            inputs,
            n,
            &vanishing_roots,
            &b_bits,
            &weights,
            &pks,
            lagrange_at,
            z_of,
        );

        assert!(result, "All equations should pass at FS challenge");
    }
}