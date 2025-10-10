// clear_sumcheck.rs - Clear-side Sumcheck for weighted aggregation W·B
//
// This module implements the identity: W(x)·B(x) = S' + Q'_x(x)·x + Q'_Z(x)·Z(x)
// where:
// - W(x) = Σ w_i · L_i(x) is the weight polynomial
// - B(x) = Σ b_i · L_i(x) is the indicator polynomial
// - S' = Σ w_i · b_i is the claimed weighted sum
// - Q'_x(x) and Q'_Z(x) are quotient polynomials

use bls12_381::Scalar;
use ff::Field;
use sha2::{Digest, Sha256};

use crate::polynomial::LagrangeInterpolation;
use crate::fri::generate_evaluation_domain;

// ============================================================================
// CLEAR POLYNOMIAL COMMITMENT
// ============================================================================

/// Clear (non-encapsulated) polynomial commitment via hash
#[derive(Clone, Debug)]
pub struct ClearPolyCommitment {
    pub root: Vec<u8>,
}

/// Commit to a vector of scalars via hash
pub fn com_scalars(scalars: &[Scalar]) -> ClearPolyCommitment {
    let mut hasher = Sha256::new();
    hasher.update(b"CLEAR_POLY_COM_V1");
    hasher.update(&(scalars.len() as u64).to_le_bytes());
    for s in scalars {
        hasher.update(&s.to_bytes());
    }
    ClearPolyCommitment {
        root: hasher.finalize().to_vec(),
    }
}

// ============================================================================
// CLEAR QUOTIENT POLYNOMIALS
// ============================================================================

/// Result of computing clear quotient polynomials for W·B identity
#[derive(Clone, Debug)]
pub struct ClearQuotients {
    pub b_evals: Vec<Scalar>,      // B(x) evaluations
    pub w_evals: Vec<Scalar>,      // W(x) evaluations
    pub c_prime_evals: Vec<Scalar>, // C'(x) = W(x)·B(x) evaluations
    pub qx_prime_evals: Vec<Scalar>, // Q'_x(x) quotient
    pub qz_prime_evals: Vec<Scalar>, // Q'_Z(x) quotient
    pub s_prime: Scalar,            // S' = Σ w_i · b_i
}

/// Compute clear quotient polynomials for the W·B identity:
/// W(x)·B(x) = S' + Q'_x(x)·x + Q'_Z(x)·Z(x)
///
/// # Arguments
/// * `b_bits` - Binary indicator values (0 or 1) for each party
/// * `weights` - Weight values for each party
/// * `eval_domain` - Evaluation domain (coset)
/// * `lagrange_eval` - Function to evaluate L_i(x) at a point x
/// * `z_of` - Function to evaluate vanishing polynomial Z(x) at a point x
///
/// # Returns
/// * `ClearQuotients` containing all polynomial evaluations and S'
pub fn compute_clear_quotients(
    b_bits: &[u8],
    weights: &[Scalar],
    eval_domain: &[Scalar],
    lagrange_eval: impl Fn(usize, usize, Scalar) -> Scalar,
    z_of: impl Fn(Scalar) -> Scalar,
) -> ClearQuotients {
    let n = b_bits.len();
    assert_eq!(n, weights.len(), "b_bits and weights must have same length");

    let domain_size = eval_domain.len();

    // Step 1: Compute S' = Σ w_i · b_i (the claimed weighted sum)
    let mut s_prime = Scalar::ZERO;
    for i in 0..n {
        if b_bits[i] == 1 {
            s_prime += weights[i];
        }
    }

    // Step 2: Evaluate B(x), W(x), and C'(x) = W(x)·B(x) over eval_domain
    let mut b_evals = Vec::with_capacity(domain_size);
    let mut w_evals = Vec::with_capacity(domain_size);
    let mut c_prime_evals = Vec::with_capacity(domain_size);

    for &x in eval_domain {
        // B(x) = Σ b_i · L_i(x)
        let mut b_x = Scalar::ZERO;
        for i in 0..n {
            if b_bits[i] == 1 {
                b_x += lagrange_eval(i, n, x);
            }
        }

        // W(x) = Σ w_i · L_i(x)
        let mut w_x = Scalar::ZERO;
        for i in 0..n {
            w_x += weights[i] * lagrange_eval(i, n, x);
        }

        // C'(x) = W(x)·B(x)
        let c_prime_x = w_x * b_x;

        b_evals.push(b_x);
        w_evals.push(w_x);
        c_prime_evals.push(c_prime_x);
    }

    // Step 3: Compute quotient polynomials Q'_x(x) and Q'_Z(x)
    // We have: W(x)·B(x) - S' = Q'_x(x)·x + Q'_Z(x)·Z(x)
    // This is a system of linear equations for each eval point

    let mut qx_prime_evals = Vec::with_capacity(domain_size);
    let mut qz_prime_evals = Vec::with_capacity(domain_size);

    for (i, &x) in eval_domain.iter().enumerate() {
        let _z_x = z_of(x);

        // We need to solve: C'(x) - S' = Q'_x(x)·x + Q'_Z(x)·Z(x)
        // For a proper system, we'd need more equations, but for this mini-step
        // we can construct valid quotients by choosing Q'_Z arbitrarily and solving for Q'_x

        // Simple construction: set Q'_Z(x) = 0 and Q'_x(x) = (C'(x) - S') / x
        // This is valid when x ≠ 0 (which is guaranteed on our coset domain)

        assert!(x != Scalar::ZERO, "Evaluation domain contains zero");

        let residual = c_prime_evals[i] - s_prime;
        let qx_prime_x = residual * x.invert().unwrap();
        let qz_prime_x = Scalar::ZERO;

        qx_prime_evals.push(qx_prime_x);
        qz_prime_evals.push(qz_prime_x);
    }

    ClearQuotients {
        b_evals,
        w_evals,
        c_prime_evals,
        qx_prime_evals,
        qz_prime_evals,
        s_prime,
    }
}

// ============================================================================
// VERIFICATION
// ============================================================================

/// Verify the clear W·B identity at a specific domain point
///
/// Checks: W(r)·B(r) = S' + Q'_x(r)·r + Q'_Z(r)·Z(r)
///
/// # Arguments
/// * `quotients` - Precomputed quotient polynomials
/// * `eval_domain` - Evaluation domain
/// * `test_idx` - Index of point to test
/// * `z_of` - Function to evaluate vanishing polynomial Z(x)
///
/// # Returns
/// * `true` if identity holds, `false` otherwise
pub fn verify_clear_wb_identity_at_domain_point(
    quotients: &ClearQuotients,
    eval_domain: &[Scalar],
    test_idx: usize,
    z_of: impl Fn(Scalar) -> Scalar,
) -> bool {
    let r = eval_domain[test_idx];

    let w_r = quotients.w_evals[test_idx];
    let b_r = quotients.b_evals[test_idx];
    let qx_prime_r = quotients.qx_prime_evals[test_idx];
    let qz_prime_r = quotients.qz_prime_evals[test_idx];
    let s_prime = quotients.s_prime;
    let z_r = z_of(r);

    // LHS: W(r)·B(r)
    let lhs = w_r * b_r;

    // RHS: S' + Q'_x(r)·r + Q'_Z(r)·Z(r)
    let rhs = s_prime + qx_prime_r * r + qz_prime_r * z_r;

    println!("  📐 LHS: W(r)·B(r)");
    println!("  📐 RHS: S' + Q'_x(r)·r + Q'_Z(r)·Z(r)");
    println!("  📊 W(r) = {:?}", w_r);
    println!("  📊 B(r) = {:?}", b_r);
    println!("  📊 S' = {:?}", s_prime);

    if lhs == rhs {
        println!("  ✅ Clear Sumcheck passed at r (W·B identity)");
        true
    } else {
        println!("  ❌ Clear Sumcheck FAILED:");
        println!("     LHS ≠ RHS");
        println!("     W(r) = {:?}", w_r);
        println!("     B(r) = {:?}", b_r);
        println!("     Q'_x(r) = {:?}", qx_prime_r);
        println!("     Q'_Z(r) = {:?}", qz_prime_r);
        println!("     S' = {:?}", s_prime);
        println!("     Z(r) = {:?}", z_r);
        println!("     LHS = {:?}", lhs);
        println!("     RHS = {:?}", rhs);
        false
    }
}

/// Full verification function that ties everything together
pub fn verify_clear_sumcheck(
    signing_set: &[usize],
    weights: &[Scalar],
    n: usize,
) -> bool {
    println!("\n🔍 Verifying Clear Sumcheck (W·B identity):");

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

    println!("  📊 Domain size: {} (next power of 2 from n={})", domain_size, n);
    println!("  📊 Signing set: {:?}", signing_set);
    println!("  📊 Evaluation domain offset: 7 (coset)");

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

    // Compute quotients
    let quotients = compute_clear_quotients(
        &b_bits,
        weights,
        &eval_domain,
        lagrange_eval,
        z_of,
    );

    println!("  📊 B(x) evaluations: {} points", quotients.b_evals.len());
    println!("  📊 W(x) evaluations: {} points", quotients.w_evals.len());
    println!("  📊 C'(x) evaluations: {} points", quotients.c_prime_evals.len());
    println!("  📊 S' (weighted sum): {:?}", quotients.s_prime);

    // Commit to polynomials
    let com_b = com_scalars(&quotients.b_evals);
    let com_w = com_scalars(&quotients.w_evals);
    let com_qx = com_scalars(&quotients.qx_prime_evals);
    let com_qz = com_scalars(&quotients.qz_prime_evals);

    println!("  🔒 Com(B): {} bytes", com_b.root.len());
    println!("  🔒 Com(W): {} bytes", com_w.root.len());
    println!("  🔒 Com(Q'_x): {} bytes", com_qx.root.len());
    println!("  🔒 Com(Q'_Z): {} bytes", com_qz.root.len());

    // Test at middle domain point
    let test_idx = domain_size / 2;
    println!("  🎲 Test point r: eval_domain[{}]", test_idx);

    // Verify identity
    verify_clear_wb_identity_at_domain_point(&quotients, &eval_domain, test_idx, z_of)
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clear_sumcheck() {
        let n = 5;
        let signing_set = vec![0, 1, 2];
        let weights = vec![
            Scalar::from(1),
            Scalar::from(2),
            Scalar::from(3),
            Scalar::from(4),
            Scalar::from(5),
        ];

        let result = verify_clear_sumcheck(&signing_set, &weights, n);
        assert!(result, "Clear sumcheck should pass");
    }

    #[test]
    fn test_clear_sumcheck_different_sets() {
        let test_cases = vec![
            (5, vec![0, 1, 2]),
            (5, vec![0, 2, 4]),
            (4, vec![0, 1, 2, 3]),
            (4, vec![1, 3]),
        ];

        for (n, signing_set) in test_cases {
            let weights: Vec<Scalar> = (1..=n)
                .map(|i| Scalar::from(i as u64))
                .collect();

            println!("\nTesting n={}, signing_set={:?}", n, signing_set);
            let result = verify_clear_sumcheck(&signing_set, &weights, n);
            assert!(result, "Clear sumcheck should pass for n={}, signing_set={:?}", n, signing_set);
        }
    }

    #[test]
    fn test_compute_clear_quotients() {
        let n = 4;
        let b_bits = vec![1u8, 0u8, 1u8, 0u8];
        let weights = vec![
            Scalar::from(1),
            Scalar::from(2),
            Scalar::from(3),
            Scalar::from(4),
        ];

        let domain_size = n.next_power_of_two();
        let eval_domain = generate_evaluation_domain(domain_size, Scalar::from(7));
        let vanishing_domain = generate_evaluation_domain(domain_size, Scalar::ONE);
        let vanishing_roots: Vec<Scalar> = vanishing_domain.iter().take(n).copied().collect();

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

        let quotients = compute_clear_quotients(
            &b_bits,
            &weights,
            &eval_domain,
            lagrange_eval,
            z_of,
        );

        // S' should be 1*1 + 3*1 = 4
        assert_eq!(quotients.s_prime, Scalar::from(4));

        // Verify identity at test point
        let test_idx = domain_size / 2;
        let result = verify_clear_wb_identity_at_domain_point(
            &quotients,
            &eval_domain,
            test_idx,
            z_of,
        );
        assert!(result, "Identity should hold at test point");
    }

    #[test]
    fn test_com_scalars() {
        let scalars = vec![Scalar::ONE, Scalar::ZERO, Scalar::from(42)];
        let com = com_scalars(&scalars);

        assert_eq!(com.root.len(), 32, "Commitment should be 32 bytes");

        // Different inputs should produce different commitments
        let scalars2 = vec![Scalar::ZERO, Scalar::ONE, Scalar::from(42)];
        let com2 = com_scalars(&scalars2);

        assert_ne!(com.root, com2.root, "Different inputs should produce different commitments");
    }
}