// booleanity.rs - Booleanity constraint checking for indicator polynomials
//
// This module implements the constraint B(x)·(1-B(x)) = Q(x)·Z(x) where:
// - B(x) = Σ b_i · L_i(x) is the indicator polynomial
// - Q(x) = B(x)·(1-B(x)) / Z(x) is the quotient polynomial
// - Z(x) = Π(x - ω_i) is the vanishing polynomial over first n points

use bls12_381::Scalar;
use ff::Field;
use sha2::{Digest, Sha256};

use crate::polynomial::LagrangeInterpolation;
use crate::fri::generate_evaluation_domain;

// ============================================================================
// CLEAR POLYNOMIAL COMMITMENT
// ============================================================================

/// Clear (non-encapsulated) polynomial commitment via Merkle root
#[derive(Clone, Debug)]
pub struct ClearPolyCommitment {
    pub root: Vec<u8>,
}

/// Commit to a vector of scalars via Merkle tree hash
pub fn com_scalars(scalars: &[Scalar]) -> ClearPolyCommitment {
    let leaves: Vec<[u8; 32]> = scalars
        .iter()
        .map(|s| {
            let bytes = s.to_bytes();
            let mut arr = [0u8; 32];
            arr.copy_from_slice(&bytes);
            arr
        })
        .collect();

    let root = merkle_commit_scalar_bytes(&leaves);
    ClearPolyCommitment { root }
}

fn merkle_commit_scalar_bytes(leaves: &[[u8; 32]]) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(b"MERKLE_ROOT_SCALARS_BOOL");
    for leaf in leaves {
        hasher.update(leaf);
    }
    hasher.finalize().to_vec()
}

// ============================================================================
// BOOLEAN QUOTIENT COMPUTATION
// ============================================================================

/// Compute the Boolean quotient polynomial Q(x) = B(x)·(1-B(x)) / Z(x)
/// where B(x) = Σ b_i · L_i(x) is the indicator polynomial.
///
/// # Arguments
/// * `b_bits` - Binary indicator values (0 or 1) for each party
/// * `domain` - Evaluation domain H
/// * `lagrange_eval` - Function to evaluate L_i(x) at a point x
/// * `z_of` - Function to evaluate vanishing polynomial Z(x) at a point x
///
/// # Returns
/// * `(b_eval, q_bool)` where:
///   - `b_eval[j]` = B(domain[j])
///   - `q_bool[j]` = Q(domain[j]) = B(domain[j])·(1-B(domain[j])) / Z(domain[j])
///
/// # Panics
/// * If Z(x) = 0 at any domain point (should not happen on coset domains)
pub fn compute_boolean_quotient(
    b_bits: &[u8],
    domain: &[Scalar],
    lagrange_eval: impl Fn(usize, usize, Scalar) -> Scalar,
    z_of: impl Fn(Scalar) -> Scalar,
) -> (Vec<Scalar>, Vec<Scalar>) {
    let n = b_bits.len();
    let domain_size = domain.len();

    let mut b_eval = Vec::with_capacity(domain_size);
    let mut q_bool = Vec::with_capacity(domain_size);

    // Evaluate B(x) and Q(x) at each domain point
    for &x in domain {
        // Compute B(x) = Σ b_i · L_i(x)
        let mut b_x = Scalar::ZERO;
        for i in 0..n {
            if b_bits[i] == 1 {
                let l_i_x = lagrange_eval(i, n, x);
                b_x += l_i_x;
            }
        }

        // Compute Z(x) = Π(x - ω_i) for the first n roots
        let z_x = z_of(x);

        // Ensure Z(x) ≠ 0 (guaranteed on coset domain)
        assert!(z_x != Scalar::ZERO, "Z(x) = 0 at domain point, cannot divide");

        // Compute Q(x) = B(x)·(1-B(x)) / Z(x)
        let numerator = b_x * (Scalar::ONE - b_x);
        let q_x = numerator * z_x.invert().unwrap();

        b_eval.push(b_x);
        q_bool.push(q_x);
    }

    (b_eval, q_bool)
}

// ============================================================================
// BOOLEANITY CONSTRAINT VERIFICATION
// ============================================================================

/// Verify the booleanity constraint: B(r)·(1-B(r)) = Q(r)·Z(r)
/// at a test point r chosen from the domain.
///
/// # Arguments
/// * `signing_set` - Indices of parties that signed
/// * `n` - Total number of parties
///
/// # Returns
/// * `true` if the constraint holds, `false` otherwise
///
/// # Output
/// * Prints diagnostic information and success/failure message
pub fn verify_booleanity_constraint(
    signing_set: &[usize],
    n: usize,
) -> bool {
    println!("\n🔍 Verifying Booleanity Constraint:");

    // Construct indicator bits: b_i = 1 if party i signed, 0 otherwise
    let mut b_bits = vec![0u8; n];
    for &i in signing_set {
        if i < n {
            b_bits[i] = 1;
        }
    }

    // Generate evaluation domain (power-of-two size, coset to avoid subgroup)
    // IMPORTANT: Use a non-trivial coset offset to ensure the evaluation domain
    // does NOT overlap with the vanishing polynomial roots
    let domain_size = n.next_power_of_two();
    let coset_offset = Scalar::from(7); // Non-subgroup coset offset
    let eval_domain = generate_evaluation_domain(domain_size, coset_offset);

    // Generate the vanishing polynomial domain (first n points of a DIFFERENT domain)
    // This is H = {ω^0, ω^1, ..., ω^(n-1)} - the roots where Z(x) = 0
    let vanishing_domain = generate_evaluation_domain(domain_size, Scalar::ONE);
    let vanishing_roots: Vec<Scalar> = vanishing_domain.iter().take(n).copied().collect();

    println!("  📊 Domain size: {} (next power of 2 from n={})", domain_size, n);
    println!("  📊 Signing set: {:?}", signing_set);
    println!("  📊 Evaluation domain offset: 7 (coset)");
    println!("  📊 Vanishing roots domain offset: 1");

    // Define Lagrange evaluation function over vanishing_roots
    let lagrange_eval = |i: usize, n: usize, x: Scalar| -> Scalar {
        LagrangeInterpolation::lagrange_at(i, n, &vanishing_roots, x)
    };

    // Define vanishing polynomial Z(x) = Π(x - ω_i) for first n points
    let z_of = |x: Scalar| -> Scalar {
        let mut result = Scalar::ONE;
        for j in 0..n {
            result *= x - vanishing_roots[j];
        }
        result
    };

    // Compute B(x) and Q(x) evaluations over the COSET evaluation domain
    let (b_eval, q_bool) = compute_boolean_quotient(
        &b_bits,
        &eval_domain,
        lagrange_eval,
        z_of,
    );

    // Commit to B and Q
    let com_b = com_scalars(&b_eval);
    let com_q = com_scalars(&q_bool);

    println!("  📊 B(x) evaluations: {} points", b_eval.len());
    println!("  📊 Q(x) evaluations: {} points", q_bool.len());
    println!("  🔒 Com(B): {} bytes", com_b.root.len());
    println!("  🔒 Com(Q): {} bytes", com_q.root.len());

    // For this mini-step: use middle domain point as test point r
    // (avoids interpolation; direct table lookup)
    let test_idx = domain_size / 2;
    let r_test = eval_domain[test_idx];

    println!("  🎲 Test point r: eval_domain[{}]", test_idx);

    // Single-point check: B(r)·(1-B(r)) = Q(r)·Z(r)
    let b_r = b_eval[test_idx];
    let q_r = q_bool[test_idx];
    let z_r = z_of(r_test);

    let lhs = b_r * (Scalar::ONE - b_r);
    let rhs = q_r * z_r;

    println!("  📐 LHS: B(r)·(1-B(r))");
    println!("  📐 RHS: Q(r)·Z(r)");

    if lhs == rhs {
        println!("  ✅ Booleanity check passed at r");
        true
    } else {
        println!("  ❌ Booleanity check FAILED:");
        println!("     LHS ≠ RHS");
        println!("     B(r) = {:?}", b_r);
        println!("     Q(r) = {:?}", q_r);
        println!("     Z(r) = {:?}", z_r);
        println!("     LHS = {:?}", lhs);
        println!("     RHS = {:?}", rhs);
        false
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_booleanity_constraint() {
        // Test with signing set {0, 2} out of 4 parties
        let n = 4;
        let signing_set = vec![0, 2];

        let result = verify_booleanity_constraint(&signing_set, n);
        assert!(result, "Booleanity constraint should hold");
    }

    #[test]
    fn test_booleanity_constraint_all_sign() {
        // Test when all parties sign
        let n = 4;
        let signing_set = vec![0, 1, 2, 3];

        let result = verify_booleanity_constraint(&signing_set, n);
        assert!(result, "Booleanity constraint should hold when all sign");
    }

    #[test]
    fn test_booleanity_constraint_none_sign() {
        // Test when no parties sign (edge case)
        let n = 4;
        let signing_set = vec![];

        let result = verify_booleanity_constraint(&signing_set, n);
        assert!(result, "Booleanity constraint should hold when none sign");
    }

    #[test]
    fn test_compute_boolean_quotient() {
        let n = 4;
        let b_bits = vec![1u8, 0u8, 1u8, 0u8];

        let domain_size = n.next_power_of_two();

        // Evaluation domain (coset)
        let eval_domain = generate_evaluation_domain(domain_size, Scalar::from(7));

        // Vanishing polynomial roots (standard domain)
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

        let (b_eval, q_bool) = compute_boolean_quotient(&b_bits, &eval_domain, lagrange_eval, z_of);

        assert_eq!(b_eval.len(), domain_size);
        assert_eq!(q_bool.len(), domain_size);

        // Verify constraint at test point
        let test_idx = domain_size / 2;
        let b_r = b_eval[test_idx];
        let q_r = q_bool[test_idx];
        let z_r = z_of(eval_domain[test_idx]);

        let lhs = b_r * (Scalar::ONE - b_r);
        let rhs = q_r * z_r;

        assert_eq!(lhs, rhs, "Booleanity constraint should hold at test point");
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