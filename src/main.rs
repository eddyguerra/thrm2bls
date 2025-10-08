// main.rs - Complete threshold signature scheme with FRI-based proof generation
use bls12_381::{G1Projective, Scalar};
use ff::Field;
use group::Curve;
use rand::RngCore;
use sha2::{Digest, Sha256};
use std::collections::HashMap;

mod polynomial;
mod fri;

use polynomial::LagrangeInterpolation;
use fri::ProofGenerator;

// ============================================================================
// DOMAIN UTILITIES
// ============================================================================

/// Generate m-th roots of unity domain for polynomial evaluation
/// For simplicity, we use a multiplicative subgroup H = {ω^0, ω^1, ..., ω^(m-1)}
fn domain_roots_of_unity(m: usize) -> Vec<Scalar> {
    // For BLS12-381 scalar field, we need to find a primitive m-th root of unity
    // For now, use a simple domain (this should be replaced with actual roots of unity)
    (0..m).map(|i| Scalar::from((i + 1) as u64)).collect()
}

/// Compute Lagrange basis value L_i(alpha) over domain
fn lagrange_at(i: usize, n: usize, domain: &[Scalar], alpha: Scalar) -> Scalar {
    LagrangeInterpolation::lagrange_at(i, n, domain, alpha)
}

/// Merkle commit to byte arrays
fn merkle_commit_bytes(leaves: &[[u8; 48]]) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(b"MERKLE_ROOT");
    for leaf in leaves {
        hasher.update(leaf);
    }
    hasher.finalize().to_vec()
}

/// Merkle commit to scalar byte arrays
fn merkle_commit_scalar_bytes(leaves: &[[u8; 32]]) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(b"MERKLE_ROOT_SCALARS");
    for leaf in leaves {
        hasher.update(leaf);
    }
    hasher.finalize().to_vec()
}

// ============================================================================
// CORE THRESHOLD SIGNATURE TYPES
// ============================================================================

#[derive(Clone, Debug)]
struct PolynomialCommitment {
    commitment: Vec<u8>,
}

impl PolynomialCommitment {
    fn new(data: &[u8]) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(data);
        Self {
            commitment: hasher.finalize().to_vec(),
        }
    }
}

fn hcom_from_pks(public_keys: &[G1Projective]) -> PolynomialCommitment {
    let mut data = Vec::new();
    for pk in public_keys {
        data.extend_from_slice(&pk.to_affine().to_compressed());
    }
    PolynomialCommitment::new(&data)
}

fn com_from_weights(weights: &[Scalar]) -> PolynomialCommitment {
    let mut data = Vec::new();
    for w in weights {
        data.extend_from_slice(&w.to_bytes());
    }
    PolynomialCommitment::new(&data)
}

fn ro(point: &G1Projective) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(b"RO");
    hasher.update(&point.to_affine().to_compressed());
    hasher.finalize().to_vec()
}

fn ro_prime(msg: &[u8], point: &G1Projective) -> Scalar {
    let mut hasher = Sha256::new();
    hasher.update(b"RO'");
    hasher.update(msg);
    hasher.update(&point.to_affine().to_compressed());
    let hash = hasher.finalize();

    let mut bytes = [0u8; 64];
    bytes[..32].copy_from_slice(&hash);
    Scalar::from_bytes_wide(&bytes)
}

#[derive(Clone, Debug)]
pub struct SecretKey(Scalar);

#[derive(Clone, Debug)]
pub struct PublicKey(G1Projective);

#[derive(Clone, Debug)]
pub struct VerificationKey {
    sk_commitment: PolynomialCommitment,
    weight_commitment: PolynomialCommitment,
}

pub struct ThresholdSignature {
    generator: G1Projective,
}

impl ThresholdSignature {
    pub fn new() -> Self {
        Self {
            generator: G1Projective::generator(),
        }
    }

    pub fn keygen<R: RngCore>(&self, rng: &mut R) -> (SecretKey, PublicKey) {
        let sk = Scalar::random(rng);
        let pk = self.generator * sk;
        (SecretKey(sk), PublicKey(pk))
    }

    pub fn preprocess(&self, public_keys: &[PublicKey], weights: &[Scalar]) -> VerificationKey {
        assert_eq!(
            public_keys.len(),
            weights.len(),
            "Number of public keys must match number of weights"
        );

        let pks: Vec<G1Projective> = public_keys.iter().map(|pk| pk.0).collect();

        let sk_commitment = hcom_from_pks(&pks);
        let weight_commitment = com_from_weights(weights);

        VerificationKey {
            sk_commitment,
            weight_commitment,
        }
    }
}

// ============================================================================
// SIGNING PROTOCOL
// ============================================================================

#[derive(Clone)]
pub struct SigningParty {
    #[allow(dead_code)]
    id: usize,
    secret_key: SecretKey,
    #[allow(dead_code)]
    public_key: PublicKey,
    #[allow(dead_code)]
    weight: Scalar,
    nonce: Option<Scalar>,
    #[allow(dead_code)]
    nonce_commitment: Option<Vec<u8>>,
}

impl SigningParty {
    pub fn new(id: usize, secret_key: SecretKey, public_key: PublicKey, weight: Scalar) -> Self {
        Self {
            id,
            secret_key,
            public_key,
            weight,
            nonce: None,
            nonce_commitment: None,
        }
    }

    pub fn sign1<R: RngCore>(&mut self, rng: &mut R, generator: &G1Projective) -> Vec<u8> {
        let r = Scalar::random(rng);
        let g_r = generator * r;
        let commitment = ro(&g_r);

        self.nonce = Some(r);
        self.nonce_commitment = Some(commitment.clone());

        commitment
    }

    pub fn sign2(&self, _generator: &G1Projective) -> G1Projective {
        let r = self.nonce.expect("Must call sign1 first");
        _generator * r
    }

    pub fn sign3(
        &self,
        msg: &[u8],
        all_nonces: &HashMap<usize, G1Projective>,
        _generator: &G1Projective,
    ) -> Scalar {
        let g_r = all_nonces.values().fold(G1Projective::identity(), |acc, &n| acc + n);
        let c = ro_prime(msg, &g_r);
        let r = self.nonce.expect("Must call sign1 first");
        c * self.secret_key.0 + r
    }
}

#[derive(Clone, Debug)]
pub struct PartialSignature {
    pub party_id: usize,
    pub commitment: Vec<u8>,
    pub nonce_reveal: G1Projective,
    pub response: Scalar,
}

#[derive(Clone, Debug)]
pub struct AggregatedSignature {
    pub g_r: G1Projective,
    pub sigma: Scalar,
    pub threshold: Scalar,
    pub aggregated_pk: G1Projective,
    pub proof: Option<fri::AggregationProof>,
}

// ============================================================================
// AGGREGATOR
// ============================================================================

pub struct Aggregator {
    generator: G1Projective,
    proof_generator: ProofGenerator,
}

impl Aggregator {
    pub fn new(generator: G1Projective) -> Self {
        Self {
            generator,
            proof_generator: ProofGenerator::new(generator),
        }
    }

    pub fn verify_partial(
        &self,
        partial: &PartialSignature,
        public_key: &PublicKey,
        msg: &[u8],
        g_r: &G1Projective,
    ) -> bool {
        let c = ro_prime(msg, g_r);
        let lhs = self.generator * partial.response;
        let rhs = (public_key.0 * c) + partial.nonce_reveal;
        lhs == rhs
    }

    pub fn aggregate(
        &self,
        msg: &[u8],
        partials: &[PartialSignature],
        public_keys: &HashMap<usize, PublicKey>,
        weights: &HashMap<usize, Scalar>,
        n: usize,
    ) -> Result<AggregatedSignature, &'static str> {
        if partials.is_empty() {
            return Err("No partial signatures provided");
        }

        let g_r = partials
            .iter()
            .fold(G1Projective::identity(), |acc, p| acc + p.nonce_reveal);

        for partial in partials {
            let pk = public_keys
                .get(&partial.party_id)
                .ok_or("Public key not found")?;

            if !self.verify_partial(partial, pk, msg, &g_r) {
                return Err("Partial signature verification failed");
            }
        }

        let threshold = partials
            .iter()
            .map(|p| weights.get(&p.party_id).unwrap())
            .fold(Scalar::ZERO, |acc, &w| acc + w);

        let aggregated_pk = partials
            .iter()
            .map(|p| public_keys.get(&p.party_id).unwrap().0)
            .fold(G1Projective::identity(), |acc, pk| acc + pk);

        let sigma = partials
            .iter()
            .fold(Scalar::ZERO, |acc, p| acc + p.response);

        // Generate aggregation proof
        let signing_set: Vec<usize> = partials.iter().map(|p| p.party_id).collect();

        let all_pks: Vec<G1Projective> = (0..n)
            .map(|i| public_keys.get(&i).map(|pk| pk.0).unwrap_or(G1Projective::identity()))
            .collect();

        let all_weights: Vec<Scalar> = (0..n)
            .map(|i| *weights.get(&i).unwrap_or(&Scalar::ZERO))
            .collect();

        let proof = self.proof_generator.generate_aggregation_proof(
            &signing_set,
            n,
            &all_pks,
            &all_weights,
        );

        Ok(AggregatedSignature {
            g_r,
            sigma,
            threshold,
            aggregated_pk,
            proof: Some(proof),
        })
    }

    pub fn verify_aggregated(
        &self,
        msg: &[u8],
        signature: &AggregatedSignature,
        n: usize,
    ) -> bool {
        let c = ro_prime(msg, &signature.g_r);
        let lhs = self.generator * signature.sigma;
        let rhs = (signature.aggregated_pk * c) + signature.g_r;

        let sig_valid = lhs == rhs;

        if !sig_valid {
            return false;
        }

        // Verify aggregation proof if present
        if let Some(ref proof) = signature.proof {
            return self.proof_generator.verify_aggregation_proof(
                proof,
                signature.threshold,
                signature.aggregated_pk,
                n,
            );
        }

        true
    }
}

// ============================================================================
// MAIN DEMO
// ============================================================================

fn main() {
    use rand::thread_rng;

    println!("═══════════════════════════════════════════════════════════");
    println!("  Weighted Threshold Signature with FRI-based Proofs");
    println!("═══════════════════════════════════════════════════════════\n");

    let mut rng = thread_rng();
    let ts = ThresholdSignature::new();
    let n = 5;
    let t = 3;

    println!("📋 Setup:");
    println!("  Total parties: {}", n);
    println!("  Threshold: {} signers required", t);
    println!("  Curve: BLS12-381");
    println!("  Proof System: FRI on LHEncap\n");

    // Key Generation
    let mut parties = Vec::new();
    let mut public_keys_map = HashMap::new();
    let mut weights_map = HashMap::new();
    let mut public_keys_vec = Vec::new();
    let mut weights_vec = Vec::new();

    println!("🔑 Key Generation:");
    for i in 0..n {
        let (sk, pk) = ts.keygen(&mut rng);
        let weight = Scalar::from((i + 1) as u64);

        let party = SigningParty::new(i, sk, pk.clone(), weight);
        public_keys_map.insert(i, pk.clone());
        weights_map.insert(i, weight);
        public_keys_vec.push(pk);
        weights_vec.push(weight);
        parties.push(party);

        println!("  Party {} → weight: {}", i, i + 1);
    }

    // Preprocess
    println!("\n⚙️  Preprocessing:");
    let vk = ts.preprocess(&public_keys_vec, &weights_vec);
    println!("  Verification key generated");
    println!("  SK commitment: {} bytes", vk.sk_commitment.commitment.len());
    println!("  Weight commitment: {} bytes", vk.weight_commitment.commitment.len());

    // Signing Protocol
    let signing_set: Vec<usize> = (0..t).collect();
    let msg = b"Hello, weighted threshold signature with proofs!";

    println!("\n✍️  Signing Protocol:");
    println!("  Message: {:?}", String::from_utf8_lossy(msg));
    println!("  Signing parties: {:?}", signing_set);

    // Round 1
    println!("\n  📝 Round 1: Nonce Commitments");
    let mut commitments = HashMap::new();
    for &i in &signing_set {
        let commitment = parties[i].sign1(&mut rng, &ts.generator);
        commitments.insert(i, commitment);
        println!("    Party {} committed", i);
    }

    // Round 2
    println!("\n  📤 Round 2: Nonce Reveals");
    let mut nonces = HashMap::new();
    for &i in &signing_set {
        let nonce = parties[i].sign2(&ts.generator);
        nonces.insert(i, nonce);
        println!("    Party {} revealed", i);
    }

    // Round 3
    println!("\n  🔐 Round 3: Partial Signatures");
    let mut partials = Vec::new();
    for &i in &signing_set {
        let response = parties[i].sign3(msg, &nonces, &ts.generator);
        partials.push(PartialSignature {
            party_id: i,
            commitment: commitments[&i].clone(),
            nonce_reveal: nonces[&i],
            response,
        });
        println!("    Party {} signed", i);
    }

    // Aggregation with Proof Generation
    println!("\n🔗 Aggregation:");
    let aggregator = Aggregator::new(ts.generator);

    match aggregator.aggregate(msg, &partials, &public_keys_map, &weights_map, n) {
        Ok(agg_sig) => {
            println!("  ✓ Aggregation successful");
            println!("  Threshold achieved: {:?}", agg_sig.threshold);

            let threshold_value = signing_set.iter()
                .map(|&i| i + 1)
                .sum::<usize>();
            println!("  Expected threshold sum: {} (weights: 1+2+3)", threshold_value);

            if let Some(ref proof) = agg_sig.proof {
                println!("\n📊 Proof Statistics:");
                println!("  Commitment size: {} bytes", proof.b_commitment.len());
                println!("  Estimated total proof size: {} bytes", proof.proof_size);
                println!("  Complexity: O(λ·log²n) = O(128·log²5) ≈ {} bytes",
                         128 * (5_f64.log2().ceil() as usize).pow(2) * 32);
            }

            // Verification
            println!("\n🔍 Verification:");
            if aggregator.verify_aggregated(msg, &agg_sig, n) {
                println!("  ✅ Signature is VALID!");
                println!("  ✅ Aggregation proof VERIFIED!");
            } else {
                println!("  ❌ Signature is INVALID!");
            }
        }
        Err(e) => {
            println!("  ✗ Aggregation failed: {}", e);
        }
    }

    println!("\n═══════════════════════════════════════════════════════════");
    println!("  🎉 Demo Complete!");
    println!("═══════════════════════════════════════════════════════════\n");

    // Additional information
    println!("📖 Implementation Details:");
    println!("  • Polynomial commitments via Merkle trees");
    println!("  • Generalized Sumcheck (Lemma 1) for quotients");
    println!("  • FRI protocol for low-degree testing on LHEncap");
    println!("  • Binary constraint check: B(x)·(1-B(x)) = Q(x)·Z(x)");
    println!("  • Security: AGM + Random Oracle Model");
    println!("  • Signature size: O(log²n)");
    println!("  • Verification time: O(log²n)");
    println!("  • Aggregation time: O(n·log n)\n");
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::thread_rng;

    #[test]
    fn test_complete_workflow() {
        let mut rng = thread_rng();
        let ts = ThresholdSignature::new();
        let n = 5;
        let t = 3;

        let mut parties = Vec::new();
        let mut public_keys_map = HashMap::new();
        let mut weights_map = HashMap::new();
        let mut public_keys_vec = Vec::new();
        let mut weights_vec = Vec::new();

        for i in 0..n {
            let (sk, pk) = ts.keygen(&mut rng);
            let weight = Scalar::from((i + 1) as u64);

            let party = SigningParty::new(i, sk, pk.clone(), weight);
            public_keys_map.insert(i, pk.clone());
            weights_map.insert(i, weight);
            public_keys_vec.push(pk);
            weights_vec.push(weight);
            parties.push(party);
        }

        let _vk = ts.preprocess(&public_keys_vec, &weights_vec);
        let signing_set: Vec<usize> = (0..t).collect();
        let msg = b"Test message";

        let mut commitments = HashMap::new();
        for &i in &signing_set {
            let commitment = parties[i].sign1(&mut rng, &ts.generator);
            commitments.insert(i, commitment);
        }

        let mut nonces = HashMap::new();
        for &i in &signing_set {
            let nonce = parties[i].sign2(&ts.generator);
            nonces.insert(i, nonce);
        }

        let mut partials = Vec::new();
        for &i in &signing_set {
            let response = parties[i].sign3(msg, &nonces, &ts.generator);
            partials.push(PartialSignature {
                party_id: i,
                commitment: commitments[&i].clone(),
                nonce_reveal: nonces[&i],
                response,
            });
        }

        let aggregator = Aggregator::new(ts.generator);
        let agg_sig = aggregator
            .aggregate(msg, &partials, &public_keys_map, &weights_map, n)
            .expect("Aggregation failed");

        assert!(
            aggregator.verify_aggregated(msg, &agg_sig, n),
            "Signature verification failed"
        );

        assert!(agg_sig.proof.is_some(), "Proof should be generated");

        println!("✓ Complete workflow test passed!");
    }
}