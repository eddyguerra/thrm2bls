// polynomial.rs - Polynomial operations and utilities
use bls12_381::{G1Projective, Scalar};
use ff::Field;

/// Represents a polynomial in coefficient form
#[derive(Clone, Debug)]
pub struct Polynomial {
    pub coefficients: Vec<Scalar>,
}

impl Polynomial {
    pub fn new(coefficients: Vec<Scalar>) -> Self {
        Self { coefficients }
    }

    pub fn degree(&self) -> usize {
        self.coefficients.len().saturating_sub(1)
    }

    /// Evaluate polynomial at a point
    pub fn evaluate(&self, x: Scalar) -> Scalar {
        let mut result = Scalar::ZERO;
        let mut power = Scalar::ONE;

        for coeff in &self.coefficients {
            result += *coeff * power;
            power *= x;
        }

        result
    }

    /// Multiply two polynomials
    pub fn multiply(&self, other: &Polynomial) -> Polynomial {
        let result_degree = self.degree() + other.degree();
        let mut result = vec![Scalar::ZERO; result_degree + 1];

        for (i, &a) in self.coefficients.iter().enumerate() {
            for (j, &b) in other.coefficients.iter().enumerate() {
                result[i + j] += a * b;
            }
        }

        Polynomial::new(result)
    }

    /// Add two polynomials
    pub fn add(&self, other: &Polynomial) -> Polynomial {
        let max_len = self.coefficients.len().max(other.coefficients.len());
        let mut result = vec![Scalar::ZERO; max_len];

        for (i, &coeff) in self.coefficients.iter().enumerate() {
            result[i] += coeff;
        }

        for (i, &coeff) in other.coefficients.iter().enumerate() {
            result[i] += coeff;
        }

        Polynomial::new(result)
    }

    /// Subtract two polynomials
    pub fn subtract(&self, other: &Polynomial) -> Polynomial {
        let max_len = self.coefficients.len().max(other.coefficients.len());
        let mut result = vec![Scalar::ZERO; max_len];

        for (i, &coeff) in self.coefficients.iter().enumerate() {
            result[i] += coeff;
        }

        for (i, &coeff) in other.coefficients.iter().enumerate() {
            result[i] -= coeff;
        }

        Polynomial::new(result)
    }

    /// Divide polynomial by (x - point), returns (quotient, remainder)
    pub fn divide_by_linear(&self, point: Scalar) -> (Polynomial, Scalar) {
        if self.coefficients.is_empty() {
            return (Polynomial::new(vec![]), Scalar::ZERO);
        }

        let mut quotient = vec![Scalar::ZERO; self.degree()];
        let mut remainder = self.coefficients[self.degree()];

        for i in (0..self.degree()).rev() {
            quotient[i] = remainder;
            remainder = self.coefficients[i] + remainder * point;
        }

        (Polynomial::new(quotient), remainder)
    }

    /// Scale polynomial by a constant
    pub fn scale(&self, scalar: Scalar) -> Polynomial {
        Polynomial::new(
            self.coefficients.iter().map(|&c| c * scalar).collect()
        )
    }
}

/// Encapsulated polynomial (polynomial in the exponent)
#[derive(Clone, Debug)]
pub struct EncapsulatedPolynomial {
    pub evaluations: Vec<G1Projective>,
}

impl EncapsulatedPolynomial {
    pub fn new(evaluations: Vec<G1Projective>) -> Self {
        Self { evaluations }
    }

    /// Add two encapsulated polynomials (point-wise)
    pub fn add(&self, other: &EncapsulatedPolynomial) -> EncapsulatedPolynomial {
        assert_eq!(self.evaluations.len(), other.evaluations.len());

        let result = self.evaluations
            .iter()
            .zip(other.evaluations.iter())
            .map(|(&a, &b)| a + b)
            .collect();

        EncapsulatedPolynomial::new(result)
    }

    /// Scale encapsulated polynomial by a scalar
    pub fn scale(&self, scalar: Scalar) -> EncapsulatedPolynomial {
        let result = self.evaluations
            .iter()
            .map(|&p| p * scalar)
            .collect();

        EncapsulatedPolynomial::new(result)
    }

    /// Linear combination of encapsulated values
    pub fn linear_combination(values: &[G1Projective], coeffs: &[Scalar]) -> G1Projective {
        assert_eq!(values.len(), coeffs.len());

        values.iter()
            .zip(coeffs.iter())
            .fold(G1Projective::identity(), |acc, (&v, &c)| acc + (v * c))
    }
}

/// Lagrange interpolation utilities
pub struct LagrangeInterpolation;

impl LagrangeInterpolation {
    /// Compute Lagrange basis polynomial L_i(x) for given points
    /// L_i(points[i]) = 1, L_i(points[j]) = 0 for j != i
    pub fn basis_polynomial(i: usize, points: &[Scalar]) -> Polynomial {
        let n = points.len();
        let mut result = Polynomial::new(vec![Scalar::ONE]);

        for j in 0..n {
            if i != j {
                // Multiply by (x - points[j]) / (points[i] - points[j])
                let numerator = Polynomial::new(vec![-points[j], Scalar::ONE]);
                let denominator = (points[i] - points[j]).invert().unwrap();

                result = result.multiply(&numerator).scale(denominator);
            }
        }

        result
    }

    /// Interpolate polynomial from points and values
    pub fn interpolate(points: &[Scalar], values: &[Scalar]) -> Polynomial {
        assert_eq!(points.len(), values.len());

        let mut result = Polynomial::new(vec![Scalar::ZERO]);

        for i in 0..points.len() {
            let basis = Self::basis_polynomial(i, points);
            let scaled_basis = basis.scale(values[i]);
            result = result.add(&scaled_basis);
        }

        result
    }

    /// Evaluate Lagrange basis L_i at a specific point x
    /// L_i(x) = ∏(j≠i) (x - points[j]) / (points[i] - points[j])
    pub fn evaluate_basis(i: usize, points: &[Scalar], x: Scalar) -> Scalar {
        let mut result = Scalar::ONE;

        for j in 0..points.len() {
            if i != j {
                result *= (x - points[j]) * (points[i] - points[j]).invert().unwrap();
            }
        }

        result
    }

    /// Evaluate L_i(alpha) over a domain, considering only first n points
    /// Used for polynomial commitment evaluation
    pub fn lagrange_at(i: usize, n: usize, domain: &[Scalar], alpha: Scalar) -> Scalar {
        let points = &domain[..n.min(domain.len())];
        Self::evaluate_basis(i, points, alpha)
    }
}

/// Vanishing polynomial Z(x) = ∏(x - ω_i)
pub struct VanishingPolynomial {
    roots: Vec<Scalar>,
}

impl VanishingPolynomial {
    pub fn new(roots: Vec<Scalar>) -> Self {
        Self { roots }
    }

    /// Compute vanishing polynomial as ∏(x - root_i)
    pub fn as_polynomial(&self) -> Polynomial {
        let mut result = Polynomial::new(vec![Scalar::ONE]);

        for &root in &self.roots {
            let linear = Polynomial::new(vec![-root, Scalar::ONE]);
            result = result.multiply(&linear);
        }

        result
    }

    /// For roots of unity: Z(x) = x^n - 1
    pub fn from_roots_of_unity(n: usize) -> Polynomial {
        let mut coeffs = vec![Scalar::ZERO; n + 1];
        coeffs[0] = -Scalar::ONE;
        coeffs[n] = Scalar::ONE;
        Polynomial::new(coeffs)
    }

    /// Evaluate vanishing polynomial at x
    pub fn evaluate(&self, x: Scalar) -> Scalar {
        self.roots.iter().fold(Scalar::ONE, |acc, &root| acc * (x - root))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_polynomial_operations() {
        // f(x) = 2x + 3
        let p1 = Polynomial::new(vec![Scalar::from(3), Scalar::from(2)]);

        // Evaluate at x = 5: f(5) = 2*5 + 3 = 13
        let result = p1.evaluate(Scalar::from(5));
        assert_eq!(result, Scalar::from(13));
    }

    #[test]
    fn test_lagrange_interpolation() {
        let points = vec![Scalar::from(1), Scalar::from(2), Scalar::from(3)];
        let values = vec![Scalar::from(2), Scalar::from(4), Scalar::from(6)];

        let poly = LagrangeInterpolation::interpolate(&points, &values);

        // Verify interpolation
        for i in 0..points.len() {
            let eval = poly.evaluate(points[i]);
            assert_eq!(eval, values[i]);
        }
    }

    #[test]
    fn test_polynomial_division() {
        // f(x) = x^2 - 1 = (x-1)(x+1)
        let poly = Polynomial::new(vec![-Scalar::ONE, Scalar::ZERO, Scalar::ONE]);
        let (quotient, remainder) = poly.divide_by_linear(Scalar::ONE);

        // Should divide evenly
        assert_eq!(remainder, Scalar::ZERO);
        // Quotient should be (x + 1)
        assert_eq!(quotient.degree(), 1);
    }

    #[test]
    fn test_polynomial_multiply() {
        // f(x) = x + 1
        let p1 = Polynomial::new(vec![Scalar::ONE, Scalar::ONE]);
        // g(x) = x + 2
        let p2 = Polynomial::new(vec![Scalar::from(2), Scalar::ONE]);

        // (x+1)(x+2) = x^2 + 3x + 2
        let result = p1.multiply(&p2);

        assert_eq!(result.coefficients.len(), 3);
        assert_eq!(result.coefficients[0], Scalar::from(2)); // constant
        assert_eq!(result.coefficients[1], Scalar::from(3)); // x coefficient
        assert_eq!(result.coefficients[2], Scalar::ONE);     // x^2 coefficient
    }

    #[test]
    fn test_vanishing_polynomial() {
        // Z(x) = x^3 - 1 (for 3rd roots of unity)
        let vanishing = VanishingPolynomial::from_roots_of_unity(3);

        assert_eq!(vanishing.degree(), 3);
        assert_eq!(vanishing.coefficients[0], -Scalar::ONE);
        assert_eq!(vanishing.coefficients[3], Scalar::ONE);

        // Should evaluate to 0 at x=1 (a cube root of unity)
        let result = vanishing.evaluate(Scalar::ONE);
        assert_eq!(result, Scalar::ZERO);
    }

    #[test]
    fn test_encapsulated_polynomial() {
        let generator = G1Projective::generator();

        // Create encapsulated values
        let evals = vec![
            generator * Scalar::from(1),
            generator * Scalar::from(2),
            generator * Scalar::from(3),
        ];

        let enc_poly = EncapsulatedPolynomial::new(evals);

        // Scale by 2
        let scaled = enc_poly.scale(Scalar::from(2));

        // Check first element: g^1 * 2 = g^2
        assert_eq!(scaled.evaluations[0], generator * Scalar::from(2));
    }
}