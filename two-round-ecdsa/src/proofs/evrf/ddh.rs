use core::{marker::PhantomData, ops::Deref};
use std::io::{self, Read, Write};

use subtle::ConditionallySelectable;
use zeroize::{Zeroize, Zeroizing};
use rand_core::{RngCore, CryptoRng};

use group::{
  Group, GroupEncoding,
  prime::PrimeGroup,
  ff::{Field, PrimeField, PrimeFieldBits},
};
use ciphersuite::Ciphersuite;

/*
  Generalized Bulletproofs is an extension of the Bulletproofs R1CS statement to support Vector
  Commitments. We invoke it without Vector Commitments, in which case it collapses back to the
  traditional Bulletproofs. This means we do use Bulletproofs here and not a newer proof.
*/
use generalized_bulletproofs::*;
use generalized_bulletproofs_circuit_abstraction::*;

use crate::{DigestReader, DigestWriter, Evrf, Parameters};

/// A curve which is embedded into another curve.
pub trait EmbeddedCurve:
  Zeroize + ConditionallySelectable + PrimeGroup<Scalar: Zeroize + PrimeFieldBits>
{
  /// The field this elliptic curve is defined over.
  type FieldElement: PrimeField;
  /// The `a` constant from the equation `y**2 = x**3 + ax + b`.
  fn a() -> Self::FieldElement;
  /// The `b` constant from the equation `y**2 = x**3 + ax + b`.
  fn b() -> Self::FieldElement;
  /// Convert the point to its `x`, `y` coordinates, returning `None` if identity.
  ///
  /// This function MUST execute in constant-time for points which aren't identity.
  fn to_xy(&self) -> Option<(Self::FieldElement, Self::FieldElement)>;
}

#[cfg(feature = "secp256k1")]
impl EmbeddedCurve for secq256k1::Point {
  type FieldElement = k256::Scalar;
  fn a() -> Self::FieldElement {
    <secq256k1::Point as ec_divisors::DivisorCurve>::a()
  }
  fn b() -> Self::FieldElement {
    <secq256k1::Point as ec_divisors::DivisorCurve>::b()
  }
  fn to_xy(&self) -> Option<(Self::FieldElement, Self::FieldElement)> {
    <secq256k1::Point as ec_divisors::DivisorCurve>::to_xy(*self)
  }
}

// Equation 9, yet scaling G_s as we have no futher use for the discrete logarithms over G_s
fn C<G: EmbeddedCurve>() -> Vec<G> {
  const {
    // ceil log2
    let mut log2_l = G::Scalar::CAPACITY.ilog2();
    if (1 << log2_l) < G::Scalar::CAPACITY {
      log2_l += 1;
    }

    // s > l**2
    // Technically, this is 2**n > log2((2**log2_ceil(l))**2) where 2**n < s
    // The real check only trips for some trivial moduli so this more aggressive version isn't an
    // issue
    assert!(G::Scalar::CAPACITY > (log2_l + log2_l));
  }

  let mut carry = 0;
  let res = (0 ..= G::Scalar::CAPACITY)
    .map(|i| {
      G::generator() *
        (if i != G::Scalar::CAPACITY {
          let i = u64::from(i) + 2;
          carry += i;
          G::Scalar::from(i)
        } else {
          -G::Scalar::from(carry)
        })
    })
    .collect::<Vec<_>>();

  debug_assert!({
    // Sum of all prior elements
    let mut carry = G::identity();
    let mut valid = true;
    for i in 1 .. (res.len() - 1) {
      carry += res[i - 1];
      // is not in the set {0, res[i], -res[i]}
      if bool::from(carry.is_identity()) || (carry == res[i]) || (carry == -res[i]) {
        valid = false;
        break;
      }
    }
    valid
  });
  debug_assert!(bool::from(res.iter().sum::<G>().is_identity()));

  res
}

// This is the preprocess of `C[i].to_xy()`
#[allow(clippy::upper_case_acronyms)]
#[derive(Clone)]
struct CXY<F: PrimeField>(Vec<(F, F)>);
impl<F: PrimeField> CXY<F> {
  fn new<G: EmbeddedCurve<FieldElement = F>>(C: &[G]) -> Self {
    Self(C.iter().map(|point| point.to_xy().unwrap()).collect())
  }
}

// Claim 1
struct DiscreteLogarithm(Vec<Variable>);
impl DiscreteLogarithm {
  fn commit<C: Ciphersuite, F: PrimeFieldBits>(
    circuit: &mut Circuit<C>,
    scalar: Option<&F>,
  ) -> Self {
    let mut bit_iter = scalar.map(|scalar| {
      crate::const_to_le_bits(scalar).map(|choice| {
        let bit = C::F::from(u64::from(choice.unwrap_u8()));
        (bit, bit - C::F::ONE)
      })
    });

    let mut res = Vec::with_capacity(F::NUM_BITS.try_into().unwrap());
    for _ in 0 .. F::NUM_BITS {
      let (a, b, c) = circuit.mul(None, None, bit_iter.as_mut().map(|iter| iter.next().unwrap()));
      // a - 1 == b
      circuit.equality(LinComb::from(a).constant(-C::F::ONE), &b.into());
      // c == 0
      circuit.constrain_equal_to_zero(c.into());
      // Push the constrained bit to the result
      res.push(a);
    }

    /*
      The eVRF paper describes commiting to $k$ (sampled from $[0, s - 1]$) over $G_{T,1}$.
      $G_{T,1}$ is of order $q$, enabling an adversary to sample from $[0, s - 1 - q]$ and open as
      $k$ or $k + q$, or to sample from $[q, s - 1]$ and open as $k$ or $k - q$. This assumes
      $q < s$. We can add the bound $q < s$, yet for the popular secp256k1 curve, it inherently
      forms a cycle with secq256k1. The order of secq256k1 is greater than the order of secp256k1
      and would be disqualified by this bound, forcing finding (and justifying) an alternative
      curve.

      We instead don't require $k$ be committed over $G_{T,1}$. We require a commitment to $k_{hi}$
      and a distinct commitment to $k_{lo}$, where $k_{lo} = \sum^{l/2}_{i=0} 2**i * k_i$ and
      $k_{hi} = \sum^{l}_{i=(l/2)+1} 2**i * k_i$. This is safe so long as
      $((ceil_log_2(s) + 1) / 2) <= floor_log_2(q)$, which is a bound only unsatisfied by the
      insane.

      Distinctly, the eVRF paper describes a single Pedersen Commitment over multiple generators
      ($G_{T,n}$). This would be a vector commitment which Bulletproofs, as published, does _not_
      support. It's Generalized Bulletproofs which extends Bulletproofs' R1CS statement regarding
      vector commitments.

      Instead of using Generalized Bulletproofs extension of the Bulletproofs' R1CS statement, we
      simply use multiple Pedersen Commitments. This transforms the singular Pedersen Vector
      Commitment $T = Q + Y$ to the three Pedersen Commitments $Q_{lo}, Q_{hi}, Y$. Since
      $Q_{lo}, Q_{hi}$ is from the setup, this does not increase the proof size directly.

      We do need a slightly modified opening of $Y$ however. $Y$ is written as the output of the
      eVRF scaling a binding generator, yet here, it's a full Pedersen Commitment. We accordingly
      need to prove the opening of the Pedersen Commitment $Y = y * G + r * H$, which requires
      revealing $Y' = y * G$ and performing a proof of knowledge for the resulting $Y - Y'$. This
      only adds transmission of a single element, $Y'$, as the proof of knowledge for $Y - Y'$
      over $H$ is of equivalent complexity to the originally required proof of knowledge for $Y$
      over $G_{T,2}$. This has the note it's incomplete as we don't prove $Y'$ solely has a
      discrete logarithm over $G$, either proving a weaker statement or requiring an additional
      proof of knowledge.

      If we were to use Pedersen Vector Commitments, we could use a single Pedersen Vector
      Commitment for the entire bitstring of the scalar. To do so with Pedersen Commitments
      wouldn't increase the bandwidth of each invocation, yet would increase the verification time
      (due to all of those individual Pedersen Commitments needing to be scaled within the
      multi-scalar multiplication). Using a Pedersen Vector Commitment does not increase the
      verification time compared to sending the two Pedersen Commitments $Q, Y$ and out-performs
      the current solution of $Q_{lo}, Q_{hi}, Y$ regarding points novel to the multi-scalar
      multiplication. It also removes the bit constraints per invocation, potentially shrinking the
      constant reference string.

      Finally, it is possible to perform a setup which cannot ever be invoked due to the lack of
      range proofs on $Q_{lo}, Q_{hi}$. This is inherent to the originally proposed eVRF as well
      when $ceil_log_2(q) > ceil_log_2(s)$.
    */
    {
      assert!(F::NUM_BITS.div_ceil(2) <= C::F::CAPACITY);
      {
        let mut two_i = C::F::ONE;
        let mut lo = LinComb::empty();
        for i in 0 ..= (F::CAPACITY / 2) {
          lo = lo.term(two_i, res[usize::try_from(i).unwrap()]);
          two_i = two_i.double();
        }
        circuit.equality(lo, &LinComb::from(Variable::V(0)));
      }
      {
        let mut two_i = C::F::ONE;
        let mut hi = LinComb::empty();
        for i in ((F::CAPACITY / 2) + 1) ..= F::CAPACITY {
          hi = hi.term(two_i, res[usize::try_from(i).unwrap()]);
          two_i = two_i.double();
        }
        circuit.equality(hi, &LinComb::from(Variable::V(1)));
      }
    }

    Self(res)
  }
}

// Equation 13
#[allow(non_camel_case_types)]
struct Delta_i<F: PrimeField>(Vec<(F, F, F, F)>);
impl<F: PrimeField> Delta_i<F> {
  // We preprocess this for a point...
  fn new<G: EmbeddedCurve<FieldElement = F>>(C: &[G], C_xy: &CXY<F>, X: &[G]) -> Self {
    Self(
      (0 ..= usize::try_from(G::Scalar::CAPACITY).unwrap())
        .map(|i| {
          let (x, y) = {
            let delta = X[i] + C[i];
            delta.to_xy().unwrap()
          };
          let (x_apostrophe, y_apostrophe) = {
            #[allow(clippy::let_and_return)]
            let delta_apostrophe = C_xy.0[i];
            delta_apostrophe
          };
          let delta_x = x - x_apostrophe;
          let delta_y = y - y_apostrophe;
          (delta_x, delta_y, x_apostrophe, y_apostrophe)
        })
        .collect(),
    )
  }

  // ... and allow fetching the exact constraints for specific variables later
  // In practice, this lets us reuse these calculcations between prover and verifier
  fn delta_i(&self, i: usize, k_i: Variable) -> (LinComb<F>, LinComb<F>) {
    let (delta_x, delta_y, x_apostrophe, y_apostrophe) = self.0[i];
    (
      LinComb::empty().term(delta_x, k_i).constant(x_apostrophe),
      LinComb::empty().term(delta_y, k_i).constant(y_apostrophe),
    )
  }
}

// Equation 10
#[allow(non_camel_case_types)]
struct P_iIterator<'a, G: EmbeddedCurve> {
  C: &'a [G],
  X: &'a [G],
  iter: core::iter::Enumerate<crate::ToLeBits<G::Scalar>>,
  last: Zeroizing<G>,
}
impl<'a, G: EmbeddedCurve> P_iIterator<'a, G> {
  fn new(C: &'a [G], X: &'a [G], k: &G::Scalar) -> Self {
    Self { C, X, iter: crate::const_to_le_bits(k).enumerate(), last: Zeroizing::new(G::identity()) }
  }
}
impl<G: EmbeddedCurve> Iterator for P_iIterator<'_, G> {
  type Item = Zeroizing<G>;
  fn next(&mut self) -> Option<Self::Item> {
    let (i, bit) = self.iter.next().unwrap();
    if i == 0 {
      let P_0 = Zeroizing::new(G::conditional_select(&self.C[i], &(self.X[i] + self.C[i]), bit));
      self.last = P_0.clone();
      Some(P_0)
    } else {
      let delta_i =
        Zeroizing::new(G::conditional_select(&self.C[i], &(self.X[i] + self.C[i]), bit));
      let P_i = Zeroizing::new(*self.last + delta_i.deref());
      self.last = P_i.clone();
      Some(P_i)
    }
  }
}

// Claim 2
struct P;
impl P {
  fn evaluate<C: Ciphersuite, G: EmbeddedCurve<FieldElement = C::F>>(
    circuit: &mut Circuit<C>,
    C: &[G],
    X: &[G],
    delta_i: &Delta_i<G::FieldElement>,
    k: Option<&G::Scalar>,
    discrete_logarithm: &DiscreteLogarithm,
  ) -> Variable {
    // "First, for i = 1,...l, verify that the point P_i ... is a point"
    let res = {
      let mut P_i =
        k.map(|k| P_iIterator::new(C, X, k).skip(1).map(|point| point.to_xy().unwrap()));
      let mut res = Vec::with_capacity(G::Scalar::CAPACITY.try_into().unwrap());
      for _ in 1 ..= G::Scalar::CAPACITY {
        let P_i = P_i.as_mut().map(|iter| iter.next().unwrap());
        // Calculate x**2
        let (x, other_x, x2) = circuit.mul(None, None, P_i.map(|(x, _y)| (x, x)));
        circuit.equality(x.into(), &other_x.into());
        // Calculate x**3
        let (_a, _b, x3) =
          circuit.mul(Some(x2.into()), Some(x.into()), P_i.map(|(x, _y)| (x * x, x)));
        // Calculate y**2
        let (y, other_y, y2) = circuit.mul(None, None, P_i.map(|(_, y)| (y, y)));
        circuit.equality(y.into(), &other_y.into());
        // Constrain y**2 = x**3 + ax + b
        circuit.equality(y2.into(), &LinComb::from(x3).term(G::a(), x).constant(G::b()));
        res.push((x, y));
      }
      res
    };

    // "verify that P_0 is constructed correctly, and this is done using (13)"
    let P_0 = {
      let (delta_0_x, delta_0_y) = delta_i.delta_i(0, discrete_logarithm.0[0]);
      let witness = circuit.eval(&delta_0_x).map(|a| {
        let b = circuit.eval(&delta_0_y).unwrap();
        (a, b)
      });
      // We don't need their product, solely that they're committed to and constrained
      let (x, y, _c) = circuit.mul(Some(delta_0_x), Some(delta_0_y), witness);
      (x, y)
    };

    // "Second, for i = 1,...,l, verify that the points ... are co-linear"
    for i in 1 ..= usize::try_from(G::Scalar::CAPACITY).unwrap() {
      let P_i_minus_1 = if i == 1 { P_0 } else { res[i - 2] };
      let P_i = res[i - 1];

      let (delta_i_x, delta_i_y) = delta_i.delta_i(i, discrete_logarithm.0[i]);

      // Equation 14
      let lhs = {
        let lhs_a = LinComb::from(P_i_minus_1.1).term(C::F::ONE, P_i.1);
        let lhs_b = delta_i_x.term(-C::F::ONE, P_i.0);
        let witness = circuit.eval(&lhs_a).map(|a| {
          let b = circuit.eval(&lhs_b).unwrap();
          (a, b)
        });
        let (_a, _b, lhs) = circuit.mul(Some(lhs_a), Some(lhs_b), witness);
        lhs
      };
      let rhs = {
        let rhs_a = delta_i_y.term(C::F::ONE, P_i.1);
        let rhs_b = LinComb::from(P_i_minus_1.0).term(-C::F::ONE, P_i.0);
        let witness = circuit.eval(&rhs_a).map(|a| {
          let b = circuit.eval(&rhs_b).unwrap();
          (a, b)
        });
        let (_a, _b, rhs) = circuit.mul(Some(rhs_a), Some(rhs_b), witness);
        rhs
      };
      circuit.equality(lhs.into(), &rhs.into());
    }

    // Return the x coordinate of the final point
    res[usize::try_from(G::Scalar::CAPACITY).unwrap() - 1].0
  }
}

/*
  This circuit is universal to all invocations *for the specified points*. We take advantage of
  this to minimize verification time by simply cloning (not rebuilding) this whenever we have a new
  instance.

  Unfortunately, the underlying circuit abstraction fundamentally insists on being either the
  prover or the verifier. This means the prover must do `CommonCircuit::new(..., Some(k))` and the
  verifier must do `CommonCircuit::new(..., None)`, unable to share those builds. To minimize the
  pain of this, we preprocess all of the elliptic curve operations before `CommonCircuit::new`.
  This means we only duplicate the allocation/formatting of the constraints themselves.
*/
#[derive(Clone)]
struct CommonCircuit<C: Ciphersuite>(Circuit<C>, Variable, Variable);
impl<C: Ciphersuite> CommonCircuit<C> {
  fn new<G: EmbeddedCurve<FieldElement = C::F>>(
    C: &[G],
    X_0: &[G],
    X_0_delta_i: &Delta_i<C::F>,
    X_1: &[G],
    X_1_delta_i: &Delta_i<C::F>,
    mut circuit: Circuit<C>,
    k: Option<&G::Scalar>,
  ) -> Self {
    let discrete_logarithm = DiscreteLogarithm::commit(&mut circuit, k);

    let dh_x_0_x = P::evaluate(&mut circuit, C, X_0, X_0_delta_i, k, &discrete_logarithm);
    let dh_x_1_x = P::evaluate(&mut circuit, C, X_1, X_1_delta_i, k, &discrete_logarithm);

    Self(circuit, dh_x_0_x, dh_x_1_x)
  }

  // Bind this common circuit to a specific instance
  fn bind(self, k_apostrophe: C::F) -> Circuit<C> {
    let Self(mut circuit, dh_x_0_x, dh_x_1_x) = self;
    circuit.equality(
      LinComb::from(dh_x_1_x).term(k_apostrophe, dh_x_0_x),
      &LinComb::from(Variable::V(2)),
    );
    circuit
  }
}

/// The global setup for the DDH eVRF.
#[derive(Clone)]
pub struct DdhEvrfGlobalSetup<C: Ciphersuite, G: EmbeddedCurve<FieldElement = C::F>> {
  generators: Generators<C>,
  C: Vec<G>,
  C_xy: CXY<G::FieldElement>,
}

/// The view of a setup for the DDH eVRF.
/*
  We use a slightly modified setup from $Q, k', \pi_Q$ to $Q_{lo}, Q_{hi}$. We derive $k'$ as the
  hash of $Q_{lo}, Q_{hi}$, which is a uniform value effectively random yet without communication
  overhead. We drop $\pi_Q$ as $\pi_Q$ is necessary when $Q$ is intended to be over a single
  generator for its later summation into a Pedersen Vector Commitment. As extensively described
  above, we don't use our $Q_{lo}, Q_{hi}$ values as such. Our Bulletproofs do assert they're
  well-formed without risk of side effects (as they are treated as independent Pedersen
  Commitments). While the prover may perform the setup with a $Q_{lo}, Q_{hi}$ they cannot open,
  they could already so by committing to a $k$ value greater than or equal to $2**ceil_log_2(s)$.
*/
#[derive(Clone)]
pub struct DdhEvrfSetupView<C: Ciphersuite> {
  Q_lo: C::G,
  Q_hi: C::G,
  k_apostrophe: C::F,
  Q_serialization: Vec<u8>,
}
impl<C: Ciphersuite> DdhEvrfSetupView<C> {
  fn new(Q_lo: C::G, Q_hi: C::G) -> Self {
    let k_apostrophe = C::reduce_512({
      let mut hasher = blake3::Hasher::new();
      hasher.update(Q_lo.to_bytes().as_ref());
      hasher.update(Q_hi.to_bytes().as_ref());
      let mut bytes = [0; 64];
      hasher.finalize_xof().fill(&mut bytes);
      bytes
    });

    let mut Q_serialization =
      Vec::with_capacity(2 * <C::G as GroupEncoding>::Repr::default().as_ref().len());
    Q_serialization.extend(Q_lo.to_bytes().as_ref());
    Q_serialization.extend(Q_hi.to_bytes().as_ref());

    DdhEvrfSetupView { Q_lo, Q_hi, k_apostrophe, Q_serialization }
  }
}

/// A setup for the eVRF.
#[derive(Clone)]
pub struct DdhEvrfSetup<C: Ciphersuite, G: EmbeddedCurve<FieldElement = C::F>> {
  k: Zeroizing<G::Scalar>,
  Q_lo: Zeroizing<PedersenCommitment<C>>,
  Q_lo_commitment: C::G,
  Q_hi: Zeroizing<PedersenCommitment<C>>,
  Q_hi_commitment: C::G,
  k_apostrophe: C::F,
}

/// The context for the DDH eVRF.
pub struct DdhEvrfContext<C: Ciphersuite, G: EmbeddedCurve<FieldElement = C::F>> {
  X_0: Vec<G>,
  X_0_delta_i: Delta_i<G::FieldElement>,
  X_1: Vec<G>,
  X_1_delta_i: Delta_i<G::FieldElement>,
  verifier_circuit: CommonCircuit<C>,
}

fn random_point<G: GroupEncoding>(xof: &mut blake3::OutputReader) -> G {
  loop {
    let mut bytes = G::Repr::default();
    xof.fill(bytes.as_mut());
    if let Some(point) = Option::<G>::from(G::from_bytes(&bytes)) {
      break point;
    }
  }
}

/// The DDH-premised eVRF proposed within the eVRF paper.
pub struct DdhEvrf<C: Ciphersuite, G: EmbeddedCurve<FieldElement = C::F>>(PhantomData<(C, G)>);
impl<
  CG: class_groups::Element,
  P: Parameters<CG>,
  C: Ciphersuite<G = P::E, F = P::F>,
  G: EmbeddedCurve<FieldElement = C::F>,
> Evrf<CG, P> for DdhEvrf<C, G>
{
  type GlobalSetup = DdhEvrfGlobalSetup<C, G>;
  type SetupView = DdhEvrfSetupView<C>;
  type Setup = DdhEvrfSetup<C, G>;
  type Context = DdhEvrfContext<C, G>;
  type BatchVerifier = BatchVerifier<C>;

  fn global_setup() -> Self::GlobalSetup {
    let generators = {
      let mut xof = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"DDH eVRF Generators");
        hasher.finalize_xof()
      };
      let h = random_point::<C::G>(&mut xof);
      let generators = usize::try_from((16 * G::Scalar::NUM_BITS).next_power_of_two()).unwrap();
      let mut g_bold = Vec::with_capacity(generators);
      let mut h_bold = Vec::with_capacity(generators);
      for _ in 0 .. generators {
        g_bold.push(random_point::<C::G>(&mut xof));
        h_bold.push(random_point::<C::G>(&mut xof));
      }
      Generators::new(C::G::generator(), h, g_bold, h_bold).unwrap()
    };
    let C = C::<G>();
    let C_xy = CXY::new::<G>(&C);

    DdhEvrfGlobalSetup { generators, C, C_xy }
  }

  fn setup(
    global_setup: &Self::GlobalSetup,
    rng: &mut (impl RngCore + CryptoRng),
  ) -> (Self::SetupView, Self::Setup) {
    let k = loop {
      let candidate = Zeroizing::new(G::Scalar::random(&mut *rng));
      // Negligible probability yet would be invalid
      if bool::from(candidate.is_zero()) {
        continue;
      }
      break candidate;
    };

    let mut bit_iter = crate::const_to_le_bits(k.deref());

    let mut lo = Zeroizing::new(C::F::ZERO);
    let mut bit_pos = C::F::ONE;
    for _ in 0 ..= (G::Scalar::CAPACITY / 2) {
      let bit = bit_iter.next().unwrap();
      *lo += C::F::conditional_select(&C::F::ZERO, &bit_pos, bit);
      bit_pos = bit_pos.double();
    }

    let mut hi = Zeroizing::new(C::F::ZERO);
    let mut bit_pos = C::F::ONE;
    for bit in bit_iter {
      *hi += C::F::conditional_select(&C::F::ZERO, &bit_pos, bit);
      bit_pos = bit_pos.double();
    }

    /*
      TODO: This probably needs a range proof that `k` is in the range `[1, s - 1]`. Else, the
      prover can commit to `0` or `s` and trigger `P_l == identity`, breaking the incomplete
      addition rules performed.

      Specifically, we'd have a proof that the bit decomposition of these Pedersen commitments is
      known, of the expected length, has a non-zero sum, and is less than `s`. The last check would
      be checking that if `s_i` is `0`, `(less == 1) || (k_i == 0)`. If `s_i` is `1`, then
      `less = less || (k_i == 0)`, where `i` is iterated from `0` to `l`.

      We don't include this range proof currently as the protocol, as implemented in this proof of
      concept, is only provided with a dealer key-generation (a trusted setup). Such a proof,
      necessary for a distributed setup, would not affect the performance of the signing protocol
      this implementation exists to benchmark.
    */
    let Q_lo =
      Zeroizing::new(PedersenCommitment::<C> { value: *lo, mask: C::F::random(&mut *rng) });
    let Q_hi =
      Zeroizing::new(PedersenCommitment::<C> { value: *hi, mask: C::F::random(&mut *rng) });
    let setup_view = DdhEvrfSetupView::new(
      Q_lo.commit(global_setup.generators.g(), global_setup.generators.h()),
      Q_hi.commit(global_setup.generators.g(), global_setup.generators.h()),
    );
    let setup = DdhEvrfSetup {
      k,
      Q_lo,
      Q_lo_commitment: setup_view.Q_lo,
      Q_hi,
      Q_hi_commitment: setup_view.Q_hi,
      k_apostrophe: setup_view.k_apostrophe,
    };
    (setup_view, setup)
  }

  fn context(global_setup: &Self::GlobalSetup, transcript: &mut blake3::Hasher) -> Self::Context {
    let mut xof = transcript.finalize_xof();
    transcript.update(&[0]);

    let one_X_0 = random_point::<G>(&mut xof);
    let one_X_1 = random_point::<G>(&mut xof);

    let mut X_0 = Vec::with_capacity(G::Scalar::NUM_BITS.try_into().unwrap());
    X_0.push(one_X_0);
    let mut X_1 = Vec::with_capacity(G::Scalar::NUM_BITS.try_into().unwrap());
    X_1.push(one_X_1);
    for _ in 1 ..= G::Scalar::CAPACITY {
      let two_i_X_0 = X_0.last().unwrap().double();
      X_0.push(two_i_X_0);

      let two_i_X_1 = X_1.last().unwrap().double();
      X_1.push(two_i_X_1);
    }

    let X_0_delta_i = Delta_i::new(&global_setup.C, &global_setup.C_xy, &X_0);
    let X_1_delta_i = Delta_i::new(&global_setup.C, &global_setup.C_xy, &X_1);
    let verifier_circuit = CommonCircuit::new(
      &global_setup.C,
      &X_0,
      &X_0_delta_i,
      &X_1,
      &X_1_delta_i,
      Circuit::verify(),
      None,
    );
    DdhEvrfContext { X_0, X_0_delta_i, X_1, X_1_delta_i, verifier_circuit }
  }

  fn prove<W: io::Write>(
    rng: &mut (impl RngCore + CryptoRng),
    global_setup: &Self::GlobalSetup,
    setup: &Self::Setup,
    context: &Self::Context,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<Zeroizing<P::F>> {
    let ecdh_0 = Zeroizing::new(Zeroizing::new(context.X_0[0] * setup.k.deref()).to_xy().unwrap());
    let ecdh_1 = Zeroizing::new(Zeroizing::new(context.X_1[0] * setup.k.deref()).to_xy().unwrap());
    let nonce = Zeroizing::new((ecdh_0.deref().0 * setup.k_apostrophe) + ecdh_1.deref().0);

    let nonce_mask = Zeroizing::new(C::F::random(&mut *rng));
    let Y = PedersenCommitment::<C> { value: *nonce, mask: *nonce_mask };

    let Y_commitment = Y.commit(global_setup.generators.g(), global_setup.generators.h());

    let circuit = CommonCircuit::new(
      &global_setup.C,
      &context.X_0,
      &context.X_0_delta_i,
      &context.X_1,
      &context.X_1_delta_i,
      Circuit::prove(vec![], vec![*setup.Q_lo, *setup.Q_hi, Y]),
      Some(&setup.k),
    )
    .bind(setup.k_apostrophe);
    let muls = circuit.muls();

    let mut bp_transcript = transcript::Transcript::new(transcript.0.finalize().into());
    let commitments = bp_transcript.write_commitments::<C>(
      vec![],
      vec![setup.Q_lo_commitment, setup.Q_hi_commitment, Y_commitment],
    );

    let (statement, witness) = circuit
      .statement(global_setup.generators.reduce(muls.next_power_of_two()).unwrap(), commitments)
      .unwrap();
    let witness = witness.unwrap();
    statement.prove(&mut *rng, &mut bp_transcript, witness).unwrap();
    let bp = bp_transcript.complete();
    // Write everything after $Q_{hi}, Q_{lo}$
    transcript.write_all(&bp[(2 * <C::G as GroupEncoding>::Repr::default().as_ref().len()) ..])?;

    // Open the Pedersen commitment
    transcript.write_all((global_setup.generators.g() * nonce.deref()).to_bytes().as_ref())?;

    // Prove the opening of the Pedersen commitment
    // We do prove the opening of `Y'` and `r * H` to ensure this proves the proper statement, even
    // though the round-one proofs should prove themselves for knowledge of `Y'`
    {
      let r_nonce = Zeroizing::new(C::F::random(&mut *rng));
      let r_nonce_mask = Zeroizing::new(C::F::random(rng));
      transcript.write_all((global_setup.generators.g() * r_nonce.deref()).to_bytes().as_ref())?;
      transcript
        .write_all((global_setup.generators.h() * r_nonce_mask.deref()).to_bytes().as_ref())?;
      let c = P::from_xof(transcript.0.finalize_xof());
      transcript.write_all(((c * nonce.deref()) + r_nonce.deref()).to_repr().as_ref())?;
      transcript.write_all(((c * nonce_mask.deref()) + r_nonce_mask.deref()).to_repr().as_ref())?;
    }

    Ok(nonce)
  }

  fn batch_verifier(_global_setup: &Self::GlobalSetup) -> Self::BatchVerifier {
    Generators::batch_verifier()
  }
  fn queue_verification<R: io::Read>(
    rng: &mut (impl RngCore + CryptoRng),
    global_setup: &Self::GlobalSetup,
    batch_verifier: &mut Self::BatchVerifier,
    participant: dkg::Participant,
    setup: &Self::SetupView,
    context: &Self::Context,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<P::E> {
    let circuit = context.verifier_circuit.clone().bind(setup.k_apostrophe);
    let muls = circuit.muls();

    let bp_context = transcript.0.finalize().into();

    let point_len = <C::G as GroupEncoding>::Repr::default().as_ref().len();
    let bp_len = {
      let scalar_len = <C::F as PrimeField>::Repr::default().as_ref().len();

      debug_assert_eq!(2u8.next_power_of_two(), 2);
      debug_assert_eq!(2u8.ilog2(), 1);
      // ((Q_hi, Q_lo), Y, (A_I, A_O, S), (T_0, T_1, T_3, T_4, T_5, T_6), (L_i, R_i))
      /*
        Please note we read $T_0$ from the transcript, when Bulletproofs doesn't, as Bulletproofs
        assumes it's zero yet Generalized Bulletproofs doesn't (though it will be in our
        invocation, as it's only non-zero when there's vector commitments).

        TODO: PR generalized-bulletproofs for this oddity
      */
      let points = 2 + 1 + 3 + 6 + (2 * usize::try_from(muls.next_power_of_two().ilog2()).unwrap());
      // (tau_x, u, \hat{t}, a, b)
      let scalars = 5;
      (points * point_len) + (scalars * scalar_len)
    };
    let mut bp = vec![0; bp_len];
    bp[.. (2 * point_len)].copy_from_slice(&setup.Q_serialization);
    transcript.read_exact(&mut bp[(2 * point_len) ..])?;

    let mut bp_transcript = transcript::VerifierTranscript::new(bp_context, &bp);
    let commitments = bp_transcript.read_commitments(0, 3)?;
    circuit
      .statement(global_setup.generators.reduce(muls).unwrap(), commitments)
      .unwrap()
      .0
      .verify(&mut *rng, batch_verifier, &mut bp_transcript)
      .map_err(|e| io::Error::other(format!("{e:?}")))?;

    // The Pedersen commitment for the nonce
    let Y_commitment = P::read_canonical_E(&mut &bp[(2 * point_len) ..])?;
    // The nonce itself
    let Y_apostrophe = P::read_canonical_E(&mut *transcript)?;

    {
      let R_nonce = P::read_canonical_E(&mut *transcript)?;
      let R_nonce_mask = P::read_canonical_E(&mut *transcript)?;
      let c = P::from_xof(transcript.0.finalize_xof());

      {
        let s_nonce = C::read_F(&mut *transcript)?;
        let weight = C::F::random(&mut *rng);
        // R
        batch_verifier.additional.push((weight, R_nonce));
        // + cX
        batch_verifier.additional.push((weight * c, Y_apostrophe));
        // - sG == 0
        batch_verifier.g -= weight * s_nonce;
      }

      {
        let s_nonce_mask = C::read_F(&mut *transcript)?;
        let weight = C::F::random(&mut *rng);
        batch_verifier.additional.push((weight, R_nonce_mask));
        batch_verifier.additional.push((weight * c, (Y_commitment - Y_apostrophe)));
        batch_verifier.h -= weight * s_nonce_mask;
      }
    }

    Ok(Y_apostrophe)
  }
  fn verify(
    global_setup: &Self::GlobalSetup,
    batch_verifier: Self::BatchVerifier,
  ) -> Result<(), Vec<dkg::Participant>> {
    if !global_setup.generators.verify(batch_verifier) {
      todo!("TODO");
    }
    Ok(())
  }
}

#[test]
fn test_ddh_evrf() {
  type EvrfInstantiated = DdhEvrf<ciphersuite::Secp256k1, secq256k1::Point>;
  type Parameters = crate::Secp256k1<class_groups::MalachiteElement, crate::CryptoPrimesStackCcykc>;

  let global_setup = <EvrfInstantiated as Evrf<_, Parameters>>::global_setup();

  let (setup_view, setup) =
    <EvrfInstantiated as Evrf<_, Parameters>>::setup(&global_setup, &mut rand_core::OsRng);

  let context =
    <EvrfInstantiated as Evrf<_, Parameters>>::context(&global_setup, &mut blake3::Hasher::new());

  let mut transcript = DigestWriter(blake3::Hasher::new(), vec![]);
  let nonce = <EvrfInstantiated as Evrf<_, Parameters>>::prove(
    &mut rand_core::OsRng,
    &global_setup,
    &setup,
    &context,
    &mut transcript,
  )
  .unwrap();

  let mut batch_verifier = <EvrfInstantiated as Evrf<_, Parameters>>::batch_verifier(&global_setup);
  let mut transcript = DigestReader(blake3::Hasher::new(), transcript.1.as_slice());
  let nonce_commitment = <EvrfInstantiated as Evrf<_, Parameters>>::queue_verification(
    &mut rand_core::OsRng,
    &global_setup,
    &mut batch_verifier,
    dkg::Participant::new(1).unwrap(),
    &setup_view,
    &context,
    &mut transcript,
  )
  .unwrap();
  assert_eq!(k256::ProjectivePoint::GENERATOR * *nonce, nonce_commitment);
  <EvrfInstantiated as Evrf<_, Parameters>>::verify(&global_setup, batch_verifier).unwrap();
}
