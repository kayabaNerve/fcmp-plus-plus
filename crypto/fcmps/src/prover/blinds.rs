use core::ops::Deref;

use zeroize::{Zeroize, Zeroizing};

use ciphersuite::group::{
  ff::{PrimeFieldBits, PrimeField},
  prime::PrimeGroup,
};

use ec_divisors::{Poly, DivisorCurve, ScalarDecomposition};

use std_shims::io;

use crate::{Output, Input, FcmpError};

#[derive(Clone, Zeroize)]
pub(crate) struct ScalarMulAndDivisor<G: DivisorCurve + PrimeGroup> {
  /// The point resulting from this scalar multiplication.
  pub(crate) point: Zeroizing<G>,
  /// The `x` coordinate of the result of this scalar multiplication.
  pub(crate) x: G::FieldElement,
  /// The `y` coordinate of the result of this scalar multiplication.
  pub(crate) y: G::FieldElement,
  /// The divisor interpolating the inverse of this result with instances of `2**i G`, where `G` is
  /// some generator.
  pub(crate) divisor: Poly<G::FieldElement>,
}

// Helper function to read a point
fn read_point<G: PrimeGroup>(r: &mut impl io::Read) -> io::Result<G> {
  let mut repr = G::Repr::default();
  r.read_exact(repr.as_mut())?;
  let point = G::from_bytes(&repr);
  let Some(point) = Option::<G>::from(point) else {
    Err(io::Error::new(io::ErrorKind::Other, "invalid point"))?
  };
  if point.to_bytes().as_ref() != repr.as_ref() {
    Err(io::Error::new(io::ErrorKind::Other, "non-canonical point"))?;
  }
  Ok(point)
}

// Helper function to read a scalar
fn read_scalar<F: PrimeField>(r: &mut impl io::Read) -> io::Result<F> {
  let mut repr = F::Repr::default();
  r.read_exact(repr.as_mut())?;
  let scalar = F::from_repr(repr);
  if scalar.is_none().into() {
    Err(io::Error::new(io::ErrorKind::Other, "invalid scalar"))?;
  }
  Ok(scalar.unwrap())
}

impl<G: DivisorCurve + PrimeGroup> ScalarMulAndDivisor<G>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  fn new(A: G, scalar: &ScalarDecomposition<G::Scalar>) -> Self {
    let point = Zeroizing::new(A * scalar.scalar());
    let (x, y) = G::to_xy(*point).expect("zero scalar was decomposed");
    let divisor = scalar.scalar_mul_divisor(A).normalize_x_coefficient();
    ScalarMulAndDivisor { point, x, y, divisor }
  }

  pub fn write<W: io::Write>(&self, w: &mut W) -> io::Result<()> {
    w.write_all((*self.point).to_bytes().as_ref())?;
    w.write_all(self.x.to_repr().as_ref())?;
    w.write_all(self.y.to_repr().as_ref())?;
    self.divisor.write(w)
  }

  pub fn read(r: &mut impl io::Read) -> io::Result<Self> {
    let point = Zeroizing::new(read_point(r)?);
    let x = read_scalar(r)?;
    let y = read_scalar(r)?;
    let divisor = Poly::read(r)?;
    Ok(Self { point, x, y, divisor })
  }
}

/// A blind, prepared for usage within the circuit.
#[derive(Clone, Zeroize)]
pub(crate) struct PreparedBlind<G: DivisorCurve + PrimeGroup>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  pub(crate) scalar: ScalarDecomposition<G::Scalar>,
  pub(crate) scalar_mul_and_divisor: ScalarMulAndDivisor<G>,
}

impl<G: DivisorCurve + PrimeGroup> PreparedBlind<G>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  fn new(A: G, scalar: ScalarDecomposition<G::Scalar>) -> Self {
    let scalar_mul_and_divisor = ScalarMulAndDivisor::new(A, &scalar);
    PreparedBlind { scalar, scalar_mul_and_divisor }
  }

  pub fn write<W: io::Write>(&self, w: &mut W) -> io::Result<()> {
    self.scalar.write(w)?;
    self.scalar_mul_and_divisor.write(w)
  }

  pub fn read(r: &mut impl io::Read) -> io::Result<Self> {
    let scalar = ScalarDecomposition::<G::Scalar>::read(r)?;
    let scalar_mul_and_divisor = ScalarMulAndDivisor::<G>::read(r)?;
    Ok(Self { scalar, scalar_mul_and_divisor })
  }
}

/// A blind for `O` (the output's key).
#[derive(Clone, Zeroize)]
pub struct OBlind<G: DivisorCurve + PrimeGroup>(pub(crate) PreparedBlind<G>)
where
  G::Scalar: Zeroize + PrimeFieldBits;
impl<G: DivisorCurve + PrimeGroup> OBlind<G>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  /// Construct a new blind for `O`.
  ///
  /// This will calculate a divisor and is computationally non-trivial.
  pub fn new(T: G, scalar: ScalarDecomposition<G::Scalar>) -> Self
  where
    G::Scalar: Zeroize + PrimeFieldBits,
  {
    Self(PreparedBlind::new(T, scalar))
  }

  /// Write the OBlind
  pub fn write<W: io::Write>(&self, w: &mut W) -> io::Result<()> {
    self.0.write(w)
  }

  /// Read the OBlind
  pub fn read(r: &mut impl io::Read) -> io::Result<Self> {
    Ok(Self(PreparedBlind::<G>::read(r)?))
  }
}

/// A blind for `I` (the output's key image generator).
#[derive(Clone, Zeroize)]
pub struct IBlind<G: DivisorCurve + PrimeGroup>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  pub(crate) scalar: ScalarDecomposition<G::Scalar>,
  pub(crate) u: ScalarMulAndDivisor<G>,
  pub(crate) v: ScalarMulAndDivisor<G>,
}
impl<G: DivisorCurve + PrimeGroup> IBlind<G>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  /// Construct a new blind for `I`.
  ///
  /// This will calculate two divisors (distinct from the other blinds which only calculate one
  /// each) and is computationally non-trivial.
  pub fn new(U: G, V: G, scalar: ScalarDecomposition<G::Scalar>) -> Self {
    let u = ScalarMulAndDivisor::new(U, &scalar);
    let v = ScalarMulAndDivisor::new(V, &scalar);
    IBlind { scalar, u, v }
  }

  /// Write the IBlind
  pub fn write<W: io::Write>(&self, w: &mut W) -> io::Result<()> {
    self.scalar.write(w)?;
    self.u.write(w)?;
    self.v.write(w)
  }

  /// Read the IBlind
  pub fn read(r: &mut impl io::Read) -> io::Result<Self> {
    let scalar = ScalarDecomposition::<G::Scalar>::read(r)?;
    let u = ScalarMulAndDivisor::<G>::read(r)?;
    let v = ScalarMulAndDivisor::<G>::read(r)?;
    Ok(Self { scalar, u, v })
  }
}

/// A blind for `I`'s blind.
#[derive(Clone, Zeroize)]
pub struct IBlindBlind<G: DivisorCurve + PrimeGroup>(pub(crate) PreparedBlind<G>)
where
  G::Scalar: Zeroize + PrimeFieldBits;
impl<G: DivisorCurve + PrimeGroup> IBlindBlind<G>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  /// Construct a new blind for `I`'s blind.
  ///
  /// This will calculate a divisor and is computationally non-trivial.
  pub fn new(T: G, scalar: ScalarDecomposition<G::Scalar>) -> Self {
    Self(PreparedBlind::new(T, scalar))
  }

  /// Write the IBlindBlind
  pub fn write<W: io::Write>(&self, w: &mut W) -> io::Result<()> {
    self.0.write(w)
  }

  /// Read the IBlindBlind
  pub fn read(r: &mut impl io::Read) -> io::Result<Self> {
    Ok(Self(PreparedBlind::<G>::read(r)?))
  }
}

/// A blind for `C` (the output's commitment).
#[derive(Clone, Zeroize)]
pub struct CBlind<G: DivisorCurve + PrimeGroup>(pub(crate) PreparedBlind<G>)
where
  G::Scalar: Zeroize + PrimeFieldBits;
impl<G: DivisorCurve + PrimeGroup> CBlind<G>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  /// Construct a new blind for `C`.
  ///
  /// This will calculate a divisor and is computationally non-trivial.
  pub fn new(G: G, scalar: ScalarDecomposition<G::Scalar>) -> Self {
    Self(PreparedBlind::new(G, scalar))
  }

  /// Write the CBlind
  pub fn write<W: io::Write>(&self, w: &mut W) -> io::Result<()> {
    self.0.write(w)
  }

  /// Read the IBlindBlind
  pub fn read(r: &mut impl io::Read) -> io::Result<Self> {
    Ok(Self(PreparedBlind::<G>::read(r)?))
  }
}

/// All of the blinds used for an output, prepared for usage within the circuit.
#[derive(Clone, Zeroize)]
pub struct OutputBlinds<G: DivisorCurve + PrimeGroup>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  pub(crate) o_blind: OBlind<G>,
  pub(crate) i_blind: IBlind<G>,
  pub(crate) i_blind_blind: IBlindBlind<G>,
  pub(crate) c_blind: CBlind<G>,
}

impl<G: DivisorCurve + PrimeGroup> OutputBlinds<G>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  /// Construct a new blinded output.
  ///
  /// Returns `None` if any the points in the resulting `Input` would be identity. This should
  /// only happen with negligible probability unless the blinds are explicitly crafted for this
  /// purpose.
  pub fn new(
    o_blind: OBlind<G>,
    i_blind: IBlind<G>,
    i_blind_blind: IBlindBlind<G>,
    c_blind: CBlind<G>,
  ) -> Self {
    Self { o_blind, i_blind, i_blind_blind, c_blind }
  }

  /// Blind an output.
  pub(crate) fn blind(
    &self,
    output: &Output<G>,
  ) -> Result<Input<<G as DivisorCurve>::FieldElement>, FcmpError> {
    // We add the proven results of the blinds to the input tuple to recalculate the output
    // tuple
    // In order for `input_tuple_value + blind_value = output_tuple_value`,
    // `input_tuple_value = output_tuple_value - blind_value`
    let O_tilde = output.O - self.o_blind.0.scalar_mul_and_divisor.point.deref();
    let I_tilde = output.I - self.i_blind.u.point.deref();
    let C_tilde = output.C - self.c_blind.0.scalar_mul_and_divisor.point.deref();
    // I's blind's blind is not inverted, yet I's blind was prior inverted and remains
    // inverted
    let R = *self.i_blind_blind.0.scalar_mul_and_divisor.point - self.i_blind.v.point.deref();
    Input::new(O_tilde, I_tilde, R, C_tilde)
  }

  /// Write the OutputBlind to writable
  pub fn write<W: io::Write>(&self, w: &mut W) -> io::Result<()> {
    self.o_blind.write(w)?;
    self.i_blind.write(w)?;
    self.i_blind_blind.write(w)?;
    self.c_blind.write(w)
  }

  /// Read the OutputBlind
  pub fn read(r: &mut impl io::Read) -> io::Result<Self> {
    let o_blind = OBlind::<G>::read(r)?;
    let i_blind = IBlind::<G>::read(r)?;
    let i_blind_blind = IBlindBlind::<G>::read(r)?;
    let c_blind = CBlind::<G>::read(r)?;

    Ok(Self { o_blind, i_blind, i_blind_blind, c_blind })
  }
}

/// A blind for a branch.
#[derive(Clone, Zeroize)]
pub struct BranchBlind<G: DivisorCurve + PrimeGroup>(pub(crate) PreparedBlind<G>)
where
  G::Scalar: Zeroize + PrimeFieldBits;
impl<G: DivisorCurve + PrimeGroup> BranchBlind<G>
where
  G::Scalar: Zeroize + PrimeFieldBits,
{
  /// Construct a new blind for a branch.
  ///
  /// This will calculate a divisor and is computationally non-trivial.
  pub fn new(H: G, scalar: ScalarDecomposition<G::Scalar>) -> Self {
    Self(PreparedBlind::new(H, scalar))
  }

  /// Write the Branch Blind
  pub fn write<W: io::Write>(&self, w: &mut W) -> io::Result<()> {
    self.0.write(w)
  }

  /// Read the Branch Blind
  pub fn read(r: &mut impl io::Read) -> io::Result<Self> {
    Ok(Self(PreparedBlind::<G>::read(r)?))
  }
}
