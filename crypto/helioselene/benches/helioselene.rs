#![allow(non_snake_case)]

use std::time;

use rand_core::OsRng;
use helioselene::{
  group::{ff::Field, Group, GroupEncoding},
  HelioseleneField, SelenePoint,
};

macro_rules! run_bench {
  ($name: literal, $op:expr, $n_iters:expr) => {{
    let start = time::Instant::now();
    for _ in 0 .. $n_iters {
      let _ = core::hint::black_box($op);
    }
    let time_to_run = (time::Instant::now() - start).as_millis();

    println!("{} took {}ms", $name, time_to_run);
  }};
}

fn main() {
  let A_S = SelenePoint::random(&mut OsRng);
  let B_S = SelenePoint::random(&mut OsRng);

  let a_h = HelioseleneField::random(&mut OsRng);
  let b_h = HelioseleneField::random(&mut OsRng);

  let A_S_bytes = A_S.to_bytes();

  run_bench!("Selene Point add", A_S + B_S, 2_000_000);
  run_bench!("helioselene mul", a_h * b_h, 50_000_000);
  run_bench!("helioselene invert", a_h.invert(), 200_000);
  run_bench!("Selene Point from_bytes", SelenePoint::from_bytes(&A_S_bytes), 100_000);
  run_bench!("helioselene add", a_h + b_h, 200_000_000);
  run_bench!("helioselene sub", a_h - b_h, 200_000_000);
}
