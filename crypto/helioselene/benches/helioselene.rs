#![allow(non_snake_case)]

use rand_core::OsRng;
use helioselene::{
  group::{ff::Field, Group, GroupEncoding},
  HelioseleneField, SelenePoint,
};

macro_rules! run_bench {
  ($name: literal, $op:expr, $n_iters:expr) => {{
    #[cfg(target_arch = "x86")]
    let start = unsafe { core::arch::x86::_rdtsc() };
    #[cfg(target_arch = "x86_64")]
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    let start = std::time::Instant::now();
    for _ in 0 .. $n_iters {
      let _ = core::hint::black_box($op);
    }
    #[cfg(target_arch = "x86")]
    let time_to_run = unsafe { core::arch::x86::_rdtsc() } - start;
    #[cfg(target_arch = "x86_64")]
    let time_to_run = unsafe { core::arch::x86_64::_rdtsc() } - start;
    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    let time_to_run = (std::time::Instant::now() - start).as_millis();

    println!("{:<23} took {:>12} ticks", $name, time_to_run);
  }};
}

fn main() {
  let A_S = SelenePoint::random(&mut OsRng);
  let B_S = SelenePoint::random(&mut OsRng);

  let a_h = HelioseleneField::random(&mut OsRng);
  let b_h = HelioseleneField::random(&mut OsRng);

  let A_S_bytes = A_S.to_bytes();

  run_bench!("Selene Point add", A_S + B_S, 2_000_000);
  run_bench!("helioselene mul", a_h * b_h, 2_000_000_000);
  run_bench!("helioselene invert", a_h.invert(), 200_000);
  run_bench!("Selene Point from_bytes", SelenePoint::from_bytes(&A_S_bytes), 100_000);
  run_bench!("helioselene add", a_h + b_h, 2_000_000_000);
  run_bench!("helioselene sub", a_h - b_h, 2_000_000_000);
}
