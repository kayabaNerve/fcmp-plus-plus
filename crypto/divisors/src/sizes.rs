// f(x,y) = ax + by + c
// f(x,y) = A(x) - yB(x)
// A(x) = ax + c
// B(x) = b
// f1 * f2 = A1A2 - y(A1B2 + A2B1) + y^2 B1B2
// f1 * f2 = A1A2 - y(A1B2 + A2B1) + (x^3 + ax + b) B1B2
//
// (A1+B1)(A2+B2)
// A1(A2+B2) + B1(A2+B2)
// A1A2 + A1B2 + B1A2 + B1B2
// deg(A) = max (deg(A1) + deg(A2), deg(B1) + deg(B2) + 3)
// deg(B) = max (deg(A1) + deg(B2), deg(A2) + deg(B1))
//
// deg(f1f2f3) = ??
// deg(f1f2_A) = max(1+1,0+0+3) = 3
// deg(f1f2_B) = max(1+0,1+0) = 1
//
// deg(f1f2f3_A) = max(3+1,1+0+3) = 4
// deg(f1f2f3_B) = max(3+0,1+1) = 3
//
// lowered by denominator
// let f1 = f1f2f3, deg_A(f1) = 2, deg_B(f1) = 1
// let f2 = f1
// let f3; with deg(A) = 1, deg(B) = 0
//
// deg(f1f2) = ??
// deg(f1f2_A) = max(2+2,1+1+3) = 5
// deg(f1f2_B) = max(2+1,2+1) = 3
// deg(f1f2f3_A) = max(5+1,3+0+3) = 6
// deg(f1f2f3_B) = max(5+0,1+3) = 5
// deg(A) = 4, deg(B) = 3

#[cfg(test)]
fn sizes(a: usize, b: usize) -> (usize, usize) {
  // A = max (A1 + A2, B1 + B2 + 3)
  // B = max (A1 + B2, A2 + B1)
  let a1 = (a * 2).max(b * 2 + 3);
  let b1 = a + b;

  // a2 = 1, b2 = 0
  let a = (a1 + 1).max(b1 + 0 + 3);
  let b = (a1 + 0).max(1 + b1);

  (a - 2, b - 2)
}

#[test]
fn print_sizes() {
  let mut a = 1;
  let mut b = 0;
  for _ in 0 .. 20 {
    let res = sizes(a, b);
    a = res.0;
    b = res.1;
    println!("a: {}, b: {}", a, b);
  }
}
