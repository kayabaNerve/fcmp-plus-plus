# Helioselene

An Implementation of Helios and Selene, a curve cycle towering Ed25519.
Please refer to https://gist.github.com/tevador/4524c2092178df08996487d4e272b096
for documentation of these curves.

## Status

This library should be complete and constant time. It was implemented using
crypto-bigint's Residue type. While that enables basic tests for accuracy, it's
no where near performant enough for benchmarking, nor does it take advantage of
the form of the curve's primes *which is why this curve was chosen in the first
place*.

In order to be used in production, this library needs to be rewritten with
custom field implementations.
