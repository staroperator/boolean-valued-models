# Boolean Valued Models

This repository aims to formalize Boolean valued models and independence proofs in set theory,
including porting certain results in [Flypitch](https://github.com/flypitch/flypitch) into Lean 4.

## Formalized results

This repository is still in an early stage.

- ZFC can not prove CH:
  ```lean
  theorem zfc_not_entails_ch : ¬ ZFC ⊨ᵇ CH
  ```

## References

Textbooks
1. J. L. Bell, *Boolean-Valued Models and Independence Proofs in Set Theory*.
2. Thomas Jech, *Set Theory*.
3. Kenneth Kunen, *Set Theory: An Introduction to Independence Proofs*.

Papers
1. Jesse Michael Han and Floris van Doorn, *A formal proof of the independence of the continuum hypothesis*.
