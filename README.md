# Formally certifying invariants of number fields in Lean

Building on previous work on certifying rings of integers, this work extends this certification approach to further number field invariants including the signature and the unit group modulo $p$-th powers, culminating in the class group. We also improve discriminant certification, allowing verifications for higher-degree number fields infeasible in previous work.

This work builds on [RingOfIntegersProject](https://github.com/alainchmt/RingOfIntegersProject), for verifying rings of integers. The `IdealArithmetic/DedekindProject/` folder is ported from that project (updated to use Mathlib's definitions of the resultant and discriminant of polynomials). 


## Examples in Lean
Each certified number field has its own folder under `IdealArithmetic/Examples/` named `NF<label>`, where `<label>` is the [LMFDB](https://www.lmfdb.org/NumberField/) label of that number field, replacing dots with underscores. 

In each folder, the file `Results<label>.lean` is the summary file. Besides a proof of the ring of integers, it contains proofs of the discriminant, the number of real and complex places (signature), the class group structure and the class number. 

For example, the number field with defining polynomial $X^5 - X^4 + 3X^2 + 21X + 4$ has label `5.1.3790297.2` in the LMFDB. Proofs of its invariants are found in 
`IdealArithmetic/Examples/NF5_1_3790297_2/Results5_1_3790297_2`. 

## SageMath script
- `InvariantsNFLean.sage` : The function `generate_invariants_proof_lean` takes as input a defining polynomial with integer coefficients, an integral basis, and a naming label, and outputs a `NF<label>` folder with the .lean files certifying the invariants. For verification, this file must be placed in `IdealArithmetic/Examples/`. 

## Timing files 
- `degree3_timing.csv` : contains the names and corresponding verification timings of the degree-3 number fields we verified. 
- `degree5_timing.csv` : contains the names and corresponding verification timings of the degree-5 number fields we verified. 
