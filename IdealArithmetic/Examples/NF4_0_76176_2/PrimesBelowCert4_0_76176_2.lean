import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F1
import IdealArithmetic.PrimeSieve
noncomputable section

lemma PB42I0_primes :
  ∀ (p : ℕ), p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 41 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB42I0 : PrimesBelowBoundCertificateInterval O 1 41 42 where
  m := 13
  g := ![4, 4, 2, 2, 2, 4, 2, 2, 4, 2, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
  hP := PB42I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![I2N0, I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2, I13N3]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N1, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2]
    · exact ![3, 3, 3, 3]
    · exact ![25, 25]
    · exact ![49, 49]
    · exact ![121, 121]
    · exact ![13, 13, 13, 13]
    · exact ![289, 289]
    · exact ![361, 361]
    · exact ![23, 23, 23, 23]
    · exact ![841, 841]
    · exact ![961, 961]
    · exact ![1369, 1369]
    · exact ![1681, 1681]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
      exact NI13N3
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N0
      exact NI23N1
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
  Il := ![[I2N0, I2N0, I2N1, I2N1], [I3N0, I3N0, I3N1, I3N1], [I5N0, I5N1], [], [], [I13N0, I13N1, I13N2, I13N3], [], [], [I23N0, I23N0, I23N1, I23N1], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

def PB42 : PrimesBelowBoundCertificate O 42 := by
  refine primesBelowBoundCertificate_of_Interval O ![1, 41] 41 rfl rfl ?_ ?_
  · decide
  · intro i
    match i with
    | 0 => exact PB42I0
