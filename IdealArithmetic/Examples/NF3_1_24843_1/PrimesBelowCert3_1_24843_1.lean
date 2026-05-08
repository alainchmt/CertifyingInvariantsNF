import IdealArithmetic.Examples.NF3_1_24843_1.PrimesBelow3_1_24843_1F0
import IdealArithmetic.Examples.NF3_1_24843_1.PrimesBelow3_1_24843_1F1
import IdealArithmetic.Computation.PrimeSieve

noncomputable section

lemma PB45I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 44 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 44 (by omega)

def PB45I0 : PrimesBelowBoundCertificateInterval O 1 44 45 where
  m := 14
  g := ![2, 3, 2, 3, 2, 3, 2, 1, 2, 2, 3, 1, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
  hP := PB45I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N0, I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
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
    · exact PBC43
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 2]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![529, 23]
    · exact ![841, 29]
    · exact ![31, 31, 31]
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![79507]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N0
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N0, I7N0], [I11N1], [I13N0, I13N0, I13N0], [I17N1], [], [I23N1], [I29N1], [I31N0, I31N1, I31N2], [], [I41N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

def PB45 : PrimesBelowBoundCertificate O 45 := by
  refine primesBelowBoundCertificate_of_Interval O ![1, 44] 44 rfl rfl ?_ ?_
  · decide
  · rintro ⟨i,hi⟩
    interval_cases i 
    exact PB45I0
