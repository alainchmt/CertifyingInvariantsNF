import IdealArithmetic.Examples.NF2_0_231_1.PrimesBelow2_0_231_1F0
import IdealArithmetic.Computation.PrimeSieve

noncomputable section

lemma PB10I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 9 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 9 (by omega)

def PB10I0 : PrimesBelowBoundCertificateInterval O 1 9 10 where
  m := 4
  g := ![2, 2, 2, 2]
  P := ![2, 3, 5, 7]
  hP := PB10I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2]
    · exact ![3, 3]
    · exact ![5, 5]
    · exact ![7, 7]
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
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
  Il := ![[I2N0, I2N1], [I3N0, I3N0], [I5N0, I5N1], [I7N0, I7N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

def PB10 : PrimesBelowBoundCertificate O 10 := by
  refine primesBelowBoundCertificate_of_Interval O ![1, 9] 9 rfl rfl ?_ ?_
  · decide
  · rintro ⟨i,hi⟩
    interval_cases i 
    exact PB10I0
