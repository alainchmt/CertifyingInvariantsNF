import IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F0
import IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F1
import IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F2
import IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F3
import IdealArithmetic.Computation.PrimeSieve

noncomputable section

lemma PB122I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 47 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 47 (by omega)

def PB122I0 : PrimesBelowBoundCertificateInterval O 1 47 122 where
  m := 15
  g := ![3, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
  hP := PB122I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2]
    · exact ![I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1, I7N1, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
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
    · exact PBC47
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 4, 4]
    · exact ![243]
    · exact ![25, 125]
    · exact ![49, 7, 7, 7]
    · exact ![121, 121, 11]
    · exact ![371293]
    · exact ![83521, 17]
    · exact ![2476099]
    · exact ![6436343]
    · exact ![24389, 841]
    · exact ![28629151]
    · exact ![1369, 37, 37, 37]
    · exact ![2825761, 41]
    · exact ![3418801, 43]
    · exact ![103823, 2209]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N1
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
  Il := ![[I2N0, I2N1, I2N2], [], [I5N0], [I7N0, I7N1, I7N1, I7N1], [I11N0, I11N1, I11N2], [], [I17N1], [], [], [], [], [I37N1, I37N2, I37N3], [I41N1], [I43N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB122I1_primes (p : ℕ) :
  p ∈ Set.range ![53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 47 < p ∧ p ≤ 121 := by
  rw [← List.mem_ofFn']
  convert primes_range 47 121 (by omega)

def PB122I1 : PrimesBelowBoundCertificateInterval O 47 121 122 where
  m := 15
  g := ![2, 3, 3, 3, 2, 1, 2, 2, 4, 3, 3, 4, 1, 2, 3]
  P := ![53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB122I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2, I89N3]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7890481, 53]
    · exact ![205379, 59, 59]
    · exact ![226981, 61, 61]
    · exact ![4489, 4489, 67]
    · exact ![25411681, 71]
    · exact ![2073071593]
    · exact ![38950081, 79]
    · exact ![47458321, 83]
    · exact ![7921, 89, 89, 89]
    · exact ![9409, 9409, 97]
    · exact ![1030301, 101, 101]
    · exact ![10609, 103, 103, 103]
    · exact ![14025517307]
    · exact ![1295029, 11881]
    · exact ![1442897, 113, 113]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
      exact NI89N3
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
  Il := ![[I53N1], [I59N1, I59N2], [I61N1, I61N2], [I67N2], [I71N1], [], [I79N1], [I83N1], [I89N1, I89N2, I89N3], [I97N2], [I101N1, I101N2], [I103N1, I103N1, I103N2], [], [], [I113N1, I113N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

def PB122 : PrimesBelowBoundCertificate O 122 := by
  refine primesBelowBoundCertificate_of_Interval O ![1, 47, 121] 121 rfl rfl ?_ ?_
  · decide
  · rintro ⟨i,hi⟩
    interval_cases i 
    exact PB122I0
    exact PB122I1
