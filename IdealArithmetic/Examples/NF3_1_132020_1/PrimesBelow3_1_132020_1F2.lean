
import IdealArithmetic.Examples.NF3_1_132020_1.RI3_1_132020_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [29, 18, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 19, 5], [71, 63, 78], [0, 1]]
 g := ![![[34, 34, 17], [75, 44, 78], [40, 31], [77, 63], [69, 81, 1], []], ![[42, 57, 62, 34], [82, 31, 38, 54], [30, 3], [51, 68], [23, 64, 82, 8], [57, 25]], ![[39, 33, 66, 4], [55, 18, 79, 30], [8, 51], [33, 37], [9, 15, 6, 21], [67, 25]]]
 h' := ![![[10, 19, 5], [66, 63, 73], [38, 18, 24], [6, 5, 60], [74, 61, 35], [0, 0, 1], [0, 1]], ![[71, 63, 78], [41, 50, 17], [47, 57, 25], [2, 5, 70], [30, 69, 20], [24, 40, 63], [10, 19, 5]], ![[0, 1], [36, 53, 76], [55, 8, 34], [72, 73, 36], [38, 36, 28], [27, 43, 19], [71, 63, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 23], []]
 b := ![[], [30, 63, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [29, 18, 2, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4731, 332, 332]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57, 4, 4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7920224218387205427, 2076908978513713485, -431478786975456577]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-7920224218387205427, 2076908978513713485, -431478786975456577]] 
 ![![89, 0, 0], ![0, 89, 0], ![86, 52, 1]] where
  M :=![![![-7920224218387205427, 2076908978513713485, -431478786975456577], ![30203515088281960390, -7920224218387205427, 1645430191538256908], ![-115180113407677983560, 30203515088281960390, -6274794026848948519]]]
  hmulB := by decide  
  f := ![![![-2203376837, -689911165, -29401809]], ![![2058126630, -2203376837, -719312974]], ![![-360852978, -1930896956, -481522697]]]
  g := ![![![327943274848337755, 275436021362218601, -431478786975456577], ![-1250600914427057682, -1050366226723332187, 1645430191538256908], ![4769125538217208866, 4005537129038508802, -6274794026848948519]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [67, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 88], [0, 1]]
 g := ![![[2, 4], [4], [4], [4, 8], [78, 67], [1]], ![[0, 85], [4], [4], [0, 81], [0, 22], [1]]]
 h' := ![![[44, 88], [88, 87], [0, 2], [88, 87], [25, 50], [22, 44], [0, 1]], ![[0, 1], [0, 2], [88, 87], [0, 2], [0, 39], [0, 45], [44, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [60, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [67, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![233, -716, 130]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-123, -84, 130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2203376837, -689911165, -29401809]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-2203376837, -689911165, -29401809]] 
 ![![89, 0, 0], ![36, 1, 0], ![39, 0, 1]] where
  M :=![![![-2203376837, -689911165, -29401809], ![2058126630, -2203376837, -719312974], ![50351908180, 2058126630, -2922689811]]]
  hmulB := by decide  
  f := ![![![-7920224218387205427, 2076908978513713485, -431478786975456577]], ![![-2864320862625364438, 751106730428162697, -156042765613237976]], ![![-4764818628368303317, 1249471519666480745, -259578277740356798]]]
  g := ![![![267192086, -689911165, -29401809], ![1229583132, -2203376837, -719312974], ![1013980361, 2058126630, -2922689811]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-7920224218387205427, 2076908978513713485, -431478786975456577]] ![![-2203376837, -689911165, -29401809]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24799, 6503, -1351]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-24799, 6503, -1351]] 
 ![![97, 0, 0], ![43, 1, 0], ![91, 0, 1]] where
  M :=![![![-24799, 6503, -1351], ![94570, -24799, 5152], ![-360640, 94570, -19647]]]
  hmulB := by decide  
  f := ![![![-1313, -371, -7]], ![![-577, -178, -7]], ![![-959, -343, -24]]]
  g := ![![![-1871, 6503, -1351], ![7135, -24799, 5152], ![-27209, 94570, -19647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45378673, -11899584, 2472144]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![45378673, -11899584, 2472144]] 
 ![![97, 0, 0], ![63, 1, 0], ![8, 0, 1]] where
  M :=![![![45378673, -11899584, 2472144], ![-173050080, 45378673, -9427440], ![659920800, -173050080, 35951233]]]
  hmulB := by decide  
  f := ![![![58609, 15552, 48]], ![![38031, 10705, 192]], ![![-6424, 1248, 769]]]
  g := ![![![7992529, -11899584, 2472144], ![-30479247, 45378673, -9427440], ![116231608, -173050080, 35951233]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-701681, -434435, -65671]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-701681, -434435, -65671]] 
 ![![97, 0, 0], ![87, 1, 0], ![94, 0, 1]] where
  M :=![![![-701681, -434435, -65671], ![4596970, -701681, -500106], ![35007420, 4596970, -1201787]]]
  hmulB := by decide  
  f := ![![![-3142243382767, 823985952215, -171183457159]], ![![-2694766312367, 706644685154, -146805755441]], ![![-3516155181794, 922036304220, -191553462481]]]
  g := ![![![446054, -434435, -65671], ![1161373, -701681, -500106], ![-2597536, 4596970, -1201787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-24799, 6503, -1351]] ![![45378673, -11899584, 2472144]]
  ![![-3142243382767, 823985952215, -171183457159]] where
 M := ![![![-3142243382767, 823985952215, -171183457159]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-3142243382767, 823985952215, -171183457159]] ![![-701681, -434435, -65671]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [65, 98, 91, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 9, 28], [16, 91, 73], [0, 1]]
 g := ![![[84, 83, 23], [63, 81], [88, 98, 19], [90, 95], [50, 100], [1]], ![[34, 3, 64, 29], [43, 85], [35, 50, 76, 40], [1, 100], [9, 54], [81, 18, 5, 35]], ![[87, 34, 89, 94], [36, 52], [75, 3, 57, 83], [73, 71], [87, 36], [96, 2, 67, 66]]]
 h' := ![![[95, 9, 28], [1, 15, 86], [37, 92, 92], [21, 83, 25], [66, 27, 14], [36, 3, 10], [0, 1]], ![[16, 91, 73], [29, 7, 65], [81, 24, 40], [67, 85, 54], [43, 46, 10], [74, 45, 85], [95, 9, 28]], ![[0, 1], [48, 79, 51], [60, 86, 70], [21, 34, 22], [25, 28, 77], [78, 53, 6], [16, 91, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 57], []]
 b := ![[], [46, 36, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [65, 98, 91, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![92415, 7878, -808]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![915, 78, -8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀



lemma PB103I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 102 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 102 (by omega)

def PB103I2 : PrimesBelowBoundCertificateInterval O 79 102 103 where
  m := 4
  g := ![1, 2, 3, 1]
  P := ![83, 89, 97, 101]
  hP := PB103I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![1030301]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
  β := ![I89N1, I97N0, I97N1, I97N2]
  Il := ![[], [I89N1], [I97N0, I97N1, I97N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
