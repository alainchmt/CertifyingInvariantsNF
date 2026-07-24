
import IdealArithmetic.Examples.NF5_3_125000000_1.RI5_3_125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 2, 1, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 2, 1, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 2, 1, 0, 0], ![0, 3, 4, 2, 0], ![0, 2, 3, 4, 2], ![20, 12, 0, 1, 4], ![40, 34, 12, -2, 1]]]
  hmulB := by decide  
  f := ![![![121, 8, -11, 8, -10]], ![![-100, -5, 8, -6, 8]], ![![80, 2, -5, 4, -6]], ![![-10, 4, -2, 1, 0]], ![![0, -6, 4, -2, 1]]]
  g := ![![![1, 2, 1, 0, 0], ![0, 3, 4, 2, 0], ![0, 2, 3, 4, 2], ![10, 12, 0, 1, 4], ![20, 34, 12, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -1, 0, -1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-3, -1, 0, -1, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-3, -1, 0, -1, 1], ![20, 9, -2, -1, -2], ![-20, -3, 9, -1, -1], ![-20, -16, -2, 10, 0], ![0, -11, -16, -2, 10]]]
  hmulB := by decide  
  f := ![![![-34, -22, -10, -7, -2]], ![![-20, -34, -22, -9, -7]], ![![-87, -74, -39, -22, -10]], ![![-80, -89, -52, -25, -15]], ![![-167, -167, -94, -48, -26]]]
  g := ![![![-2, -1, 0, -1, 1], ![12, 9, -2, -1, -2], ![-14, -3, 9, -1, -1], ![-9, -16, -2, 10, 0], ![3, -11, -16, -2, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 10, -5, 6, -5]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![67, 10, -5, 6, -5]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![67, 10, -5, 6, -5], ![-100, 2, 20, -5, 12], ![120, 32, 2, 14, -5], ![0, 30, 22, 7, 8], ![80, 59, 30, 18, 7]]]
  hmulB := by decide  
  f := ![![![-14, -7, 2, 3, 0]], ![![0, -6, -7, 2, 3]], ![![23, 11, -5, -7, 2]], ![![20, 27, 18, -8, -10]], ![![-100, -41, 27, 23, -8]]]
  g := ![![![36, 10, -5, 6, -5], ![-60, 2, 20, -5, 12], ![59, 32, 2, 14, -5], ![-11, 30, 22, 7, 8], ![25, 59, 30, 18, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 2, 1, 0, 0]] ![![-3, -1, 0, -1, 1]]
  ![![14, 13, 5, -5, -3]] where
 M := ![![![14, 13, 5, -5, -3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![14, 13, 5, -5, -3]] ![![-3, -1, 0, -1, 1]]
  ![![218, 201, 77, -76, -47]] where
 M := ![![![218, 201, 77, -76, -47]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![218, 201, 77, -76, -47]] ![![67, 10, -5, 6, -5]]
  ![![-14, -7, 2, 3, 0]] where
 M := ![![![-14, -7, 2, 3, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-14, -7, 2, 3, 0]] ![![67, 10, -5, 6, -5]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![2, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 5 2 1 [2, 0, 0, 0, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 0, 1], [1, 2, 1, 2], [2, 2, 2, 0, 1], [2, 1, 0, 0, 2], [0, 1]]
 g := ![![[]], ![[1, 2, 1, 2, 1]], ![[1, 2, 2, 1, 2]], ![[0, 1, 0, 1, 2, 1, 2, 1]], ![[1, 1, 0, 2, 1, 2, 1, 2]]]
 h' := ![![[0, 0, 0, 1], [0, 1]], ![[1, 2, 1, 2], [0, 0, 0, 1]], ![[2, 2, 2, 0, 1], [1, 2, 1, 2]], ![[2, 1, 0, 0, 2], [2, 2, 2, 0, 1]], ![[0, 1], [2, 1, 0, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 1, 1], [], [], []]
 b := ![[], [2, 2, 2, 1, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 5
  hpos := by decide
  P := [2, 0, 0, 0, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2491536258, -2765778645, -1662835446, -696710565, -342176172]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-830512086, -921926215, -554278482, -232236855, -114058724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 243 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -16, -16, 4, 8]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-5, -16, -16, 4, 8]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-5, -16, -16, 4, 8], ![160, 75, -32, -40, 8], ![80, 112, 75, -36, -40], ![-480, -200, 128, 115, -40], ![-400, -416, -200, 148, 115]]]
  hmulB := by decide  
  f := ![![![5375, 1520, -1264, 780, -648]], ![![-2592, -733, 608, -376, 312]], ![![3120, 880, -733, 452, -376]], ![![-2464, -696, 576, -357, 296]], ![![2960, 832, -696, 428, -357]]]
  g := ![![![-1, -16, -16, 4, 8], ![32, 75, -32, -40, 8], ![16, 112, 75, -36, -40], ![-96, -200, 128, 115, -40], ![-80, -416, -200, 148, 115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-5, -16, -16, 4, 8]] ![![-5, -16, -16, 4, 8]]
  ![![-8935, -7040, -1696, 2840, 1232]] where
 M := ![![![-8935, -7040, -1696, 2840, 1232]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-8935, -7040, -1696, 2840, 1232]] ![![-5, -16, -16, 4, 8]]
  ![![-3073405, -1655504, 358160, 815852, -31880]] where
 M := ![![![-3073405, -1655504, 358160, 815852, -31880]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-3073405, -1655504, 358160, 815852, -31880]] ![![-5, -16, -16, 4, 8]]
  ![![-599717775, -184782720, 239817664, 130137520, -88457952]] where
 M := ![![![-599717775, -184782720, 239817664, 130137520, -88457952]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-599717775, -184782720, 239817664, 130137520, -88457952]] ![![-5, -16, -16, 4, 8]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-34464062005, 33367362800, 67844049200, -1766960300, -31246875800]]]
 hmul := by decide  
 g := ![![![![-6892812401, 6673472560, 13568809840, -353392060, -6249375160]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-403, -41, 46, -32, 36]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-403, -41, 46, -32, 36]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![3, 2, 2, 1, 0], ![1, 2, 5, 0, 1]] where
  M :=![![![-403, -41, 46, -32, 36], ![720, 75, -82, 56, -64], ![-640, -65, 75, -50, 56], ![200, 16, -24, 19, -18], ![-180, -20, 16, -15, 19]]]
  hmulB := by decide  
  f := ![![![-29, -7, 8, -4, 4]], ![![80, 27, -14, 12, -8]], ![![-80, -15, 27, -10, 12]], ![![-1, 5, 6, 1, 2]], ![![-47, -4, 21, -5, 9]]]
  g := ![![![-49, -7, -10, -32, 36], ![88, 13, 18, 56, -64], ![-78, -11, -15, -50, 56], ![23, 2, 4, 19, -18], ![-22, -4, -7, -15, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [5, 5, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 5, 1], [6, 1, 6], [0, 1]]
 g := ![![[4], [1]], ![[2, 6, 4, 4], [5, 3, 1, 1]], ![[0, 4, 5, 3], [4, 6, 3, 6]]]
 h' := ![![[1, 5, 1], [2, 2], [0, 1]], ![[6, 1, 6], [4, 3, 2], [1, 5, 1]], ![[0, 1], [0, 2, 5], [6, 1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 6], []]
 b := ![[], [3, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [5, 5, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-72552433, -44929474, -4112220, -10020980, -4577766]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5415961, -2247426, 5545510, -10020980, -4577766]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, 17, -16, 9, -8]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![63, 17, -16, 9, -8]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![63, 17, -16, 9, -8], ![-160, -49, 34, -24, 18], ![180, 45, -49, 25, -24], ![-160, -54, 28, -25, 16], ![160, 30, -54, 20, -25]]]
  hmulB := by decide  
  f := ![![![-31, -11, 2, 3, 2]], ![![-12, -7, -2, 2, 2]], ![![-18, -3, 1, -1, 2]], ![![0, 6, 8, -1, -4]], ![![-40, -20, 6, 10, -1]]]
  g := ![![![13, 17, -16, 9, -8], ![-24, -49, 34, -24, 18], ![42, 45, -49, 25, -24], ![-16, -54, 28, -25, 16], ![52, 30, -54, 20, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -2, 0, 1, 0]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-3, -2, 0, 1, 0]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-3, -2, 0, 1, 0], ![0, -3, -4, 0, 2], ![20, 10, -3, -5, 0], ![0, 10, 12, -3, -6], ![-60, -30, 10, 15, -3]]]
  hmulB := by decide  
  f := ![![![331, 36, -40, 27, -30]], ![![198, 21, -24, 16, -18]], ![![219, 24, -27, 18, -20]], ![![66, 6, -8, 5, -6]], ![![73, 8, -10, 6, -7]]]
  g := ![![![1, -2, 0, 1, 0], ![4, -3, -4, 0, 2], ![-3, 10, -3, -5, 0], ![-12, 10, 12, -3, -6], ![9, -30, 10, 15, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-403, -41, 46, -32, 36]] ![![63, 17, -16, 9, -8]]
  ![![331, 36, -40, 27, -30]] where
 M := ![![![331, 36, -40, 27, -30]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![331, 36, -40, 27, -30]] ![![-3, -2, 0, 1, 0]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 7, -4, 3, -2]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![21, 7, -4, 3, -2]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![4, 1, 8, 1, 0], ![1, 9, 3, 0, 1]] where
  M :=![![![21, 7, -4, 3, -2], ![-40, -7, 14, -6, 6], ![60, 23, -7, 11, -6], ![-40, -6, 16, -1, 8], ![80, 36, -6, 12, -1]]]
  hmulB := by decide  
  f := ![![![-89, -9, 10, -7, 8]], ![![160, 17, -18, 12, -14]], ![![-140, -13, 17, -11, 12]], ![![-116, -11, 14, -9, 10]], ![![81, 9, -9, 6, -7]]]
  g := ![![![1, 2, -2, 3, -2], ![-2, -5, 4, -6, 6], ![2, 6, -7, 11, -6], ![-4, -7, 0, -1, 8], ![3, 3, -9, 12, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [1, 9, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10, 1], [2, 0, 10], [0, 1]]
 g := ![![[1, 1, 5], [3, 1, 1], []], ![[9, 7, 9, 3], [7, 1], [10, 1]], ![[7, 9, 2, 7], [10, 6, 1, 10], [1, 1]]]
 h' := ![![[10, 10, 1], [8, 5, 4], [0, 0, 1], [0, 1]], ![[2, 0, 10], [0, 2, 5], [2, 10], [10, 10, 1]], ![[0, 1], [8, 4, 2], [3, 1, 10], [2, 0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 3], []]
 b := ![[], [9, 9, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [1, 9, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65519, -68976, -37796, -12391, -5384]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-961, -739, 7044, -12391, -5384]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 9, -10, 7, -8]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![89, 9, -10, 7, -8]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![6, 3, 1, 0, 0], ![4, 0, 0, 1, 0], ![0, 2, 0, 0, 1]] where
  M :=![![![89, 9, -10, 7, -8], ![-160, -17, 18, -12, 14], ![140, 13, -17, 11, -12], ![-40, -2, 4, -5, 4], ![40, 6, -2, 2, -5]]]
  hmulB := by decide  
  f := ![![![-21, -7, 4, -3, 2]], ![![40, 7, -14, 6, -6]], ![![-6, -4, -1, -1, 0]], ![![-4, -2, 0, -1, 0]], ![![0, -2, -2, 0, -1]]]
  g := ![![![11, 5, -10, 7, -8], ![-20, -9, 18, -12, 14], ![18, 8, -17, 11, -12], ![-4, -2, 4, -5, 4], ![4, 2, -2, 2, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10], [0, 1]]
 g := ![![[4, 4], [5, 4], [1]], ![[7, 7], [8, 7], [1]]]
 h' := ![![[9, 10], [3, 2], [5, 9], [0, 1]], ![[0, 1], [10, 9], [9, 2], [9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [10, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [6, 2, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3009, 6649, 6906, 3552, 1287]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4785, -1513, 6906, 3552, 1287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![21, 7, -4, 3, -2]] ![![89, 9, -10, 7, -8]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 1, 0, 4, -2]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![17, 1, 0, 4, -2]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![3, 2, 3, 1, 0], ![4, 10, 6, 0, 1]] where
  M :=![![![17, 1, 0, 4, -2], ![-40, -7, 2, 2, 8], ![80, 29, -7, -2, 2], ![40, 52, 28, -9, -6], ![-60, -2, 52, 31, -9]]]
  hmulB := by decide  
  f := ![![![-2211, -623, 518, -320, 266]], ![![5320, 1499, -1246, 770, -640]], ![![-6400, -1803, 1499, -926, 770]], ![![-781, -220, 183, -113, 94]], ![![-8, -2, 2, -1, 1]]]
  g := ![![![1, 1, 0, 4, -2], ![-6, -7, -4, 2, 8], ![6, 1, -1, -2, 2], ![7, 10, 7, -9, -6], ![-9, 2, 1, 31, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [9, 10, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 11, 4], [11, 1, 9], [0, 1]]
 g := ![![[9], [1, 12], [1]], ![[3, 10, 0, 4], [3, 10], [3, 5, 0, 12]], ![[0, 10, 10, 9], [9, 4], [1, 5, 4, 1]]]
 h' := ![![[10, 11, 4], [7, 10], [4, 3, 8], [0, 1]], ![[11, 1, 9], [3, 6, 1], [11, 1, 7], [10, 11, 4]], ![[0, 1], [0, 10, 12], [9, 9, 11], [11, 1, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 12], []]
 b := ![[], [7, 2, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [9, 10, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-72937, -2119, 64206, -30123, -112356]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![35912, 90899, 63747, -30123, -112356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2211, -623, 518, -320, 266]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-2211, -623, 518, -320, 266]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![2, 10, 1, 0, 0], ![6, 12, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-2211, -623, 518, -320, 266], ![5320, 1499, -1246, 770, -640], ![-6400, -1803, 1499, -926, 770], ![5040, 1420, -1180, 729, -606], ![-6060, -1706, 1420, -877, 729]]]
  hmulB := by decide  
  f := ![![![17, 1, 0, 4, -2]], ![![-40, -7, 2, 2, 8]], ![![-22, -3, 1, 2, 6]], ![![-26, -2, 4, 3, 6]], ![![-2, 0, 4, 3, -1]]]
  g := ![![![-143, -151, 518, -320, 266], ![344, 363, -1246, 770, -640], ![-414, -437, 1499, -926, 770], ![326, 344, -1180, 729, -606], ![-392, -414, 1420, -877, 729]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 12], [0, 1]]
 g := ![![[6, 12], [1], [1, 1]], ![[5, 1], [1], [2, 12]]]
 h' := ![![[1, 12], [2, 5], [11, 12], [0, 1]], ![[0, 1], [7, 8], [10, 1], [1, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [11, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [2, 12, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-798, 2180, 3024, -2880, 524]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![722, 500, 3024, -2880, 524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![17, 1, 0, 4, -2]] ![![-2211, -623, 518, -320, 266]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![791, 81, -90, 63, -70]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![791, 81, -90, 63, -70]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![4, 2, 11, 11, 1]] where
  M :=![![![791, 81, -90, 63, -70], ![-1400, -139, 162, -110, 126], ![1260, 137, -139, 99, -110], ![-400, -30, 56, -29, 36], ![360, 44, -30, 38, -29]]]
  hmulB := by decide  
  f := ![![![-33, -9, 8, -5, 4]], ![![80, 23, -18, 12, -10]], ![![-100, -29, 23, -13, 12]], ![![80, 22, -20, 11, -8]], ![![-16, -5, 3, -2, 3]]]
  g := ![![![63, 13, 40, 49, -70], ![-112, -23, -72, -88, 126], ![100, 21, 63, 77, -110], ![-32, -6, -20, -25, 36], ![28, 6, 17, 21, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [12, 3, 6, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 6, 0, 4], [12, 5, 1, 16], [5, 5, 16, 14], [0, 1]]
 g := ![![[16, 7, 13, 9], [3, 3, 8], [1], []], ![[14, 6, 12, 10, 16, 9], [13, 4, 8], [5, 15, 13], [12, 5, 16]], ![[0, 7, 2, 0, 13, 8], [0, 3, 9], [0, 11, 15], [3, 10, 1]], ![[0, 7, 9, 12, 7, 6], [11, 13, 15], [9, 5, 4], [10, 12, 9]]]
 h' := ![![[12, 6, 0, 4], [6, 10, 13, 14], [5, 14, 11, 12], [0, 0, 1], [0, 1]], ![[12, 5, 1, 16], [10, 6, 15, 10], [8, 9, 16, 12], [0, 14, 12, 9], [12, 6, 0, 4]], ![[5, 5, 16, 14], [4, 7, 4, 3], [2, 15, 8, 3], [6, 8, 6, 10], [12, 5, 1, 16]], ![[0, 1], [0, 11, 2, 7], [9, 13, 16, 7], [7, 12, 15, 15], [5, 5, 16, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 7, 3], []]
 b := ![[], [], [2, 13, 8, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [12, 3, 6, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2188929, 815732, 3346387, 5443711, 2529517]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-723941, -249606, -1439900, -1316528, 2529517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 9, -8, 5, -4]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![33, 9, -8, 5, -4]] 
 ![![17, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![33, 9, -8, 5, -4], ![-80, -23, 18, -12, 10], ![100, 29, -23, 13, -12], ![-80, -22, 20, -11, 8], ![80, 18, -22, 16, -11]]]
  hmulB := by decide  
  f := ![![![-791, -81, 90, -63, 70]], ![![-476, -49, 54, -38, 42]], ![![-679, -70, 77, -54, 60]], ![![-23, -3, 2, -2, 2]], ![![-533, -55, 60, -43, 47]]]
  g := ![![![4, 9, -8, 5, -4], ![-8, -23, 18, -12, 10], ![10, 29, -23, 13, -12], ![-9, -22, 20, -11, 8], ![15, 18, -22, 16, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![791, 81, -90, 63, -70]] ![![33, 9, -8, 5, -4]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 20, -10, -8, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![61, 20, -10, -8, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![9, 7, 6, 1, 0], ![3, 13, 9, 0, 1]] where
  M :=![![![61, 20, -10, -8, 0], ![0, 51, 40, -20, -16], ![-160, -76, 51, 48, -20], ![-200, -200, -96, 71, 56], ![560, 188, -200, -124, 71]]]
  hmulB := by decide  
  f := ![![![-241, -252, -142, -72, -40]], ![![-800, -863, -504, -244, -144]], ![![-1440, -1516, -863, -432, -244]], ![![-971, -1031, -592, -293, -168]], ![![-1457, -1549, -891, -440, -253]]]
  g := ![![![7, 4, 2, -8, 0], ![12, 21, 16, -20, -16], ![-28, -8, -3, 48, -20], ![-53, -75, -54, 71, 56], ![77, 7, -5, -124, 71]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [9, 18, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 6, 8], [3, 12, 11], [0, 1]]
 g := ![![[1, 14, 6], [12, 5, 1], [13, 1], []], ![[0, 7, 17, 10], [4, 0, 10, 8], [14, 11], [16, 7]], ![[13, 2, 7, 17], [1, 7], [10, 17], [13, 7]]]
 h' := ![![[10, 6, 8], [6, 14, 14], [16, 4, 18], [0, 0, 1], [0, 1]], ![[3, 12, 11], [5, 4, 14], [5, 8, 1], [13, 16, 12], [10, 6, 8]], ![[0, 1], [18, 1, 10], [3, 7], [6, 3, 6], [3, 12, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 5], []]
 b := ![[], [13, 11, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [9, 18, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7164, 6014, 7284, -15015, 4847]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5970, 2532, 2829, -15015, 4847]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 252, 142, 72, 40]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![241, 252, 142, 72, 40]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![2, 13, 1, 0, 0], ![12, 13, 0, 1, 0], ![12, 8, 0, 0, 1]] where
  M :=![![![241, 252, 142, 72, 40], ![800, 863, 504, 244, 144], ![1440, 1516, 863, 432, 244], ![2040, 2184, 1264, 619, 360], ![3600, 3812, 2184, 1084, 619]]]
  hmulB := by decide  
  f := ![![![-61, -20, 10, 8, 0]], ![![0, -51, -40, 20, 16]], ![![2, -33, -29, 12, 12]], ![![-28, -37, -16, 15, 8]], ![![-68, -44, 0, 20, 3]]]
  g := ![![![-73, -150, 142, 72, 40], ![-256, -527, 504, 244, 144], ![-442, -909, 863, 432, 244], ![-644, -1325, 1264, 619, 360], ![-1116, -2296, 2184, 1084, 619]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [8, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 18], [0, 1]]
 g := ![![[18, 5], [2, 16], [7], [1]], ![[1, 14], [16, 3], [7], [1]]]
 h' := ![![[8, 18], [3, 9], [8, 4], [11, 8], [0, 1]], ![[0, 1], [18, 10], [2, 15], [18, 11], [8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [5, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [8, 11, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1070, -93, 730, -1046, 756]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![50, -107, 730, -1046, 756]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![61, 20, -10, -8, 0]] ![![241, 252, 142, 72, 40]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [19, 10, 10, 12, 21, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 9, 15, 7, 4], [10, 4, 3, 4, 10], [4, 1, 12, 19, 8], [14, 8, 16, 16, 1], [0, 1]]
 g := ![![[5, 19, 10, 12, 8], [3, 17, 22, 6, 4], [1], []], ![[9, 6, 4, 21, 9, 12, 9, 13], [7, 0, 13, 11, 19, 19, 3, 6], [7, 5, 7, 21, 2, 0, 0, 9], [16, 15, 19, 16]], ![[10, 9, 3, 13, 11, 16, 14, 17], [9, 10, 13, 22, 15, 1, 21, 20], [14, 14, 20, 5, 8, 8, 8, 19], [21, 11, 4, 8]], ![[9, 13, 3, 5, 13, 3, 20, 16], [20, 6, 8, 7, 15, 10, 4, 6], [2, 0, 11, 2, 12, 2, 20, 9], [17, 5, 18, 18]], ![[3, 5, 6, 20, 21, 0, 19, 13], [18, 3, 15, 11, 13, 13, 4, 2], [0, 11, 14, 13, 8, 17, 5, 16], [16, 22, 11, 1]]]
 h' := ![![[20, 9, 15, 7, 4], [12, 8, 15, 9, 10], [4, 13, 13, 11, 2], [0, 0, 1], [0, 1]], ![[10, 4, 3, 4, 10], [1, 9, 16, 12, 3], [3, 18, 12, 19, 6], [4, 7, 10, 13, 13], [20, 9, 15, 7, 4]], ![[4, 1, 12, 19, 8], [1, 18, 0, 17, 21], [10, 8, 22, 11, 5], [0, 6, 2, 10, 8], [10, 4, 3, 4, 10]], ![[14, 8, 16, 16, 1], [12, 10, 16, 15, 18], [11, 1, 21, 11, 15], [15, 19, 18, 21, 21], [4, 1, 12, 19, 8]], ![[0, 1], [20, 1, 22, 16, 17], [19, 6, 1, 17, 18], [7, 14, 15, 2, 4], [14, 8, 16, 16, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 17, 8], [], [], []]
 b := ![[], [9, 1, 9, 21], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [19, 10, 10, 12, 21, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-103880167, -11484567, 90416634, 225232951, 123930486]
  a := ![1, 0, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4516529, -499329, 3931158, 9792737, 5388282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB547I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB547I0 : PrimesBelowBoundCertificateInterval O 1 23 547 where
  m := 9
  g := ![5, 1, 5, 3, 2, 2, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB547I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![243]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 7, 7]
    · exact ![1331, 121]
    · exact ![2197, 169]
    · exact ![83521, 17]
    · exact ![6859, 361]
    · exact ![6436343]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
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
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I7N0, I7N1, I7N2, I11N1, I13N1, I17N1, I19N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N1], [I13N1], [I17N1], [I19N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
