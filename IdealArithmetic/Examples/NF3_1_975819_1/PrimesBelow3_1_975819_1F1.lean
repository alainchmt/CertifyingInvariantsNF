
import IdealArithmetic.Examples.NF3_1_975819_1.RI3_1_975819_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-43, -13, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-43, -13, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![31, 24, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-43, -13, 1], ![-270, -30, -66], ![4010, -574, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -24, 37]], ![![-2, -1, 1], ![48, 42, -66], ![100, -22, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [27, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 36], [0, 1]]
 g := ![![[5, 11], [11], [15, 3], [21], [1]], ![[0, 26], [11], [17, 34], [21], [1]]]
 h' := ![![[13, 36], [3, 14], [2, 14], [14, 15], [10, 13], [0, 1]], ![[0, 1], [0, 23], [36, 23], [24, 22], [31, 24], [13, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [36, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [27, 24, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4769, -571, 875]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-862, -583, 875]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-8, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-8, 1, 0]] 
 ![![37, 0, 0], ![29, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-8, 1, 0], ![-2, -6, 5], ![-296, 39, -9]]]
  hmulB := by decide  
  f := ![![![545, 1657, -1380], ![-37, 10212, 0]], ![![425, 1297, -1080], ![-36, 7992, 0]], ![![399, 1209, -1007], ![-21, 7452, 0]]]
  g := ![![![1, 0, 0], ![-29, 37, 0], ![-27, 0, 37]], ![![-1, 1, 0], ![1, -6, 5], ![-32, 39, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-43, -13, 1]] ![![37, 0, 0], ![-8, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-296, 37, 0]], ![![-1591, -481, 37], ![74, 74, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-8, 1, 0]]], ![![![-43, -13, 1]], ![![2, 2, -2]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-17, -15, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-17, -15, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![24, 26, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-17, -15, 1], ![-266, -8, -76], ![4602, -652, 38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -26, 41]], ![![-1, -1, 1], ![38, 48, -76], ![90, -40, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [6, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 40], [0, 1]]
 g := ![![[17, 31], [25], [21], [30, 31], [1]], ![[12, 10], [25], [21], [25, 10], [1]]]
 h' := ![![[21, 40], [22, 21], [7, 5], [25, 29], [35, 21], [0, 1]], ![[0, 1], [12, 20], [30, 36], [19, 12], [25, 20], [21, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [3, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [6, 20, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9043, -7748, 5852]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3205, -3900, 5852]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-6, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-6, 1, 0]] 
 ![![41, 0, 0], ![35, 1, 0], ![3, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-6, 1, 0], ![-2, -4, 5], ![-296, 39, -7]]]
  hmulB := by decide  
  f := ![![![1077, 2178, -2720], ![-82, 22304, 0]], ![![917, 1858, -2320], ![-81, 19024, 0]], ![![81, 159, -199], ![9, 1632, 0]]]
  g := ![![![1, 0, 0], ![-35, 41, 0], ![-3, 0, 41]], ![![-1, 1, 0], ![3, -4, 5], ![-40, 39, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-17, -15, 1]] ![![41, 0, 0], ![-6, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-246, 41, 0]], ![![-697, -615, 41], ![-164, 82, -82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-6, 1, 0]]], ![![![-17, -15, 1]], ![![-4, 2, -2]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [9, 2, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 17, 29], [33, 25, 14], [0, 1]]
 g := ![![[10, 29, 16], [11, 38, 38], [38, 15], [22, 29, 1], []], ![[27, 23, 40, 5], [34, 10, 19, 26], [26, 15], [10, 12, 41, 22], [5, 24]], ![[8, 25, 26, 15], [12, 26, 34, 10], [42, 17], [3, 28, 42, 4], [20, 24]]]
 h' := ![![[39, 17, 29], [30, 37, 4], [33, 40, 34], [17, 39, 12], [0, 0, 1], [0, 1]], ![[33, 25, 14], [24, 41, 12], [5, 25, 32], [29, 17, 12], [14, 25, 25], [39, 17, 29]], ![[0, 1], [28, 8, 27], [9, 21, 20], [0, 30, 19], [6, 18, 17], [33, 25, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 3], []]
 b := ![[], [8, 37, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [9, 2, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26173259479, 18595427013, -9956565591]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-608680453, 432451791, -231548037]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [16, 9, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 16, 36], [0, 30, 11], [0, 1]]
 g := ![![[35, 10, 2], [1, 39, 28], [7, 34, 12], [7, 4, 1], []], ![[27, 30, 4, 25], [44, 42, 17, 34], [1, 29, 6, 24], [40, 10, 15, 17], [38, 27]], ![[0, 20, 46, 41], [30, 10, 45, 45], [27, 27, 18, 40], [46, 40, 9, 43], [16, 27]]]
 h' := ![![[4, 16, 36], [31, 20, 40], [29, 46, 13], [29, 14, 23], [0, 0, 1], [0, 1]], ![[0, 30, 11], [25, 1, 40], [37, 46, 25], [5, 30, 19], [19, 12, 30], [4, 16, 36]], ![[0, 1], [37, 26, 14], [38, 2, 9], [16, 3, 5], [26, 35, 16], [0, 30, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 17], []]
 b := ![[], [7, 41, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [16, 9, 43, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30209579, 6768987, -2411805]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-642757, 144021, -51315]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331687, -57806, 18768]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![331687, -57806, 18768]] 
 ![![53, 0, 0], ![10, 1, 0], ![18, 0, 1]] where
  M :=![![![331687, -57806, 18768], ![-5439716, 948027, -307798], ![20150992, -3511890, 1140213]]]
  hmulB := by decide  
  f := ![![![-8469, 1158, 452]], ![![-4166, 435, 186]], ![![-7962, 674, 313]]]
  g := ![![![10791, -57806, 18768], ![-176974, 948027, -307798], ![655586, -3511890, 1140213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![14, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![14, 1, 0]] 
 ![![53, 0, 0], ![14, 1, 0], ![29, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![14, 1, 0], ![-2, 16, 5], ![-296, 39, 13]]]
  hmulB := by decide  
  f := ![![![1921, -15812, -4940], ![212, 52364, 0]], ![![492, -4162, -1300], ![107, 13780, 0]], ![![1049, -8652, -2703], ![124, 28652, 0]]]
  g := ![![![1, 0, 0], ![-14, 53, 0], ![-29, 0, 53]], ![![0, 1, 0], ![-7, 16, 5], ![-23, 39, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-25, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-25, 1, 0]] 
 ![![53, 0, 0], ![28, 1, 0], ![33, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-25, 1, 0], ![-2, -23, 5], ![-296, 39, -26]]]
  hmulB := by decide  
  f := ![![![-835, -10768, 2340], ![212, -24804, 0]], ![![-443, -5683, 1235], ![107, -13091, 0]], ![![-510, -6705, 1457], ![153, -15444, 0]]]
  g := ![![![1, 0, 0], ![-28, 53, 0], ![-33, 0, 53]], ![![-1, 1, 0], ![9, -23, 5], ![-10, 39, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![331687, -57806, 18768]] ![![53, 0, 0], ![14, 1, 0]]
  ![![53, 0, 0], ![-36, -16, 1]] where
 M := ![![![17579411, -3063718, 994704], ![-796098, 138743, -45046]]]
 hmul := by decide  
 g := ![![![![240931, -98142, 21289], ![-133613, 0, 0]], ![![-10878, 4459, -965], ![6099, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-36, -16, 1]] ![![53, 0, 0], ![-25, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1325, 53, 0]], ![![-1908, -848, 53], ![636, 371, -106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-25, 1, 0]]], ![![![-36, -16, 1]], ![![12, 7, -2]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [43, 28, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 22, 11], [26, 36, 48], [0, 1]]
 g := ![![[55, 31, 15], [22, 8, 26], [23, 45], [6, 2, 28], [1]], ![[50, 54, 35, 13], [53, 15, 29, 2], [44, 20], [26, 29, 36, 23], [25, 25, 6, 33]], ![[34, 58, 26, 4], [21, 44, 41, 27], [50, 7], [23, 11, 6, 19], [26, 24, 44, 26]]]
 h' := ![![[54, 22, 11], [57, 11, 30], [26, 47, 47], [37, 2, 35], [16, 31, 21], [0, 1]], ![[26, 36, 48], [54, 50, 21], [18, 37, 26], [9, 56, 43], [39, 52, 35], [54, 22, 11]], ![[0, 1], [41, 57, 8], [0, 34, 45], [12, 1, 40], [56, 35, 3], [26, 36, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 56], []]
 b := ![[], [4, 22, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [43, 28, 38, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-857565, 311697, -127145]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14535, 5283, -2155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-26, 13, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-26, 13, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![35, 13, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-26, 13, 1], ![-322, 39, 64], ![-3686, 440, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -13, 61]], ![![-1, 0, 1], ![-42, -13, 64], ![-61, 7, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [1, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 60], [0, 1]]
 g := ![![[38, 1], [22], [17, 25], [7, 14], [23, 1]], ![[0, 60], [22], [43, 36], [24, 47], [46, 60]]]
 h' := ![![[23, 60], [23, 60], [44, 49], [54, 5], [38, 40], [0, 1]], ![[0, 1], [0, 1], [12, 12], [47, 56], [43, 21], [23, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [27, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [1, 38, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-99722, 11858, 5093]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4557, -891, 5093]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-3, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-3, 1, 0]] 
 ![![61, 0, 0], ![58, 1, 0], ![60, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-3, 1, 0], ![-2, -1, 5], ![-296, 39, -4]]]
  hmulB := by decide  
  f := ![![![-1436, -721, 3600], ![61, -43920, 0]], ![![-1364, -685, 3420], ![62, -41724, 0]], ![![-1410, -710, 3541], ![110, -43200, 0]]]
  g := ![![![1, 0, 0], ![-58, 61, 0], ![-60, 0, 61]], ![![-1, 1, 0], ![-4, -1, 5], ![-38, 39, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-26, 13, 1]] ![![61, 0, 0], ![-3, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-183, 61, 0]], ![![-1586, 793, 61], ![-244, 0, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-3, 1, 0]]], ![![![-26, 13, 1]], ![![-4, 0, 1]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2960862318759303, 888230806029369, 191039919173626]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![2960862318759303, 888230806029369, 191039919173626]] 
 ![![67, 0, 0], ![1, 1, 0], ![66, 0, 1]] where
  M :=![![![2960862318759303, 888230806029369, 191039919173626], ![-58324277687452034, 12187880778589455, 4250114110973219], ![-231967851678565812, 21841326850512449, 9714228279674974]]]
  hmulB := by decide  
  f := ![![![-25567724678939509631161318695839, 4455911498642347163196112841332, -1446710523667017952592168754981]], ![![5876817422824076268801916523819, -1024204486657106989442799427106, 332530708853906504716127823980]], ![![-48369951302122377675860116018904, 8429855409599054551630853058561, -2736939577407250145807870441271]]]
  g := ![![![-157253778398946, 888230806029369, 191039919173626], ![-5239099847616029, 12187880778589455, 4250114110973219], ![-13357436492352635, 21841326850512449, 9714228279674974]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26928328675786416347960880252536353031648876069034821, -4693035883810763159664688648255588501430532591151708, 1523698215982213469852339460978936194100430847500770]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![26928328675786416347960880252536353031648876069034821, -4693035883810763159664688648255588501430532591151708, 1523698215982213469852339460978936194100430847500770]] 
 ![![67, 0, 0], ![22, 1, 0], ![28, 0, 1]] where
  M :=![![![26928328675786416347960880252536353031648876069034821, -4693035883810763159664688648255588501430532591151708, 1523698215982213469852339460978936194100430847500770], ![-441628600163113660756963103153253936450866465677924504, 76966487331471215352872741934203687598704613939261435, -24988877635036029268175782702256878701253093803259310], ![1635977732597104477376826832562241859867707444276030308, -285116179939428065707029601167556676560519637837468202, 92569293198885718301719147339949389297096642560217329]]]
  hmulB := by decide  
  f := ![![![-2182183039492792906737053505, -153567595780275301155967608, -5536322442659972320403470]], ![![-687494630361993157299459922, -90801819604225956044418081, -13195533585033372007586730]], ![![-246895537172352653169797736, -148031273337615328835564138, -35896796564379040647291371]]]
  g := ![![![1306142807046585503055500382190284875049381034990311, -4693035883810763159664688648255588501430532591151708, 1523698215982213469852339460978936194100430847500770], ![-21420936532454799686734947911082723283392258893289782, 76966487331471215352872741934203687598704613939261435, -24988877635036029268175782702256878701253093803259310], ![79352141517846594186318536309401579759409455000212620, -285116179939428065707029601167556676560519637837468202, 92569293198885718301719147339949389297096642560217329]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311119275463, -604273686, -5284171341]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![311119275463, -604273686, -5284171341]] 
 ![![67, 0, 0], ![43, 1, 0], ![28, 0, 1]] where
  M :=![![![311119275463, -604273686, -5284171341], ![1565323264308, 103828045792, 2262802911], ![-677170746186, 330472806093, 100356695509]]]
  hmulB := by decide  
  f := ![![![9672044749208673811405, -1685632020626477704539, 547277831710400547126]], ![![3839924627924587572391, -669217324511600023208, 217276251174693051591]], ![![12812288654035300834288, -2232909852336878251665, 724963721285707294336]]]
  g := ![![![7239699127, -604273686, -5284171341], ![-44218525168, 103828045792, 2262802911], ![-264141625111, 330472806093, 100356695509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![2960862318759303, 888230806029369, 191039919173626]] ![![26928328675786416347960880252536353031648876069034821, -4693035883810763159664688648255588501430532591151708, 1523698215982213469852339460978936194100430847500770]]
  ![![-9672044749208673811405, 1685632020626477704539, -547277831710400547126]] where
 M := ![![![-9672044749208673811405, 1685632020626477704539, -547277831710400547126]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-9672044749208673811405, 1685632020626477704539, -547277831710400547126]] ![![311119275463, -604273686, -5284171341]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [11, 27, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 43, 57], [66, 27, 14], [0, 1]]
 g := ![![[24, 47, 3], [58, 50, 20], [3, 29, 12], [22, 12], [15, 1], []], ![[61, 62, 2, 20], [33, 56, 15, 43], [9, 8, 53, 36], [11, 32], [20, 19], [32, 54]], ![[12, 59, 24, 52], [26, 59, 56, 31], [24, 15, 34, 34], [3, 64], [20, 3], [4, 54]]]
 h' := ![![[20, 43, 57], [1, 38, 43], [38, 35, 37], [3, 21, 15], [48, 10, 56], [0, 0, 1], [0, 1]], ![[66, 27, 14], [56, 49, 61], [29, 52, 12], [7, 5, 40], [25, 50, 23], [48, 49, 27], [20, 43, 57]], ![[0, 1], [59, 55, 38], [12, 55, 22], [39, 45, 16], [70, 11, 63], [52, 22, 43], [66, 27, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 24], []]
 b := ![[], [59, 46, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [11, 27, 56, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10861367, 2172671, -706592]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-152977, 30601, -9952]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-7, -24, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-7, -24, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![66, 49, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-7, -24, 1], ![-248, -16, -121], ![7266, -1003, 57]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -49, 73]], ![![-1, -1, 1], ![106, 81, -121], ![48, -52, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [67, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 72], [0, 1]]
 g := ![![[64, 12], [4], [2], [25, 36], [69], [1]], ![[0, 61], [4], [2], [52, 37], [69], [1]]]
 h' := ![![[19, 72], [5, 42], [28, 2], [4, 32], [12, 6], [6, 19], [0, 1]], ![[0, 1], [0, 31], [66, 71], [28, 41], [53, 67], [2, 54], [19, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [63, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [67, 54, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13583, -2520, 4485]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4241, -3045, 4485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-25, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-25, 1, 0]] 
 ![![73, 0, 0], ![48, 1, 0], ![16, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-25, 1, 0], ![-2, -23, 5], ![-296, 39, -26]]]
  hmulB := by decide  
  f := ![![![-904, -11273, 2450], ![219, -35770, 0]], ![![-593, -7408, 1610], ![147, -23506, 0]], ![![-193, -2471, 537], ![63, -7840, 0]]]
  g := ![![![1, 0, 0], ![-48, 73, 0], ![-16, 0, 73]], ![![-1, 1, 0], ![14, -23, 5], ![-24, 39, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-7, -24, 1]] ![![73, 0, 0], ![-25, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1825, 73, 0]], ![![-511, -1752, 73], ![-73, 584, -146]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-25, 1, 0]]], ![![![-7, -24, 1]], ![![-1, 8, -2]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-2, -22, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-2, -22, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![77, 57, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-2, -22, 1], ![-252, -7, -111], ![6674, -925, 60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -57, 79]], ![![-1, -1, 1], ![105, 80, -111], ![26, -55, 60]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [17, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 78], [0, 1]]
 g := ![![[17, 55], [14, 64], [21, 25], [64, 26], [18], [1]], ![[1, 24], [4, 15], [64, 54], [55, 53], [18], [1]]]
 h' := ![![[27, 78], [78, 23], [38, 71], [18, 74], [62, 42], [62, 27], [0, 1]], ![[0, 1], [67, 56], [59, 8], [41, 5], [11, 37], [1, 52], [27, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [20, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [17, 52, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-52248, -3795, 8270]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8722, -6015, 8270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![32, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![32, 1, 0]] 
 ![![79, 0, 0], ![32, 1, 0], ![19, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![32, 1, 0], ![-2, 34, 5], ![-296, 39, 31]]]
  hmulB := by decide  
  f := ![![![137, -2857, -420], ![79, 6636, 0]], ![![36, -1157, -170], ![80, 2686, 0]], ![![37, -687, -101], ![9, 1596, 0]]]
  g := ![![![1, 0, 0], ![-32, 79, 0], ![-19, 0, 79]], ![![0, 1, 0], ![-15, 34, 5], ![-27, 39, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-2, -22, 1]] ![![79, 0, 0], ![32, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2528, 79, 0]], ![![-158, -1738, 79], ![-316, -711, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![32, 1, 0]]], ![![![-2, -22, 1]], ![![-4, -9, -1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB280I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB280I1 : PrimesBelowBoundCertificateInterval O 31 79 280 where
  m := 11
  g := ![2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB280I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I53N0, I53N1, I53N2, I61N1, I67N0, I67N1, I67N2, I73N1, I79N1]
  Il := ![[I37N1], [I41N1], [], [], [I53N0, I53N1, I53N2], [], [I61N1], [I67N0, I67N1, I67N2], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
